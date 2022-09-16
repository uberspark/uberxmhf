/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

// nested-x86vmx-handler2.c
// Intercept handlers for nested VMEXIT from L2
// author: Eric Li (xiaoyili@andrew.cmu.edu)
#include <xmhf.h>
#include "nested-x86vmx-vmcs12.h"
#include "nested-x86vmx-vminsterr.h"
#include "nested-x86vmx-ept12.h"

/*
 * Update VMCS02 to virtualize NMI correctly. This function should be called
 * after VMCS12 is translated to VMCS02, but before enabling NMIs with call to
 * xmhf_smpguest_arch_x86vmx_mhv_nmi_enable().
 */
static void _update_nested_nmi(VCPU * vcpu, vmcs12_info_t * vmcs12_info)
{
	bool nmi_pending = false;
	bool nmi_windowing = false;
	bool override_nmi_blocking = false;

	/* Compute whether NMI is pending */
	if (vcpu->vmx_guest_nmi_cfg.guest_nmi_block) {
		nmi_pending = false;
	} else if (vcpu->vmx_guest_nmi_cfg.guest_nmi_pending) {
		nmi_pending = true;
	}

	/* Compute whether we need to set NMI windowing in VMCS02 */
	if (vmcs12_info->guest_nmi_exiting) {
		if (nmi_pending && !vmcs12_info->guest_block_nmi) {
			nmi_windowing = true;
			override_nmi_blocking = true;
		}
		if (vmcs12_info->guest_nmi_window_exiting) {
			nmi_windowing = true;
		}
	} else {
		if (nmi_pending) {
			nmi_windowing = true;
		}
	}

	/* Update NMI window exiting in VMCS02 */
	{
		u32 procctl = __vmx_vmread32(0x4002);
		if (nmi_windowing) {
			procctl |= (1U << VMX_PROCBASED_NMI_WINDOW_EXITING);
		} else {
			procctl &= ~(1U << VMX_PROCBASED_NMI_WINDOW_EXITING);
		}
		__vmx_vmwrite32(0x4002, procctl);
	}

	/*
	 * Warn if L1 is injecting NMI to L2 and L0 (XMHF) wants to clear L2's NMI
	 * blocking bit. The problem is that after injecting NMI, the NMI blocking
	 * bit will be set. As a result, the NMI VMEXIT to L1 will be delayed until
	 * L2 IRETs from its virtual NMI handler. This is a limitation of XMHF. The
	 * perfect solution may be using monitor traps or emulating the injection.
	 */
	if (override_nmi_blocking) {
		struct nested_vmcs12 *vmcs12 = &vmcs12_info->vmcs12_value;
		u32 injection = vmcs12->control_VM_entry_interruption_information;
#ifdef VMX_NESTED_USE_SHADOW_VMCS
		/* If using shadow VMCS, injection is actually in VMCS12 shadow */
		if (_vmx_hasctl_vmcs_shadowing(&vcpu->vmx_caps)) {
			u64 cur_vmcs;
			HALT_ON_ERRORCOND(__vmx_vmptrst(&cur_vmcs));
			HALT_ON_ERRORCOND(cur_vmcs == vmcs12_info->vmcs02_ptr);
			HALT_ON_ERRORCOND(__vmx_vmptrld(vmcs12_info->vmcs12_shadow_ptr));
			injection =
				__vmx_vmread32
				(VMCSENC_control_VM_entry_interruption_information);
			HALT_ON_ERRORCOND(__vmx_vmptrld(cur_vmcs));
		}
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
		if ((injection & INTR_INFO_VALID_MASK) &&
			(injection & INTR_INFO_INTR_TYPE_MASK) == INTR_TYPE_NMI) {
			HALT_ON_ERRORCOND((injection & INTR_INFO_VECTOR_MASK) ==
							  NMI_VECTOR);
			printf("CPU(0x%02x): Warning: NMI VMEXIT will be delayed\n",
				   vcpu->id);
		}
	}

	/* Update NMI blocking in VMCS02 */
	if (override_nmi_blocking) {
		/* Clear NMI blocking bit, possibly saving old NMI blocking bit */
		u32 guest_int = __vmx_vmread32(VMCSENC_guest_interruptibility);
		if (!vmcs12_info->guest_vmcs_block_nmi_overridden) {
			vmcs12_info->guest_vmcs_block_nmi_overridden = true;
			vmcs12_info->guest_vmcs_block_nmi = guest_int & (1U << 3);
		}
		guest_int &= ~(1U << 3);
		__vmx_vmwrite32(VMCSENC_guest_interruptibility, guest_int);
	} else {
		/* Restore old NMI blocking bit */
		if (vmcs12_info->guest_vmcs_block_nmi_overridden) {
			u32 guest_int = __vmx_vmread32(VMCSENC_guest_interruptibility);
			if (vmcs12_info->guest_vmcs_block_nmi) {
				guest_int |= (1U << 3);
			} else {
				guest_int &= ~(1U << 3);
			}
			__vmx_vmwrite32(VMCSENC_guest_interruptibility, guest_int);
			vmcs12_info->guest_vmcs_block_nmi_overridden = false;
		}
	}
}

/*
 * Perform VMENTRY. Never returns if succeed. If controls / host state check
 * fails, return error code for _vmx_nested_vm_fail().
 */
u32 xmhf_nested_arch_x86vmx_handle_vmentry(VCPU * vcpu,
										   vmcs12_info_t * vmcs12_info,
										   struct regs *r)
{
	u32 result;

	/*
	   Features notes
	   * "VMCS shadowing" not supported (logic not written)
	   * writing to VM-exit information field not supported
	   * "EPTP switching" not supported (the only VMFUNC in Intel SDM)
	   * "Sub-page write permissions for EPT" not supported
	   * "Activate tertiary controls" not supported
	 */

#ifdef VMX_NESTED_USE_SHADOW_VMCS
	/* Read VMCS12 values from the shadow VMCS */
	if (_vmx_hasctl_vmcs_shadowing(&vcpu->vmx_caps)) {
		HALT_ON_ERRORCOND(__vmx_vmptrld(vmcs12_info->vmcs12_shadow_ptr));
		xmhf_nested_arch_x86vmx_vmcs_read_all(vcpu, &vmcs12_info->vmcs12_value);
		/* No need to VMPTRLD because the next line does so */
	}
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */

	/*
	 * Begin blocking EPT02 flush (blocking is needed because VMCS translation
	 * calls xmhf_nested_arch_x86vmx_get_ept02()).
	 */
	xmhf_nested_arch_x86vmx_block_ept02_flush(vcpu);

	/* Translate VMCS12 to VMCS02 */
	HALT_ON_ERRORCOND(__vmx_vmptrld(vmcs12_info->vmcs02_ptr));
	result = xmhf_nested_arch_x86vmx_vmcs12_to_vmcs02(vcpu, vmcs12_info);

	/* When a problem happens, translate back to L1 guest */
	if (result != VM_INST_SUCCESS) {
		HALT_ON_ERRORCOND(__vmx_vmptrld(hva2spa((void *)vcpu->vmx_vmcs_vaddr)));
		return result;
	}

	if (0) {
		printf("CPU(0x%02x): nested vmentry\n", vcpu->id);
	}

	/* From now on, cannot fail */
	vcpu->vmx_nested_is_vmx_root_operation = 0;

	/*
	 * End blocking EPT02 flush (blocking is needed because VMCS translation
	 * calls xmhf_nested_arch_x86vmx_get_ept02()).
	 */
	xmhf_nested_arch_x86vmx_unblock_ept02_flush(vcpu);

	/* Process NMI */
	_update_nested_nmi(vcpu, vmcs12_info);

	/* Change NMI handler from L1 to L2 */
	HALT_ON_ERRORCOND(vcpu->vmx_mhv_nmi_handler_arg == SMPG_VMX_NMI_INJECT);
	vcpu->vmx_mhv_nmi_handler_arg = SMPG_VMX_NMI_NESTED;
	xmhf_smpguest_arch_x86vmx_mhv_nmi_enable(vcpu);

	if (vmcs12_info->launched) {
		__vmx_vmentry_vmresume(r);
	} else {
		vmcs12_info->launched = 1;
		__vmx_vmentry_vmlaunch(r);
	}

	HALT_ON_ERRORCOND(0 && "VM entry should never return");
	return 0;
}

/* Handle NMI interrupt when XMHF is interacting with nested guest */
void xmhf_nested_arch_x86vmx_handle_nmi(VCPU * vcpu)
{
	vmcs12_info_t *vmcs12_info;
	u32 nmi_pending_limit;

	vmcs12_info = xmhf_nested_arch_x86vmx_find_current_vmcs12(vcpu);
	HALT_ON_ERRORCOND(xmhf_smpguest_arch_x86vmx_mhv_nmi_disabled(vcpu));

	/* Calculate the maximum value of guest_nmi_pending */
	nmi_pending_limit = 2;

	/* When the guest OS is blocking NMI, max of guest_nmi_pending is 1 */
	if (vmcs12_info->guest_nmi_exiting) {
		if (vmcs12_info->guest_block_nmi) {
			nmi_pending_limit = 1;
		}
	} else {
		if (vmcs12_info->guest_vmcs_block_nmi_overridden) {
			if (vmcs12_info->guest_vmcs_block_nmi) {
				nmi_pending_limit = 1;
			}
		} else {
			u32 guest_int = __vmx_vmread32(VMCSENC_guest_interruptibility);
			if (guest_int & (1U << 3)) {
				nmi_pending_limit = 1;
			}
		}
	}

	/*
	 * When XMHF is injecting NMI to guest OS, the guest OS will soon be
	 * blocking NMI. So this case is the same as previous one. Max of
	 * guest_nmi_pending is 1.
	 */
	if (!vmcs12_info->guest_nmi_exiting) {
		u32 __ctl_VM_entry_intr_info =
			__vmx_vmread32(VMCSENC_control_VM_entry_interruption_information);
		if ((__ctl_VM_entry_intr_info & INTR_INFO_VALID_MASK)
			&& (__ctl_VM_entry_intr_info & INTR_INFO_VECTOR_MASK) == NMI_VECTOR) {
			nmi_pending_limit = 1;
		}
	}

	HALT_ON_ERRORCOND(vcpu->vmx_guest_nmi_cfg.guest_nmi_pending <=
					  nmi_pending_limit);

	/* Increment guest_nmi_pending, but not exceeding limit */
	if (vcpu->vmx_guest_nmi_cfg.guest_nmi_pending < nmi_pending_limit) {
		vcpu->vmx_guest_nmi_cfg.guest_nmi_pending++;
	}

	/* Set NMI windowing bit as required */
	_update_nested_nmi(vcpu, vmcs12_info);
}

/* Handle VMEXIT from nested guest */
void xmhf_nested_arch_x86vmx_handle_vmexit(VCPU * vcpu, struct regs *r)
{
	bool nmi_vmexit = false;
	bool ept_misconfig = false;
	vmcs12_info_t *vmcs12_info;
	u32 vmexit_reason = __vmx_vmread32(VMCSENC_info_vmexit_reason);

	xmhf_smpguest_arch_x86vmx_mhv_nmi_disable(vcpu);

	/*
	 * Check whether this VMEXIT is for quiescing. If so, printing before the
	 * quiesce is completed will result in deadlock.
	 */
	if (vmexit_reason == VMX_VMEXIT_EXCEPTION) {
		u32 intr_info =
			__vmx_vmread32(VMCSENC_info_vmexit_interrupt_information);
		HALT_ON_ERRORCOND(intr_info & INTR_INFO_VALID_MASK);
		if ((intr_info & INTR_INFO_INTR_TYPE_MASK) == INTR_TYPE_NMI) {
			HALT_ON_ERRORCOND((intr_info & INTR_INFO_VECTOR_MASK) ==
							  NMI_VECTOR);
			/* NMI received by L2 guest */
			if (xmhf_smpguest_arch_x86vmx_nmi_check_quiesce(vcpu)) {
				/* NMI is consumed by L0 (XMHF), nothing to do with L1 / L2 */
				xmhf_smpguest_arch_x86vmx_unblock_nmi();
			} else {
				/* Send NMI to L1 / L2 in the future */
				xmhf_smpguest_arch_x86vmx_unblock_nmi();
				xmhf_nested_arch_x86vmx_handle_nmi(vcpu);
			}
			/*
			 * Make sure that there is no interruption. (Currently not
			 * implemented if there is one. If there is one, re-injecting the
			 * event is likely the correct thing to do.)
			 */
			{
				u32 idt_info;
				u16 encoding = VMCSENC_info_IDT_vectoring_information;
				idt_info = __vmx_vmread32(encoding);
				HALT_ON_ERRORCOND((idt_info & INTR_INFO_VALID_MASK) == 0);
			}
			/* Resume to L2 (L2 -> L0 -> L2) */
			xmhf_smpguest_arch_x86vmx_mhv_nmi_enable(vcpu);
			/* Logging */
#ifdef __DEBUG_EVENT_LOGGER__
			xmhf_dbg_log_event(vcpu, 0, XMHF_DBG_EVENTLOG_vmexit_202,
							   &vmexit_reason);
#endif							/* __DEBUG_EVENT_LOGGER__ */
			if (0) {
				printf("CPU(0x%02x): 202 vmexit due to NMI\n", vcpu->id);
			}
			__vmx_vmentry_vmresume(r);
			HALT_ON_ERRORCOND(0 && "VMRESUME should not return");
		}
	}

	vmcs12_info = xmhf_nested_arch_x86vmx_find_current_vmcs12(vcpu);

	if (vmexit_reason == VMX_VMEXIT_NMI_WINDOW) {
		if (vmcs12_info->guest_nmi_exiting) {
			/*
			 * When "NMI exiting" = 1 in VMCS12, NMI windowing is shared by
			 * 1. L2 VMEXITing to L1 (due to L1 setting NMI window exiting) and
			 * 2. L0 injecting NMI to L2 (due to an NMI received by L0).
			 * Through experiment the former has higher priority. So first
			 * check whether L1 requests NMI window exiting. If so, forward the
			 * L2 -> L0 VMEXIT to L1. Otherwise, change the VMEXIT reason
			 * from NMI windowing (VMCS02) to NMI (VMCS12) by setting
			 * nmi_vmexit to true.
			 */
			if (vmcs12_info->guest_nmi_window_exiting) {
				/*
				 * Nothing to be done here. The following code will forward
				 * this VMEXIT to L1.
				 */
			} else {
				/* Compute whether NMI is pending */
				bool nmi_pending = false;
				if (vcpu->vmx_guest_nmi_cfg.guest_nmi_block) {
					nmi_pending = false;
				} else if (vcpu->vmx_guest_nmi_cfg.guest_nmi_pending) {
					nmi_pending = true;
				}
				/*
				 * We must need to deliver NMI VMEXIT to L1, otherwise NMI
				 * windowing bit in VMCS02 is wrong.
				 */
				HALT_ON_ERRORCOND(nmi_pending && !vmcs12_info->guest_block_nmi);
				/* Let the following code change the VMEXIT reason to NMI */
				nmi_vmexit = true;
			}
		} else {
			/*
			 * When "NMI exiting" = 0 in VMCS12, NMI windowing is used by L0
			 * XMHF to inject NMI to L2 nested guest. This is similar to
			 * injecting to L1 guest when there is no nested virtualization.
			 */
			/* Inject NMI to L2 */
			u16 encoding;
			u32 idt_info;
			encoding = VMCSENC_info_IDT_vectoring_information;
			idt_info = __vmx_vmread32(encoding);
			HALT_ON_ERRORCOND(!(idt_info & INTR_INFO_VALID_MASK));
			idt_info = NMI_VECTOR | INTR_TYPE_NMI | INTR_INFO_VALID_MASK;
			encoding = VMCSENC_control_VM_entry_interruption_information;
			__vmx_vmwrite32(encoding, idt_info);
			encoding = VMCSENC_control_VM_entry_exception_errorcode;
			__vmx_vmwrite32(encoding, 0U);
			/* Update NMI windowing */
			HALT_ON_ERRORCOND(vcpu->vmx_guest_nmi_cfg.guest_nmi_pending > 0);
			vcpu->vmx_guest_nmi_cfg.guest_nmi_pending--;
			_update_nested_nmi(vcpu, vmcs12_info);
			/* VMRESUME */
			xmhf_smpguest_arch_x86vmx_mhv_nmi_enable(vcpu);
			/* Logging */
#ifdef __DEBUG_EVENT_LOGGER__
			xmhf_dbg_log_event(vcpu, 1, XMHF_DBG_EVENTLOG_vmexit_202,
							   &vmexit_reason);
#endif							/* __DEBUG_EVENT_LOGGER__ */
			if (0) {
				printf("CPU(0x%02x): 202 vmexit due to NMI window\n", vcpu->id);
			}
			__vmx_vmentry_vmresume(r);
			HALT_ON_ERRORCOND(0 && "VMRESUME should not return");
		}
	}

	/*
	 * Check whether this VMEXIT is caused by EPT violation.
	 * If guest does not enable EPT, then the guest is doing illegal things.
	 * If guest enables EPT, need to manually walk EPT12 and see.
	 */
	if (vmexit_reason == VMX_VMEXIT_EPT_VIOLATION) {
		int status = 3;

		/*
		 * Begin blocking EPT02 flush (blocking is needed because
		 * vmcs12_info->guest_ept_cache_line is accessed).
		 */
		xmhf_nested_arch_x86vmx_block_ept02_flush(vcpu);

		if (vmcs12_info->guest_ept_enable) {
			ept02_cache_line_t *cache_line = vmcs12_info->guest_ept_cache_line;
			u64 guest2_paddr = __vmx_vmread64(VMCSENC_guest_paddr);
			ulong_t qualification =
				__vmx_vmreadNW(VMCSENC_info_exit_qualification);
			HALT_ON_ERRORCOND(cache_line->key == vmcs12_info->guest_ept_root);
#ifdef __DEBUG_QEMU__
			/*
			 * Workaround a KVM bug:
			 * https://bugzilla.kernel.org/show_bug.cgi?id=216234
			 *
			 * When enabled, the following code detects EPT violations on
			 * REP INS instructions. However, the following code may be
			 * disabled to increase efficiency. When such a situation is
			 * detected EPT02 entries should be hard-coded for these addresses
			 * beforehand.
			 */
			if (0) {
				ulong_t cs_base = __vmx_vmreadNW(VMCSENC_guest_CS_base);
				ulong_t rip = __vmx_vmreadNW(VMCSENC_guest_RIP);
				ulong_t cs_rip = cs_base + rip;
				u32 inst_len =
					__vmx_vmread32(VMCSENC_info_vmexit_instruction_length);
				u8 insts[16];
				int result;
				HALT_ON_ERRORCOND(inst_len <= 16);
				if (cs_rip != guest2_paddr) {
					hptw_ctx_t *ctx = &cache_line->value.ept02_ctx.ctx;
					result = hptw_checked_copy_from_va(ctx, 0, insts, cs_rip,
													   inst_len);
					if (result == 0) {
						u32 i;
						if ((inst_len >= 2 && insts[0] == 0xf3 &&
							 (insts[1] == 0x6c || insts[1] == 0x6d)) ||
							(inst_len >= 3 && insts[0] == 0x67 &&
							 insts[1] == 0xf3 &&
							 (insts[2] == 0x6c || insts[2] == 0x6d))) {
							printf("Warning: possible EPT on REP INS\n");
							printf("guest2_paddr = 0x%016llx\n", guest2_paddr);
							printf("CS:RIP=0x%08lx: ", cs_rip);
							for (i = 0; i < inst_len; i++) {
								printf("%02x ", insts[i]);
							}
							HALT_ON_ERRORCOND(0);
						}
					}
				}
			}
#endif							/* !__DEBUG_QEMU__ */
			status = xmhf_nested_arch_x86vmx_handle_ept02_exit(vcpu,
															   cache_line,
															   guest2_paddr,
															   qualification);
		}
		switch (status) {
		case 1:
			/*
			 * EPT handled by L0, continue running L2.
			 * First re-inject interruption to make sure interrupts etc. are
			 * not lost.
			 */
			{
				u16 encoding;
				u32 idt_info, idt_errcode, inst_len;
				/* Copy IDT-vectoring information */
				encoding = VMCSENC_info_IDT_vectoring_information;
				idt_info = __vmx_vmread32(encoding);
				encoding = VMCSENC_control_VM_entry_interruption_information;
				__vmx_vmwrite32(encoding, idt_info);
				/* Copy IDT-vectoring error code */
				encoding = VMCSENC_info_IDT_vectoring_error_code;
				idt_errcode = __vmx_vmread32(encoding);
				encoding = VMCSENC_control_VM_entry_exception_errorcode;
				__vmx_vmwrite32(encoding, idt_errcode);
				/* Copy VM-exit instruction length */
				encoding = VMCSENC_info_vmexit_instruction_length;
				inst_len = __vmx_vmread32(encoding);
				encoding = VMCSENC_control_VM_entry_instruction_length;
				__vmx_vmwrite32(encoding, inst_len);
				/*
				 * When this EPT VMEXIT is caused by NMI injection indirectly,
				 * the hardware will set virtual-NMI blocking. We need to
				 * remove this virtual-NMI blocking in order to retry NMI
				 * injection (otherwise VMENTRY failure will occur).
				 */
				if ((idt_info & INTR_INFO_VALID_MASK) &&
					(idt_info & INTR_INFO_INTR_TYPE_MASK) == INTR_TYPE_NMI &&
					vmcs12_info->guest_virtual_nmis) {
					u16 encoding = VMCSENC_guest_interruptibility;
					u32 guest_int = __vmx_vmread32(encoding);
					HALT_ON_ERRORCOND((idt_info & INTR_INFO_VECTOR_MASK) ==
									  NMI_VECTOR);
					HALT_ON_ERRORCOND(guest_int & (1U << 3));
					guest_int &= ~(1U << 3);
					__vmx_vmwrite32(encoding, guest_int);
				}
			}
			/* End blocking EPT02 flush */
			xmhf_nested_arch_x86vmx_unblock_ept02_flush(vcpu);
			/* Call VMRESUME */
			xmhf_smpguest_arch_x86vmx_mhv_nmi_enable(vcpu);
			/* Logging */
#ifdef __DEBUG_EVENT_LOGGER__
			xmhf_dbg_log_event(vcpu, 1, XMHF_DBG_EVENTLOG_vmexit_202,
							   &vmexit_reason);
#endif							/* __DEBUG_EVENT_LOGGER__ */
			if (0) {
				printf("CPU(0x%02x): 202 vmexit due to EPT\n", vcpu->id);
			}
			__vmx_vmentry_vmresume(r);
			HALT_ON_ERRORCOND(0 && "VMRESUME should not return");
			break;
		case 2:
			/*
			 * Forward EPT violation to L1.
			 *
			 * There is no address L0 physical -> L1 physical address
			 * translation needed, so just continue.
			 */
			break;
		case 3:
			/* Guest accesses illegal address, halt for safety */
			printf("CPU(0x%02x): qualification: 0x%08lx\n", vcpu->id,
				   __vmx_vmreadNW(VMCSENC_info_exit_qualification));
			printf("CPU(0x%02x): paddr: 0x%016llx\n", vcpu->id,
				   __vmx_vmread64(VMCSENC_guest_paddr));
			printf("CPU(0x%02x): linear addr:   0x%08lx\n", vcpu->id,
				   __vmx_vmreadNW(VMCSENC_info_guest_linear_address));
			HALT_ON_ERRORCOND(0 && "Guest accesses illegal memory");
			break;
		case 4:
			/*
			 * Guest EPT is misconfigured, change VMEXIT reason from EPT
			 * violation to EPT misconfiguration.
			 */
			ept_misconfig = true;
			break;
		default:
			HALT_ON_ERRORCOND(0 && "Unknown status");
			break;
		}

		/*
		 * End blocking EPT02 flush (blocking is needed because
		 * vmcs12_info->guest_ept_cache_line is accessed).
		 */
		xmhf_nested_arch_x86vmx_unblock_ept02_flush(vcpu);
	}

	// TODO: handle EPT misconfiguration
	if (vmexit_reason == VMX_VMEXIT_EPT_MISCONFIGURATION) {
		HALT_ON_ERRORCOND(0 && "EPT misconfiguration not implemented");
	}

	/*
	 * Begin blocking EPT02 flush (blocking is needed because VMCS translation
	 * calls xmhf_nested_arch_x86vmx_get_ept02()).
	 */
	xmhf_nested_arch_x86vmx_block_ept02_flush(vcpu);

	/* Wake the guest hypervisor up for the VMEXIT */
	xmhf_nested_arch_x86vmx_vmcs02_to_vmcs12(vcpu, vmcs12_info);
	if (vmcs12_info->vmcs12_value.info_vmexit_reason & 0x80000000U) {
		/*
		 * TODO: Stopping here makes debugging with a correct guest hypervisor
		 * easier. The correct behavior should be injecting the VMEXIT to
		 * guest hypervisor.
		 */
		HALT_ON_ERRORCOND(0 && "Debug: guest hypervisor VM-entry failure");
	}
	if (nmi_vmexit) {
		HALT_ON_ERRORCOND(vmcs12_info->vmcs12_value.info_vmexit_reason ==
						  VMX_VMEXIT_NMI_WINDOW);
		vmcs12_info->vmcs12_value.info_vmexit_reason = VMX_VMEXIT_EXCEPTION;

		/* NMI windowing should not be caused by an exception / interrupt */
		{
			u32 intr_info =
				vmcs12_info->vmcs12_value.info_vmexit_interrupt_information;
			HALT_ON_ERRORCOND(!(intr_info & INTR_INFO_VALID_MASK));
		}
		vmcs12_info->vmcs12_value.info_vmexit_interrupt_information =
			NMI_VECTOR | INTR_TYPE_NMI | INTR_INFO_VALID_MASK;

		/*
		 * Currently, we assume NMI windowing should not be caused by event
		 * delivery.
		 */
		{
			u32 idt_vec_info =
				vmcs12_info->vmcs12_value.info_IDT_vectoring_information;
			HALT_ON_ERRORCOND(!(idt_vec_info & INTR_INFO_VALID_MASK));
		}

		/* Update host state: NMI is blocked */
		vcpu->vmcs.guest_interruptibility |= (1U << 3);

		/* Consume one pending NMI */
		HALT_ON_ERRORCOND(vcpu->vmx_guest_nmi_cfg.guest_nmi_pending > 0);
		vcpu->vmx_guest_nmi_cfg.guest_nmi_pending--;
	}
	if (ept_misconfig) {
		/* Translate EPT violation to EPT misconfiguration */
		vmcs12_info->vmcs12_value.info_vmexit_reason =
			VMX_VMEXIT_EPT_MISCONFIGURATION;
		/*
		 * EPT violation will set VMEXIT qualification, but in EPT
		 * misconfiguration this field should be cleared to 0.
		 */
		vmcs12_info->vmcs12_value.info_exit_qualification = 0;
	}
	/* Logging */
#ifdef __DEBUG_EVENT_LOGGER__
	xmhf_dbg_log_event(vcpu, 1, XMHF_DBG_EVENTLOG_vmexit_201,
					   &vmcs12_info->vmcs12_value.info_vmexit_reason);
#endif							/* __DEBUG_EVENT_LOGGER__ */
	if (0) {
		printf("CPU(0x%02x): nested vmexit %d\n", vcpu->id,
			   vmcs12_info->vmcs12_value.info_vmexit_reason);
	}
	/* Follow SDM to load host state */
	vcpu->vmcs.guest_DR7 = 0x400UL;
	vcpu->vmcs.guest_IA32_DEBUGCTL = 0ULL;
	vcpu->vmcs.guest_RFLAGS = (1UL << 1);

#ifdef VMX_NESTED_USE_SHADOW_VMCS
	/* Write VMCS12 values to the shadow VMCS */
	if (_vmx_hasctl_vmcs_shadowing(&vcpu->vmx_caps)) {
		HALT_ON_ERRORCOND(__vmx_vmptrld(vmcs12_info->vmcs12_shadow_ptr));
		xmhf_nested_arch_x86vmx_vmcs_write_all(vcpu,
											   &vmcs12_info->vmcs12_value);
		/* No need to VMPTRLD because the next line does so */
	}
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */

	/* Prepare VMRESUME to guest hypervisor */
	HALT_ON_ERRORCOND(__vmx_vmptrld(hva2spa((void *)vcpu->vmx_vmcs_vaddr)));
	xmhf_baseplatform_arch_x86vmx_putVMCS(vcpu);
	vcpu->vmx_nested_is_vmx_root_operation = 1;

	/*
	 * End blocking EPT02 flush (blocking is needed because VMCS translation
	 * calls xmhf_nested_arch_x86vmx_get_ept02()).
	 */
	xmhf_nested_arch_x86vmx_unblock_ept02_flush(vcpu);

	/* NMI status be changed during L2, so update L1's NMI window exiting */
	{
		u32 procctl = __vmx_vmread32(0x4002);
		xmhf_smpguest_arch_x86vmx_update_nmi_window_exiting(vcpu, &procctl);
		__vmx_vmwrite32(0x4002, procctl);
	}

	/* Change NMI handler from L2 to L1 */
	HALT_ON_ERRORCOND(vcpu->vmx_mhv_nmi_handler_arg == SMPG_VMX_NMI_NESTED);
	vcpu->vmx_mhv_nmi_handler_arg = SMPG_VMX_NMI_INJECT;

	/*
	 * Update NMI windowing in VMCS01 since nested virtualization may change
	 * vcpu->vmx_guest_nmi_cfg.guest_nmi_pending.
	 */
	{
		u32 procctl = __vmx_vmread32(0x4002);
		xmhf_smpguest_arch_x86vmx_update_nmi_window_exiting(vcpu, &procctl);
		__vmx_vmwrite32(0x4002, procctl);
	}
	xmhf_smpguest_arch_x86vmx_mhv_nmi_enable(vcpu);

	__vmx_vmentry_vmresume(r);
}
