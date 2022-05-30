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

// nested-x86vmx-handler.c
// Intercept handlers for nested virtualization
// author: Eric Li (xiaoyili@andrew.cmu.edu)
#include <xmhf.h>
#include "nested-x86vmx-vmcs12.h"

/* Maximum number of active VMCS per CPU */
#define VMX_NESTED_MAX_ACTIVE_VMCS 10

/* VMCALL executed in VMX root operation */
#define VM_INST_ERRNO_VMCALL_IN_VMXROOT 1
/* VMCLEAR with invalid physical address */
#define VM_INST_ERRNO_VMCLEAR_INVALID_PHY_ADDR 2
/* VMCLEAR with VMXON pointer */
#define VM_INST_ERRNO_VMCLEAR_VMXON_PTR 3
/* VMLAUNCH with non-clear VMCS */
#define VM_INST_ERRNO_VMLAUNCH_NONCLEAR_VMCS 4
/* VMRESUME with non-launched VMCS */
#define VM_INST_ERRNO_VMRESUME_NONLAUNCH_VMCS 5
/* VMRESUME after VMXOFF (VMXOFF and VMXON between VMLAUNCH and VMRESUME) */
#define VM_INST_ERRNO_VMLAUNCH_AFTER_VMXOFF 6
/* VM entry with invalid control field(s) */
#define VM_INST_ERRNO_VMENTRY_INVALID_CTRL 7
/* VM entry with invalid host-state field(s) */
#define VM_INST_ERRNO_VMENTRY_INVALID_HOST 8
/* VMPTRLD with invalid physical address */
#define VM_INST_ERRNO_VMPTRLD_INVALID_PHY_ADDR 9
/* VMPTRLD with VMXON pointer */
#define VM_INST_ERRNO_VMPTRLD_VMXON_PTR 10
/* VMPTRLD with incorrect VMCS revision identifier */
#define VM_INST_ERRNO_VMPTRLD_WITH_INCORRECT_VMCS_REV_ID 11
/* VMREAD/VMWRITE from/to unsupported VMCS component */
#define VM_INST_ERRNO_VMRDWR_UNSUPP_VMCS_COMP 12
/* VMWRITE to read-only VMCS component */
#define VM_INST_ERRNO_VMWRITE_RO_VMCS_COMP 13
/* VMXON executed in VMX root operation */
#define VM_INST_ERRNO_VMXON_IN_VMXROOT 15
/* VM entry with invalid executive-VMCS pointer */
#define VM_INST_ERRNO_VMENTRY_INVALID_EXEC_VMCS_PTR 16
/* VM entry with non-launched executive VMCS */
#define VM_INST_ERRNO_VMENTRY_NONLAUNCH_EXEC_VMCS 17
/* VM entry with executive-VMCS pointer not VMXON pointer */
#define VM_INST_ERRNO_VMENTRY_EXEC_VMCS_PTR_NOT_VMXON_PTR 18
/* VMCALL with non-clear VMCS */
#define VM_INST_ERRNO_VMCALL_NONCLEAR_VMCS 19
/* VMCALL with invalid VM-exit control fields */
#define VM_INST_ERRNO_VMCALL_INVALID_VMEXIT_CTRL 20
/* VMCALL with incorrect MSEG revision identifier */
#define VM_INST_ERRNO_VMCALL_INCORRECT_MSEG_REV_ID 22
/* VMXOFF under dual-monitor treatment of SMIs and SMM */
#define VM_INST_ERRNO_VMXOFF_UNDER_DUAL_MONITOR_SMI_SMM 23
/* VMCALL with invalid SMM-monitor features */
#define VM_INST_ERRNO_VMCALL_INVALID_SMM_MONITOR_FEATURE 24
/* VM entry with invalid VM-execution control fields in executive VMCS */
#define VM_INST_ERRNO_VMENTRY_INVALID_VMEXEC_CTRL_FIELD_EXEC_VMCS 25
/* VM entry with events blocked by MOV SS */
#define VM_INST_ERRNO_VMENTRY_EVENT_BLOCK_MOVSS 26
/* Invalid operand to INVEPT/INVVPID */
#define VM_INST_ERRNO_INVALID_OPERAND_INVEPT_INVVPID 28

#define CUR_VMCS_PTR_INVALID 0xffffffffffffffffULL

#define VMX_INST_RFLAGS_MASK \
	((u64) (EFLAGS_CF | EFLAGS_PF | EFLAGS_AF | EFLAGS_ZF | EFLAGS_SF | \
			EFLAGS_OF))

union _vmx_decode_m64_inst_info {
	struct {
		u32 scaling: 2;
		u32 undefined6_2: 5;
		u32 address_size: 3;
		u32 zero_10: 1;
		u32 undefined14_11: 4;
		u32 segment_register: 3;
		u32 index_reg: 4;
		u32 index_reg_invalid: 1;
		u32 base_reg: 4;
		u32 base_reg_invalid: 1;
		u32 undefined_31_28: 4;
	};
	u32 raw;
};

/* Format of an active VMCS12 tracked by a CPU */
typedef struct vmcs12_info {
	/*
	 * Pointer to VMCS12 in guest.
	 *
	 * When a VMCS is invalid, this field is CUR_VMCS_PTR_INVALID, and all
	 * other fields are undefined.
	 */
	gpa_t vmcs12_ptr;
	/* Pointer to VMCS02 in host */
	spa_t vmcs02_ptr;
} vmcs12_info_t;

/* A blank page in memory for VMCLEAR */
static u8 blank_page[PAGE_SIZE_4K] __attribute__((section(".bss.palign_data")));

/* Track all active VMCS12's in each CPU */
static vmcs12_info_t
cpu_active_vmcs12[MAX_VCPU_ENTRIES][VMX_NESTED_MAX_ACTIVE_VMCS];

/* The VMCS02's in each CPU */
// TODO: static u8 cpu_vmcs02[MAX_VCPU_ENTRIES][VMX_NESTED_MAX_ACTIVE_VMCS][PAGE_SIZE_4K]
// TODO: __attribute__((section(".bss.palign_data")));

/*
 * Given a segment index, return the segment offset
 * TODO: do we need to check access rights?
 */
static u64 _vmx_decode_seg(u32 seg, VCPU *vcpu)
{
	switch (seg) {
		case 0: return vcpu->vmcs.guest_ES_base;
		case 1: return vcpu->vmcs.guest_CS_base;
		case 2: return vcpu->vmcs.guest_SS_base;
		case 3: return vcpu->vmcs.guest_DS_base;
		case 4: return vcpu->vmcs.guest_FS_base;
		case 5: return vcpu->vmcs.guest_GS_base;
		default:
			HALT_ON_ERRORCOND(0 && "Unexpected segment");
			return 0;
	}
}

/*
 * Decode the operand for instructions that take one m64 operand. Following
 * Table 26-13. Format of the VM-Exit Instruction-Information Field as Used
 * for VMCLEAR, VMPTRLD, VMPTRST, VMXON, XRSTORS, and XSAVES in Intel's
 * System Programming Guide, Order Number 325384
 */
static u64 _vmx_decode_m64(VCPU *vcpu, struct regs *r)
{
	union _vmx_decode_m64_inst_info inst_info;
	u64 ans = 0;
	inst_info.raw = vcpu->vmcs.info_vmx_instruction_information;
	HALT_ON_ERRORCOND(inst_info.zero_10 == 0);
	ans = _vmx_decode_seg(inst_info.segment_register, vcpu);
	ans += vcpu->vmcs.info_exit_qualification;
	if (!inst_info.base_reg_invalid) {
		ans += *_vmx_decode_reg(inst_info.base_reg, vcpu, r);
	}
	if (!inst_info.index_reg_invalid) {
		ans += *_vmx_decode_reg(inst_info.index_reg, vcpu, r) << inst_info.scaling;
	}
	switch (inst_info.address_size) {
	case 0:	/* 16-bit */
		ans &= 0xffffULL;
		break;
	case 1:	/* 32-bit */
		ans &= 0xffffffffULL;
		break;
	case 2:	/* 64-bit */
		break;
	default:
		HALT_ON_ERRORCOND(0 && "Unexpected address size");
		break;
	}
	return ans;
}

/* The VMsucceed pseudo-function in SDM "29.2 CONVENTIONS" */
static void _vmx_nested_vm_succeed(VCPU *vcpu)
{
	vcpu->vmcs.guest_RFLAGS &= ~VMX_INST_RFLAGS_MASK;
}

static void _vmx_nested_vm_fail_valid(VCPU *vcpu, u32 error_number)
{
	vcpu->vmcs.guest_RFLAGS &= ~VMX_INST_RFLAGS_MASK;
	vcpu->vmcs.guest_RFLAGS |= EFLAGS_ZF;
	/* TODO: set error_number, using vcpu->vmx_nested_current_vmcs_pointer */
	HALT_ON_ERRORCOND(0);
	(void) error_number;
}

static void _vmx_nested_vm_fail_invalid(VCPU *vcpu)
{
	vcpu->vmcs.guest_RFLAGS &= ~VMX_INST_RFLAGS_MASK;
	vcpu->vmcs.guest_RFLAGS |= EFLAGS_CF;
}

static void _vmx_nested_vm_fail(VCPU *vcpu, u32 error_number)
{
	if (vcpu->vmx_nested_current_vmcs_pointer != CUR_VMCS_PTR_INVALID) {
		_vmx_nested_vm_fail_valid(vcpu, error_number);
	} else {
		_vmx_nested_vm_fail_invalid(vcpu);
	}
}

/*
 * Check whether addr sets any bit beyond the physical-address width for VMX
 *
 * If IA32_VMX_BASIC[48] = 1, the address is limited to 32-bits.
 */
static u32 _vmx_check_physical_addr_width(VCPU *vcpu, u64 addr) {
	u32 eax, ebx, ecx, edx;
	u64 paddrmask;
	/* Check whether CPUID 0x80000008 is supported */
	cpuid(0x80000000U, &eax, &ebx, &ecx, &edx);
	HALT_ON_ERRORCOND(eax >= 0x80000008U);
	/* Compute paddrmask from CPUID.80000008H:EAX[7:0] (max phy addr) */
	cpuid(0x80000008U, &eax, &ebx, &ecx, &edx);
	eax &= 0xFFU;
	HALT_ON_ERRORCOND(eax >= 32 && eax < 64);
	paddrmask = (1ULL << eax) - 0x1ULL;
	if (vcpu->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR] & (1ULL << 48)) {
		paddrmask &= (1ULL << 32);
	}
	// TODO: paddrmask can be cached, maybe move code to part-*.c
	return (addr & ~paddrmask) == 0;
}

/*
 * Calculate virtual guest CR0
 *
 * Note: vcpu->vmcs.guest_CR0 is the CR0 on physical CPU when VMX non-root mode.
 * For bits in CR0 that are masked, use the CR0 shadow.
 * For other bits, use guest_CR0
 */
static u64 _vmx_guest_get_guest_cr0(VCPU *vcpu) {
	return ((vcpu->vmcs.guest_CR0 & ~vcpu->vmcs.control_CR0_mask) |
			(vcpu->vmcs.control_CR0_shadow & vcpu->vmcs.control_CR0_mask));
}

/*
 * Calculate virtual guest CR4
 *
 * Note: vcpu->vmcs.guest_CR4 is the CR4 on physical CPU when VMX non-root mode.
 * For bits in CR4 that are masked, use the CR4 shadow.
 * For other bits, use guest_CR4
 */
static u64 _vmx_guest_get_guest_cr4(VCPU *vcpu) {
	return ((vcpu->vmcs.guest_CR4 & ~vcpu->vmcs.control_CR4_mask) |
			(vcpu->vmcs.control_CR4_shadow & vcpu->vmcs.control_CR4_mask));
}

/* Get CPL of guest */
static u32 _vmx_guest_get_cpl(VCPU *vcpu) {
	return (vcpu->vmcs.guest_CS_selector & 0x3);
}

/*
 * Check for conditions that should result in #UD
 *
 * Always check:
 *   (CR0.PE = 0) or (RFLAGS.VM = 1) or (IA32_EFER.LMA = 1 and CS.L = 0)
 * Check for VMXON:
 *   (CR4.VMXE = 0)
 * Check for other than VMXON:
 *   (not in VMX operation)
 * Not checked:
 *   (register operand)
 *
 * Return whether should inject #UD to guest
 */
static u32 _vmx_nested_check_ud(VCPU *vcpu, int is_vmxon)
{
	if ((_vmx_guest_get_guest_cr0(vcpu) & CR0_PE) == 0 ||
		(vcpu->vmcs.guest_RFLAGS & EFLAGS_VM) ||
		((_vmx_get_guest_efer(vcpu) & (1ULL << EFER_LMA)) && !VCPU_g64(vcpu))) {
		return 1;
	}
	if (is_vmxon) {
		if ((_vmx_guest_get_guest_cr4(vcpu) & CR4_VMXE) == 0) {
			return 1;
		}
	} else {
		if (!vcpu->vmx_nested_is_vmx_operation) {
			return 1;
		}
	}
	return 0;
}

/* Clear list of active VMCS12's tracked */
static void active_vmcs12_init(VCPU *vcpu)
{
	int i;
	for (i = 0; i < VMX_NESTED_MAX_ACTIVE_VMCS; i++) {
		cpu_active_vmcs12[vcpu->idx][i].vmcs12_ptr = CUR_VMCS_PTR_INVALID;
	}
}

/*
 * Look up vmcs_ptr in list of active VMCS12's tracked in the current CPU.
 * A return value of 0 means the VMCS is not active.
 * A VMCS is defined to be active if this function returns non-zero.
 * When vmcs_ptr = CUR_VMCS_PTR_INVALID, a empty slot is returned.
 */
static vmcs12_info_t *find_active_vmcs12(VCPU *vcpu, gpa_t vmcs_ptr)
{
	int i;
	for (i = 0; i < VMX_NESTED_MAX_ACTIVE_VMCS; i++) {
		if (cpu_active_vmcs12[vcpu->idx][i].vmcs12_ptr == vmcs_ptr) {
			return &cpu_active_vmcs12[vcpu->idx][i];
		}
	}
	return NULL;
}

/*
 * Virtualize fields in VCPU that tracks nested virtualization information
 */
void xmhf_nested_arch_x86vmx_vcpu_init(VCPU *vcpu)
{
	vcpu->vmx_nested_is_vmx_operation = 0;
	vcpu->vmx_nested_vmxon_pointer = 0;
	vcpu->vmx_nested_is_vmx_root_operation = 0;
	vcpu->vmx_nested_current_vmcs_pointer = CUR_VMCS_PTR_INVALID;
}

// TODO: also need to virtualize VMCALL

void xmhf_nested_arch_x86vmx_handle_vmclear(VCPU *vcpu, struct regs *r)
{
	if (_vmx_nested_check_ud(vcpu, 0)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		// TODO: VMEXIT
		HALT_ON_ERRORCOND(0 && "Not implemented");
	} else if (_vmx_guest_get_cpl(vcpu) > 0) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
	} else {
		u64 addr = _vmx_decode_m64(vcpu, r);
		gpa_t vmcs_ptr;
		guestmem_hptw_ctx_pair_t ctx_pair;
		guestmem_init(vcpu, &ctx_pair);
		guestmem_copy_gv2h(&ctx_pair, 0, &vmcs_ptr, addr, sizeof(vmcs_ptr));
		if (!PA_PAGE_ALIGNED_4K(vmcs_ptr) ||
			!_vmx_check_physical_addr_width(vcpu, vmcs_ptr)) {
			_vmx_nested_vm_fail(vcpu, VM_INST_ERRNO_VMCLEAR_INVALID_PHY_ADDR);
		} else if (vmcs_ptr == vcpu->vmx_nested_vmxon_pointer) {
			_vmx_nested_vm_fail(vcpu, VM_INST_ERRNO_VMCLEAR_VMXON_PTR);
		} else {
			/*
			 * We do not distinguish a VMCS that is "Inactive, Not Current,
			 * Clear" from a VMCS that is "Inactive" with other states. This is
			 * because we do not track inactive guests. As a result, we expect
			 * guest hypervisors to VMCLEAR before and after using a VMCS.
			 * However, we cannot check whether the GUEST does so.
			 *
			 * SDM says that the launch state of VMCS should be set to clear.
			 * Here, we remove the VMCS from the list of active VMCS's we track.
			 */
			vmcs12_info_t *vmcs12_info = find_active_vmcs12(vcpu, vmcs_ptr);
			if (vmcs12_info != NULL) {
				vmcs12_info->vmcs12_ptr = CUR_VMCS_PTR_INVALID;
			}
			guestmem_copy_h2gp(&ctx_pair, 0, vmcs_ptr, blank_page, PAGE_SIZE_4K);
			if (vmcs_ptr == vcpu->vmx_nested_current_vmcs_pointer) {
				vcpu->vmx_nested_current_vmcs_pointer = CUR_VMCS_PTR_INVALID;
			}
			_vmx_nested_vm_succeed(vcpu);
		}
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	}
}

void xmhf_nested_arch_x86vmx_handle_vmlaunch(VCPU *vcpu, struct regs *r)
{
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_nested_arch_x86vmx_handle_vmptrld(VCPU *vcpu, struct regs *r)
{
	if (_vmx_nested_check_ud(vcpu, 0)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		// TODO: VMEXIT
		HALT_ON_ERRORCOND(0 && "Not implemented");
	} else if (_vmx_guest_get_cpl(vcpu) > 0) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
	} else {
		u64 addr = _vmx_decode_m64(vcpu, r);
		gpa_t vmcs_ptr;
		guestmem_hptw_ctx_pair_t ctx_pair;
		guestmem_init(vcpu, &ctx_pair);
		guestmem_copy_gv2h(&ctx_pair, 0, &vmcs_ptr, addr, sizeof(vmcs_ptr));
		if (!PA_PAGE_ALIGNED_4K(vmcs_ptr) ||
			!_vmx_check_physical_addr_width(vcpu, vmcs_ptr)) {
			_vmx_nested_vm_fail(vcpu, VM_INST_ERRNO_VMPTRLD_INVALID_PHY_ADDR);
		} else if (vmcs_ptr == vcpu->vmx_nested_vmxon_pointer) {
			_vmx_nested_vm_fail(vcpu, VM_INST_ERRNO_VMPTRLD_VMXON_PTR);
		} else {
			u32 rev;
			u64 basic_msr = vcpu->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];
			guestmem_copy_gp2h(&ctx_pair, 0, &rev, vmcs_ptr, sizeof(rev));
			/* Note: Currently does not support 1-setting of "VMCS shadowing" */
			if ((rev & (1U << 31)) ||
				(rev != ((u32) basic_msr & 0x7fffffffU))) {
				_vmx_nested_vm_fail
					(vcpu, VM_INST_ERRNO_VMPTRLD_WITH_INCORRECT_VMCS_REV_ID);
			} else {
				// TODO: look up active table
				HALT_ON_ERRORCOND(0 && "Not implemented");
				vcpu->vmx_nested_current_vmcs_pointer = vmcs_ptr;
				_vmx_nested_vm_succeed(vcpu);
			}
		}
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	}
}

void xmhf_nested_arch_x86vmx_handle_vmptrst(VCPU *vcpu, struct regs *r)
{
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_nested_arch_x86vmx_handle_vmread(VCPU *vcpu, struct regs *r)
{
	struct nested_vmcs12 vmcs12;
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(xmhf_nested_arch_x86vmx_vmcs_readable(&vmcs12, &vmcs12.info_vminstr_error));
	HALT_ON_ERRORCOND(xmhf_nested_arch_x86vmx_vmcs_readable(&vmcs12, &vmcs12.control_vpid));
	HALT_ON_ERRORCOND(!xmhf_nested_arch_x86vmx_vmcs_writable(&vmcs12, &vmcs12.info_vminstr_error));
	HALT_ON_ERRORCOND(xmhf_nested_arch_x86vmx_vmcs_writable(&vmcs12, &vmcs12.control_vpid));
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_nested_arch_x86vmx_handle_vmresume(VCPU *vcpu, struct regs *r)
{
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_nested_arch_x86vmx_handle_vmwrite(VCPU *vcpu, struct regs *r)
{
	struct nested_vmcs12 vmcs12;
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(xmhf_nested_arch_x86vmx_vmcs_readable(&vmcs12, &vmcs12.info_vminstr_error));
	HALT_ON_ERRORCOND(xmhf_nested_arch_x86vmx_vmcs_readable(&vmcs12, &vmcs12.control_vpid));
	HALT_ON_ERRORCOND(!xmhf_nested_arch_x86vmx_vmcs_writable(&vmcs12, &vmcs12.info_vminstr_error));
	HALT_ON_ERRORCOND(xmhf_nested_arch_x86vmx_vmcs_writable(&vmcs12, &vmcs12.control_vpid));
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_nested_arch_x86vmx_handle_vmxoff(VCPU *vcpu, struct regs *r)
{
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_nested_arch_x86vmx_handle_vmxon(VCPU *vcpu, struct regs *r)
{
	if (_vmx_nested_check_ud(vcpu, 1)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_operation) {
		u64 vcr0 = _vmx_guest_get_guest_cr0(vcpu);
		u64 vcr4 = _vmx_guest_get_guest_cr4(vcpu);
		/*
		 * Note: A20M mode is not tested here.
		 *
		 * Note: IA32_FEATURE_CONTROL is not tested here, because running XMHF
		 * already requires entering VMX operation in physical CPU. This may
		 * need to be updated if IA32_FEATURE_CONTROL is virtualized.
		 */
		if (_vmx_guest_get_cpl(vcpu) > 0 ||
			(~vcr0 & vcpu->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR]) != 0 ||
			(vcr0 & ~vcpu->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED1_MSR]) != 0 ||
			(~vcr4 & vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]) != 0 ||
			(vcr4 & ~vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED1_MSR]) != 0) {
			_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
		} else {
			u64 addr = _vmx_decode_m64(vcpu, r);
			gpa_t vmxon_ptr;
			guestmem_hptw_ctx_pair_t ctx_pair;
			guestmem_init(vcpu, &ctx_pair);
			guestmem_copy_gv2h(&ctx_pair, 0, &vmxon_ptr, addr, sizeof(vmxon_ptr));
			if (!PA_PAGE_ALIGNED_4K(vmxon_ptr) ||
				!_vmx_check_physical_addr_width(vcpu, vmxon_ptr)) {
				_vmx_nested_vm_fail_invalid(vcpu);
			} else {
				u32 rev;
				u64 basic_msr = vcpu->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];
				guestmem_copy_gp2h(&ctx_pair, 0, &rev, vmxon_ptr, sizeof(rev));
				if ((rev & (1U << 31)) ||
					(rev != ((u32) basic_msr & 0x7fffffffU))) {
					_vmx_nested_vm_fail_invalid(vcpu);
				} else {
					vcpu->vmx_nested_is_vmx_operation = 1;
					vcpu->vmx_nested_vmxon_pointer = vmxon_ptr;
					vcpu->vmx_nested_is_vmx_root_operation = 1;
					vcpu->vmx_nested_current_vmcs_pointer = CUR_VMCS_PTR_INVALID;
					active_vmcs12_init(vcpu);
					_vmx_nested_vm_succeed(vcpu);
				}
			}
			vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
		}
	} else {
		/* This may happen if guest tries nested virtualization */
		printf("\nNot implemented, HALT!");
		HALT();
	}
}

