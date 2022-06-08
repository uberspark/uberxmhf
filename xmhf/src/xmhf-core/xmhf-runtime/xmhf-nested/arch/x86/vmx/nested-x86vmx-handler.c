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
#include "nested-x86vmx-vminsterr.h"

/* Maximum number of active VMCS per CPU */
#define VMX_NESTED_MAX_ACTIVE_VMCS 10

#define CUR_VMCS_PTR_INVALID 0xffffffffffffffffULL

#define VMX_INST_RFLAGS_MASK \
	((u64) (EFLAGS_CF | EFLAGS_PF | EFLAGS_AF | EFLAGS_ZF | EFLAGS_SF | \
			EFLAGS_OF))

/*
 * This structure follows Table 26-14. Format of the VM-Exit
 * Instruction-Information Field as Used for VMREAD and VMWRITE in Intel's
 * System Programming Guide, Order Number 325384. It covers all structures in
 * Table 26-13. Format of the VM-Exit Instruction-Information Field as Used
 * for VMCLEAR, VMPTRLD, VMPTRST, VMXON, XRSTORS, and XSAVES.
 */
union _vmx_decode_vm_inst_info {
	struct {
		u32 scaling: 2;
		u32 undefined2: 1;
		u32 reg1: 4;			/* Undefined in Table 26-13. */
		u32 address_size: 3;
		u32 mem_reg: 1;			/* Cleared to 0 in Table 26-13. */
		u32 undefined14_11: 4;
		u32 segment_register: 3;
		u32 index_reg: 4;
		u32 index_reg_invalid: 1;
		u32 base_reg: 4;
		u32 base_reg_invalid: 1;
		u32 reg2: 4;			/* Undefined in Table 26-13. */
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
	/* Whether this VMCS has launched */
	int launched;
	/* Content of VMCS12, stored in XMHF's format */
	struct nested_vmcs12 vmcs12_value;
} vmcs12_info_t;

/* A blank page in memory for VMCLEAR */
static u8 blank_page[PAGE_SIZE_4K] __attribute__((section(".bss.palign_data")));

/* Track all active VMCS12's in each CPU */
static vmcs12_info_t
cpu_active_vmcs12[MAX_VCPU_ENTRIES][VMX_NESTED_MAX_ACTIVE_VMCS];

/* The VMCS02's in each CPU */
static u8 cpu_vmcs02[MAX_VCPU_ENTRIES][VMX_NESTED_MAX_ACTIVE_VMCS][PAGE_SIZE_4K]
__attribute__((section(".bss.palign_data")));

/*
 * Given a segment index, return the segment offset
 * TODO: do we need to check access rights?
 */
static uintptr_t _vmx_decode_seg(u32 seg, VCPU *vcpu)
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
 * Access size bytes of memory referenced in memory operand of instruction.
 * The memory content in the guest is returned in dst.
 */
static gva_t _vmx_decode_mem_operand(VCPU *vcpu, struct regs *r)
{
	union _vmx_decode_vm_inst_info inst_info;
	gva_t addr;
	inst_info.raw = vcpu->vmcs.info_vmx_instruction_information;
	addr = _vmx_decode_seg(inst_info.segment_register, vcpu);
	addr += vcpu->vmcs.info_exit_qualification;
	if (!inst_info.base_reg_invalid) {
		addr += *_vmx_decode_reg(inst_info.base_reg, vcpu, r);
	}
	if (!inst_info.index_reg_invalid) {
		uintptr_t *index_reg = _vmx_decode_reg(inst_info.index_reg, vcpu, r);
		addr += *index_reg << inst_info.scaling;
	}
	switch (inst_info.address_size) {
	case 0:	/* 16-bit */
		addr &= 0xffffUL;
		break;
	case 1:	/* 32-bit */
		/* This case may happen if 32-bit guest hypervisor runs in AMD64 XMHF */
		addr &= 0xffffffffUL;
		break;
	case 2:	/* 64-bit */
#ifdef __I386__
		HALT_ON_ERRORCOND(0 && "Unexpected 64-bit address size in i386");
#elif !defined(__AMD64__)
    #error "Unsupported Arch"
#endif /* __I386__ */
		break;
	default:
		HALT_ON_ERRORCOND(0 && "Unexpected address size");
		break;
	}
	return addr;
}

/*
 * Decode the operand for instructions that take one m64 operand. Following
 * Table 26-13. Format of the VM-Exit Instruction-Information Field as Used
 * for VMCLEAR, VMPTRLD, VMPTRST, VMXON, XRSTORS, and XSAVES in Intel's
 * System Programming Guide, Order Number 325384
 */
static gva_t _vmx_decode_m64(VCPU *vcpu, struct regs *r)
{
	union _vmx_decode_vm_inst_info inst_info;
	inst_info.raw = vcpu->vmcs.info_vmx_instruction_information;
	HALT_ON_ERRORCOND(inst_info.mem_reg == 0);
	return _vmx_decode_mem_operand(vcpu, r);
}

/*
 * Decode the operand for instructions for VMREAD and VMWRITE. Following
 * Table 26-14. Format of the VM-Exit Instruction-Information Field as Used for
 * VMREAD and VMWRITE in Intel's System Programming Guide, Order Number 325384.
 * Return operand size in bytes (4 or 8, depending on guest mode).
 * When the value comes from a memory operand, put 0 in pvalue_mem_reg and
 * put the guest virtual address to ppvalue. When the value comes from a
 * register operand, put 1 in pvalue_mem_reg and put the host virtual address
 * to ppvalue.
 */
static size_t _vmx_decode_vmread_vmwrite(VCPU *vcpu, struct regs *r,
										int is_vmwrite, ulong_t *pencoding,
										uintptr_t *ppvalue, int *pvalue_mem_reg)
{
	union _vmx_decode_vm_inst_info inst_info;
	ulong_t *encoding;
	size_t size = (VCPU_g64(vcpu) ? sizeof(u64) : sizeof(u32));
	HALT_ON_ERRORCOND(size == (VCPU_glm(vcpu) ? sizeof(u64) : sizeof(u32)));
	inst_info.raw = vcpu->vmcs.info_vmx_instruction_information;
	if (is_vmwrite) {
		encoding = _vmx_decode_reg(inst_info.reg2, vcpu, r);
	} else {
		encoding = _vmx_decode_reg(inst_info.reg1, vcpu, r);
	}
	*pencoding = 0;
	memcpy(pencoding, encoding, size);
	if (inst_info.mem_reg) {
		*pvalue_mem_reg = 1;
		if (is_vmwrite) {
			*ppvalue = (hva_t) _vmx_decode_reg(inst_info.reg1, vcpu, r);
		} else {
			*ppvalue = (hva_t) _vmx_decode_reg(inst_info.reg2, vcpu, r);
		}
	} else {
		*pvalue_mem_reg = 0;
		*ppvalue = _vmx_decode_mem_operand(vcpu, r);
	}
	return size;
}

/* Clear list of active VMCS12's tracked */
static void active_vmcs12_array_init(VCPU *vcpu)
{
	int i;
	for (i = 0; i < VMX_NESTED_MAX_ACTIVE_VMCS; i++) {
		spa_t vmcs02_ptr = hva2spa(cpu_vmcs02[vcpu->idx][i]);
		cpu_active_vmcs12[vcpu->idx][i].vmcs12_ptr = CUR_VMCS_PTR_INVALID;
		cpu_active_vmcs12[vcpu->idx][i].vmcs02_ptr = vmcs02_ptr;
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

/* Add a new VMCS12 to the array of actives. Initializes underlying VMCS02 */
static void new_active_vmcs12(VCPU *vcpu, gpa_t vmcs_ptr, u32 rev)
{
	vmcs12_info_t *vmcs12_info;
	HALT_ON_ERRORCOND(vmcs_ptr != CUR_VMCS_PTR_INVALID);
	vmcs12_info = find_active_vmcs12(vcpu, CUR_VMCS_PTR_INVALID);
	if (vmcs12_info == NULL) {
		HALT_ON_ERRORCOND(0 && "Too many active VMCS's");
	}
	vmcs12_info->vmcs12_ptr = vmcs_ptr;
	HALT_ON_ERRORCOND(__vmx_vmclear(vmcs12_info->vmcs02_ptr));
	*(u32 *)spa2hva(vmcs12_info->vmcs02_ptr) = rev;
	vmcs12_info->launched = 0;
	memset(&vmcs12_info->vmcs12_value, 0, sizeof(vmcs12_info->vmcs12_value));
}

/*
 * Find VMCS12 pointed by current VMCS pointer.
 * It is illegal to call this function with a invalid current VMCS pointer.
 * This function will never return NULL.
 */
static vmcs12_info_t *find_current_vmcs12(VCPU *vcpu)
{
	vmcs12_info_t *ans;
	gpa_t vmcs_ptr = vcpu->vmx_nested_current_vmcs_pointer;
	HALT_ON_ERRORCOND(vmcs_ptr != CUR_VMCS_PTR_INVALID);
	ans = find_active_vmcs12(vcpu, vmcs_ptr);
	HALT_ON_ERRORCOND(ans != NULL);
	return ans;
}

/* The VMsucceed pseudo-function in SDM "29.2 CONVENTIONS" */
static void _vmx_nested_vm_succeed(VCPU *vcpu)
{
	vcpu->vmcs.guest_RFLAGS &= ~VMX_INST_RFLAGS_MASK;
}

static void _vmx_nested_vm_fail_valid(VCPU *vcpu, u32 error_number)
{
	vmcs12_info_t *vmcs12_info = find_current_vmcs12(vcpu);
	vcpu->vmcs.guest_RFLAGS &= ~VMX_INST_RFLAGS_MASK;
	vcpu->vmcs.guest_RFLAGS |= EFLAGS_ZF;
	vmcs12_info->vmcs12_value.info_vminstr_error = error_number;
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
 * Perform VMENTRY. Never returns if succeed. If controls / host state check
 * fails, return error code for _vmx_nested_vm_fail().
 */
static u32 _vmx_vmentry(VCPU *vcpu, vmcs12_info_t *vmcs12_info, struct regs *r)
{
	u32 result;

	/*
		Features notes
		* "enable VPID" not supported (currently ignore control_vpid in VMCS12)
		* "VMCS shadowing" not supported (logic not written)
		* writing to VM-exit information field not supported
		* VM exit/entry MSR load/store not supported (TODO)
		* "Enable EPT" not supported yet
		* "EPTP switching" not supported (the only VMFUNC in Intel SDM)
		* "Sub-page write permissions for EPT" not supported
		* "Activate tertiary controls" not supported
	 */

	// TODO: for host-state fields, update vmcs of guest hv.

	/* Translate VMCS12 to VMCS02 */
	HALT_ON_ERRORCOND(__vmx_vmptrld(vmcs12_info->vmcs02_ptr));
	result = xmhf_nested_arch_x86vmx_vmcs12_to_vmcs02(vcpu, &vmcs12_info->vmcs12_value);

	/* When a problem happens, translate back to L1 guest */
	if (result != VM_INST_SUCCESS) {
		HALT_ON_ERRORCOND(__vmx_vmptrld(hva2spa((void*)vcpu->vmx_vmcs_vaddr)));
		return result;
	}

	/* From now on, cannot fail */
	vcpu->vmx_nested_is_vmx_root_operation = 0;

	if (vmcs12_info->launched) {
		__vmx_vmentry_vmresume(r);
	} else {
		vmcs12_info->launched = 1;
		__vmx_vmentry_vmlaunch(r);
	}

	HALT_ON_ERRORCOND(0 && "VM entry should never return");
	return 0;
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

/*
 * Virtualize fields in VCPU that tracks nested virtualization information
 */
void xmhf_nested_arch_x86vmx_vcpu_init(VCPU *vcpu)
{
	u32 i;
	vcpu->vmx_nested_is_vmx_operation = 0;
	vcpu->vmx_nested_vmxon_pointer = 0;
	vcpu->vmx_nested_is_vmx_root_operation = 0;
	vcpu->vmx_nested_current_vmcs_pointer = CUR_VMCS_PTR_INVALID;
	/* Compute MSRs for the guest */
	for (i = 0; i < IA32_VMX_MSRCOUNT; i++) {
		vcpu->vmx_nested_msrs[i] = vcpu->vmx_msrs[i];
	}
	{
		u64 vmx_basic_msr = vcpu->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];
		/* Set bits 44:32 to 4096 (require a full page of VMCS region) */
		vmx_basic_msr &= ~0x00001fff00000000ULL;
		vmx_basic_msr |= 0x0000100000000000ULL;
		/* Do not support dual-monitor treatment of SMI and SMM */
		vmx_basic_msr &= ~(1ULL << 49);
		vcpu->vmx_nested_msrs[INDEX_IA32_VMX_BASIC_MSR] = vmx_basic_msr;
	}
	/* INDEX_IA32_VMX_PINBASED_CTLS_MSR: not changed */
	{
		/* "Activate tertiary controls" not supported */
		u64 mask = ~(1ULL << (32 + VMX_PROCBASED_ACTIVATE_TERTIARY_CONTROLS));
		vcpu->vmx_nested_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] &= mask;
		vcpu->vmx_nested_msrs[INDEX_IA32_VMX_TRUE_PROCBASED_CTLS_MSR] &= mask;
	}
	{
		/*
		 * Modifying IA32_PAT and IA32_EFER and CET state not supported yet.
		 * Need some extra logic to protect XMHF's states.
		 */
		u64 mask = ~(1ULL << (32 + VMX_VMEXIT_SAVE_IA32_PAT));
		mask &= ~(1ULL << (32 + VMX_VMEXIT_LOAD_IA32_PAT));
		mask &= ~(1ULL << (32 + VMX_VMEXIT_SAVE_IA32_EFER));
		mask &= ~(1ULL << (32 + VMX_VMEXIT_LOAD_IA32_EFER));
		mask &= ~(1ULL << (32 + VMX_VMEXIT_LOAD_CET_STATE));
		vcpu->vmx_nested_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] &= mask;
	}
	{
		/*
		 * Modifying IA32_PAT and IA32_EFER and CET state not supported yet.
		 * Need some extra logic to protect XMHF's states.
		 */
		u64 mask = ~(1ULL << (32 + VMX_VMENTRY_LOAD_IA32_PAT));
		mask &= ~(1ULL << (32 + VMX_VMENTRY_LOAD_IA32_EFER));
		mask &= ~(1ULL << (32 + VMX_VMENTRY_LOAD_CET_STATE));
		vcpu->vmx_nested_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR] &= mask;
	}
	{
		/* VMWRITE to VM-exit information field not supported */
		u64 mask = ~(1ULL << 29);
		vcpu->vmx_nested_msrs[INDEX_IA32_VMX_MISC_MSR] &= mask;
	}
	/* INDEX_IA32_VMX_CR0_FIXED0_MSR: not changed */
	/* INDEX_IA32_VMX_CR0_FIXED1_MSR: not changed */
	/* INDEX_IA32_VMX_CR4_FIXED0_MSR: not changed */
	/* INDEX_IA32_VMX_CR4_FIXED1_MSR: not changed */
	/* INDEX_IA32_VMX_VMCS_ENUM_MSR: not changed */
	{
		/* "Enable VPID" not supported */
		u64 mask = ~(1ULL << (32 + VMX_SECPROCBASED_ENABLE_VPID));
		/* "VMCS shadowing" not supported */
		mask &= ~(1ULL << (32 + VMX_SECPROCBASED_VMCS_SHADOWING));
		/* "Enable EPT" not supported */
		mask &= ~(1ULL << (32 + VMX_SECPROCBASED_ENABLE_EPT));
		/* "Unrestricted guest" not supported */
		mask &= ~(1ULL << (32 + VMX_SECPROCBASED_UNRESTRICTED_GUEST));
		/* "Sub-page write permissions for EPT" not supported */
		mask &= ~(1ULL << (32 + VMX_SECPROCBASED_SUB_PAGE_WRITE_PERMISSIONS_FOR_EPT));
		vcpu->vmx_nested_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] &= mask;
	}
	/* Select IA32_VMX_* or IA32_VMX_TRUE_* in guest mode */
	if (vcpu->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR] & (1ULL << 55)) {
		vcpu->vmx_nested_pinbased_ctls =
			vcpu->vmx_nested_msrs[INDEX_IA32_VMX_TRUE_PINBASED_CTLS_MSR];
		vcpu->vmx_nested_procbased_ctls =
			vcpu->vmx_nested_msrs[INDEX_IA32_VMX_TRUE_PROCBASED_CTLS_MSR];
		vcpu->vmx_nested_exit_ctls =
			vcpu->vmx_nested_msrs[INDEX_IA32_VMX_TRUE_EXIT_CTLS_MSR];
		vcpu->vmx_nested_entry_ctls =
			vcpu->vmx_nested_msrs[INDEX_IA32_VMX_TRUE_ENTRY_CTLS_MSR];
		} else {
		vcpu->vmx_nested_pinbased_ctls =
			vcpu->vmx_nested_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR];
		vcpu->vmx_nested_procbased_ctls =
			vcpu->vmx_nested_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR];
		vcpu->vmx_nested_exit_ctls =
			vcpu->vmx_nested_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR];
		vcpu->vmx_nested_entry_ctls =
			vcpu->vmx_nested_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR];
	}
}

void xmhf_nested_arch_x86vmx_handle_vmexit(VCPU *vcpu, struct regs *r)
{
	vmcs12_info_t *vmcs12_info = find_current_vmcs12(vcpu);
	xmhf_nested_arch_x86vmx_vmread_all(vcpu, "Nested VMEXIT: ");
	xmhf_nested_arch_x86vmx_vmcs02_to_vmcs12(vcpu, &vmcs12_info->vmcs12_value);
	(void) r;
	HALT_ON_ERRORCOND(0 && "TODO frontier");
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
		gva_t addr = _vmx_decode_m64(vcpu, r);
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

void xmhf_nested_arch_x86vmx_handle_vmlaunch_vmresume(VCPU *vcpu,
														struct regs *r,
														int is_vmresume)
{
	if (_vmx_nested_check_ud(vcpu, 0)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		// TODO: VMEXIT
		HALT_ON_ERRORCOND(0 && "Not implemented");
	} else if (_vmx_guest_get_cpl(vcpu) > 0) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
	} else {
		if (vcpu->vmx_nested_current_vmcs_pointer == CUR_VMCS_PTR_INVALID) {
			_vmx_nested_vm_fail_invalid(vcpu);
		} else if (vcpu->vmcs.guest_interruptibility & (1U << 1)) {
			/* Blocking by MOV SS */
			_vmx_nested_vm_fail_valid
				(vcpu, VM_INST_ERRNO_VMENTRY_EVENT_BLOCK_MOVSS);
		} else {
			vmcs12_info_t *vmcs12_info = find_current_vmcs12(vcpu);
			u32 error_number;
			if (!is_vmresume && vmcs12_info->launched) {
				error_number = VM_INST_ERRNO_VMLAUNCH_NONCLEAR_VMCS;
			} else if (is_vmresume && !vmcs12_info->launched) {
				error_number = VM_INST_ERRNO_VMRESUME_NONLAUNCH_VMCS;
			} else {
				error_number = _vmx_vmentry(vcpu, vmcs12_info, r);
			}
			_vmx_nested_vm_fail_valid(vcpu, error_number);
		}
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	}
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
		gva_t addr = _vmx_decode_m64(vcpu, r);
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
				vmcs12_info_t *vmcs12_info = find_active_vmcs12(vcpu, vmcs_ptr);
				if (vmcs12_info == NULL) {
					new_active_vmcs12(vcpu, vmcs_ptr, rev);
				}
				vcpu->vmx_nested_current_vmcs_pointer = vmcs_ptr;
				_vmx_nested_vm_succeed(vcpu);
			}
		}
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	}
}

void xmhf_nested_arch_x86vmx_handle_vmptrst(VCPU *vcpu, struct regs *r)
{
	printf("CPU(0x%02x): %s(): r=%p\n", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_nested_arch_x86vmx_handle_vmread(VCPU *vcpu, struct regs *r)
{
	if (_vmx_nested_check_ud(vcpu, 0)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		/* Note: Currently does not support 1-setting of "VMCS shadowing" */
		// TODO: VMEXIT
		HALT_ON_ERRORCOND(0 && "Not implemented");
	} else if (_vmx_guest_get_cpl(vcpu) > 0) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
	} else {
		if (vcpu->vmx_nested_current_vmcs_pointer == CUR_VMCS_PTR_INVALID) {
			/* Note: Currently does not support 1-setting of "VMCS shadowing" */
			_vmx_nested_vm_fail_invalid(vcpu);
		} else {
			ulong_t encoding;
			uintptr_t pvalue;
			int value_mem_reg;
			size_t size = _vmx_decode_vmread_vmwrite(vcpu, r, 1, &encoding,
													&pvalue, &value_mem_reg);
			size_t offset = xmhf_nested_arch_x86vmx_vmcs_field_find(encoding);
			if (offset == (size_t) (-1)) {
				_vmx_nested_vm_fail_valid
					(vcpu, VM_INST_ERRNO_VMRDWR_UNSUPP_VMCS_COMP);
			} else {
				/* Note: Currently does not support VMCS shadowing */
				vmcs12_info_t *vmcs12_info = find_current_vmcs12(vcpu);
				ulong_t value = xmhf_nested_arch_x86vmx_vmcs_read
					(&vmcs12_info->vmcs12_value, offset, size);
				if (value_mem_reg) {
					*(ulong_t *)pvalue = value;
				} else {
					guestmem_hptw_ctx_pair_t ctx_pair;
					guestmem_init(vcpu, &ctx_pair);
					guestmem_copy_h2gv(&ctx_pair, 0, pvalue, &value, size);
				}
				_vmx_nested_vm_succeed(vcpu);
			}
		}
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	}
}

void xmhf_nested_arch_x86vmx_handle_vmwrite(VCPU *vcpu, struct regs *r)
{
	if (_vmx_nested_check_ud(vcpu, 0)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		/* Note: Currently does not support 1-setting of "VMCS shadowing" */
		// TODO: VMEXIT
		HALT_ON_ERRORCOND(0 && "Not implemented");
	} else if (_vmx_guest_get_cpl(vcpu) > 0) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
	} else {
		if (vcpu->vmx_nested_current_vmcs_pointer == CUR_VMCS_PTR_INVALID) {
			/* Note: Currently does not support 1-setting of "VMCS shadowing" */
			_vmx_nested_vm_fail_invalid(vcpu);
		} else {
			ulong_t encoding;
			uintptr_t pvalue;
			int value_mem_reg;
			size_t size = _vmx_decode_vmread_vmwrite(vcpu, r, 1, &encoding,
													&pvalue, &value_mem_reg);
			size_t offset = xmhf_nested_arch_x86vmx_vmcs_field_find(encoding);
			if (offset == (size_t) (-1)) {
				_vmx_nested_vm_fail_valid
					(vcpu, VM_INST_ERRNO_VMRDWR_UNSUPP_VMCS_COMP);
			} else if (!xmhf_nested_arch_x86vmx_vmcs_writable(offset)) {
				/*
				 * Note: currently not supporting writing to VM-exit
				 * information field
				 */
				_vmx_nested_vm_fail_valid
					(vcpu, VM_INST_ERRNO_VMWRITE_RO_VMCS_COMP);
			} else {
				/* Note: Currently does not support VMCS shadowing */
				vmcs12_info_t *vmcs12_info = find_current_vmcs12(vcpu);
				ulong_t value;
				if (value_mem_reg) {
					value = *(ulong_t *)pvalue;
				} else {
					guestmem_hptw_ctx_pair_t ctx_pair;
					guestmem_init(vcpu, &ctx_pair);
					guestmem_copy_gv2h(&ctx_pair, 0, &value, pvalue, size);
				}
				xmhf_nested_arch_x86vmx_vmcs_write(&vmcs12_info->vmcs12_value,
													offset, value, size);
				_vmx_nested_vm_succeed(vcpu);
			}
		}
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	}
}

void xmhf_nested_arch_x86vmx_handle_vmxoff(VCPU *vcpu, struct regs *r)
{
	printf("CPU(0x%02x): %s(): r=%p\n", vcpu->id, __func__, r);
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
			gva_t addr = _vmx_decode_m64(vcpu, r);
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
					active_vmcs12_array_init(vcpu);
					_vmx_nested_vm_succeed(vcpu);
				}
			}
			vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
		}
	} else {
		/* This may happen if guest tries nested virtualization */
		printf("Not implemented, HALT!\n");
		HALT();
	}
}

