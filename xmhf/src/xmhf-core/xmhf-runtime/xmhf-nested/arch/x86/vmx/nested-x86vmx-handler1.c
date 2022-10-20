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

// nested-x86vmx-handler1.c
// Intercept handlers for nested virtualization operations from L1
// author: Eric Li (xiaoyili@andrew.cmu.edu)
#include <xmhf.h>
#include "nested-x86vmx-handler1.h"
#include "nested-x86vmx-handler2.h"
#include "nested-x86vmx-vmcs12.h"
#include "nested-x86vmx-vminsterr.h"
#include "nested-x86vmx-ept12.h"

#define CUR_VMCS_PTR_INVALID 0xffffffffffffffffULL

#define VMX_INST_RFLAGS_MASK \
	((u64) (EFLAGS_CF | EFLAGS_PF | EFLAGS_AF | EFLAGS_ZF | EFLAGS_SF | \
			EFLAGS_OF))

#define INVALID_VMCS12_INDEX UINT32_MAX

_Static_assert(VMX_NESTED_MAX_ACTIVE_VMCS < INVALID_VMCS12_INDEX);

#ifdef __DEBUG_QEMU__
bool is_in_kvm = false;
#endif							/* !__DEBUG_QEMU__ */

/*
 * This structure follows Table 26-14. Format of the VM-Exit
 * Instruction-Information Field as Used for VMREAD and VMWRITE in Intel's
 * System Programming Guide, Order Number 325384. It covers all structures in
 * Table 26-13. Format of the VM-Exit Instruction-Information Field as Used
 * for VMCLEAR, VMPTRLD, VMPTRST, VMXON, XRSTORS, and XSAVES. It also covers
 * all structures in Table 26-9. Format of the VM-Exit Instruction-Information
 * Field as Used for INVEPT, INVPCID, and INVVPID.
 */
union _vmx_decode_vm_inst_info {
	struct {
		u32 scaling:2;
		u32 undefined2:1;
		u32 reg1:4;				/* Undefined in Table 26-9 and 26-13. */
		u32 address_size:3;
		u32 mem_reg:1;			/* Cleared to 0 in Table 26-9 and 26-13. */
		u32 undefined14_11:4;
		u32 segment_register:3;
		u32 index_reg:4;
		u32 index_reg_invalid:1;
		u32 base_reg:4;
		u32 base_reg_invalid:1;
		u32 reg2:4;				/* Undefined in Table 26-13. */
	};
	u32 raw;
};

/* Track all active VMCS12's in each CPU */
static vmcs12_info_t
	cpu_active_vmcs12[MAX_VCPU_ENTRIES][VMX_NESTED_MAX_ACTIVE_VMCS];

/* The VMCS02's in each CPU */
static u8 cpu_vmcs02[MAX_VCPU_ENTRIES][VMX_NESTED_MAX_ACTIVE_VMCS][PAGE_SIZE_4K]
	__attribute__((aligned(PAGE_SIZE_4K)));

#ifdef VMX_NESTED_USE_SHADOW_VMCS
/*
 * A blank page in memory that is only read from. This page is used as VMREAD
 * and VMWRITE bitmaps when using shadow VMCS.
 */
static u8 blank_page[PAGE_SIZE_4K] __attribute__((aligned(PAGE_SIZE_4K)));

/* The shadow VMCS12's in each CPU */
static u8 cpu_shadow_vmcs12[MAX_VCPU_ENTRIES][VMX_NESTED_MAX_ACTIVE_VMCS]
	[PAGE_SIZE_4K]
	__attribute__((aligned(PAGE_SIZE_4K)));
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */

/*
 * Given a segment index, return the segment offset
 * TODO: do we need to check access rights?
 */
static uintptr_t _vmx_decode_seg(u32 seg, VCPU * vcpu)
{
	switch (seg) {
	case 0:
		return vcpu->vmcs.guest_ES_base;
	case 1:
		return vcpu->vmcs.guest_CS_base;
	case 2:
		return vcpu->vmcs.guest_SS_base;
	case 3:
		return vcpu->vmcs.guest_DS_base;
	case 4:
		return vcpu->vmcs.guest_FS_base;
	case 5:
		return vcpu->vmcs.guest_GS_base;
	default:
		HALT_ON_ERRORCOND(0 && "Unexpected segment");
		return 0;
	}
}

/*
 * Access size bytes of memory referenced in memory operand of instruction.
 * The memory content in the guest is returned in dst.
 */
static gva_t _vmx_decode_mem_operand(VCPU * vcpu, struct regs *r)
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
	case 0:					/* 16-bit */
		addr &= 0xffffUL;
		break;
	case 1:					/* 32-bit */
		/* This case may happen if 32-bit guest hypervisor runs in AMD64 XMHF */
		addr &= 0xffffffffUL;
		break;
	case 2:					/* 64-bit */
#ifdef __I386__
		HALT_ON_ERRORCOND(0 && "Unexpected 64-bit address size in i386");
#elif !defined(__AMD64__)
#error "Unsupported Arch"
#endif							/* __I386__ */
		break;
	default:
		HALT_ON_ERRORCOND(0 && "Unexpected address size");
		break;
	}
	return addr;
}

/*
 * Decode the operand for instructions that take one register operand and one
 * m64 operand. Following Table 26-9. Format of the VM-Exit
 * Instruction-Information Field as Used for INVEPT, INVPCID, and INVVPID in
 * Intel's System Programming Guide, Order Number 325384. The register operand
 * is returned in ptype. The address of memory operand is returned in
 * ppdescriptor.
 */
static void _vmx_decode_r_m128(VCPU * vcpu, struct regs *r, ulong_t * ptype,
							   gva_t * ppdescriptor)
{
	union _vmx_decode_vm_inst_info inst_info;
	size_t size = (VCPU_g64(vcpu) ? sizeof(u64) : sizeof(u32));
	uintptr_t *type;
	inst_info.raw = vcpu->vmcs.info_vmx_instruction_information;
	HALT_ON_ERRORCOND(inst_info.mem_reg == 0);
	type = _vmx_decode_reg(inst_info.reg2, vcpu, r);
	*ptype = 0;
	memcpy(ptype, type, size);
	*ppdescriptor = _vmx_decode_mem_operand(vcpu, r);
}

/*
 * Decode the operand for instructions that take one m64 operand. Following
 * Table 26-13. Format of the VM-Exit Instruction-Information Field as Used
 * for VMCLEAR, VMPTRLD, VMPTRST, VMXON, XRSTORS, and XSAVES in Intel's
 * System Programming Guide, Order Number 325384.
 */
static gva_t _vmx_decode_m64(VCPU * vcpu, struct regs *r)
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
static size_t _vmx_decode_vmread_vmwrite(VCPU * vcpu, struct regs *r,
										 int is_vmwrite, ulong_t * pencoding,
										 uintptr_t * ppvalue,
										 int *pvalue_mem_reg)
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
static void active_vmcs12_array_init(VCPU * vcpu)
{
	int i;
	for (i = 0; i < VMX_NESTED_MAX_ACTIVE_VMCS; i++) {
		spa_t vmcs02_ptr = hva2spa(cpu_vmcs02[vcpu->idx][i]);
#ifdef VMX_NESTED_USE_SHADOW_VMCS
		spa_t vmcs12_shadow_ptr = hva2spa(cpu_shadow_vmcs12[vcpu->idx][i]);
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
		cpu_active_vmcs12[vcpu->idx][i].index = i;
		cpu_active_vmcs12[vcpu->idx][i].vmcs12_ptr = CUR_VMCS_PTR_INVALID;
		cpu_active_vmcs12[vcpu->idx][i].vmcs02_ptr = vmcs02_ptr;
#ifdef VMX_NESTED_USE_SHADOW_VMCS
		cpu_active_vmcs12[vcpu->idx][i].vmcs12_shadow_ptr = vmcs12_shadow_ptr;
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
	}
}

/*
 * Look up vmcs_ptr in list of active VMCS12's tracked in the current CPU.
 * A return value of 0 means the VMCS is not active.
 * A VMCS is defined to be active if this function returns non-zero.
 * When vmcs_ptr = CUR_VMCS_PTR_INVALID, a empty slot is returned.
 */
static vmcs12_info_t *find_active_vmcs12(VCPU * vcpu, gpa_t vmcs_ptr)
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
 * Invalidate guest_ept_cache_line for all vmcs12_info in vcpu. This function
 * is intended to be used when asynchronously invalidating EPT02.
 */
void xmhf_nested_arch_x86vmx_clear_all_vmcs12_ept02(VCPU * vcpu)
{
	int i;
	for (i = 0; i < VMX_NESTED_MAX_ACTIVE_VMCS; i++) {
		cpu_active_vmcs12[vcpu->idx][i].guest_ept_cache_line = NULL;
	}
}

/* Add a new VMCS12 to the array of actives. Initializes underlying VMCS02 */
static vmcs12_info_t *new_active_vmcs12(VCPU * vcpu, gpa_t vmcs_ptr, u32 rev)
{
	vmcs12_info_t *vmcs12_info;
	HALT_ON_ERRORCOND(vmcs_ptr != CUR_VMCS_PTR_INVALID);
	vmcs12_info = find_active_vmcs12(vcpu, CUR_VMCS_PTR_INVALID);
	if (vmcs12_info == NULL) {
		HALT_ON_ERRORCOND(0 && "Too many active VMCS's");
	}
	vmcs12_info->vmcs12_ptr = vmcs_ptr;
	HALT_ON_ERRORCOND(__vmx_vmclear(vmcs12_info->vmcs02_ptr));
	*(u32 *) spa2hva(vmcs12_info->vmcs02_ptr) = rev;
#ifdef VMX_NESTED_USE_SHADOW_VMCS
	if (_vmx_hasctl_vmcs_shadowing(&vcpu->vmx_caps)) {
		/* Note: this memset is probably unnecessary, but is here to be safe */
		memset(spa2hva(vmcs12_info->vmcs12_shadow_ptr), 0, PAGE_SIZE_4K);
		HALT_ON_ERRORCOND(__vmx_vmclear(vmcs12_info->vmcs12_shadow_ptr));
		*(u32 *) spa2hva(vmcs12_info->vmcs12_shadow_ptr) = 0x80000000U | rev;
	}
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
	vmcs12_info->launched = 0;
	/* vmcs12_info->vmcs12_value will be initialized by caller */
	/* vmcs02_vmexit_msr_store_area need to process the same MSRs as VMCS01 */
	memset(&vmcs12_info->vmcs02_vmexit_msr_store_area, 0,
		   sizeof(vmcs12_info->vmcs02_vmexit_msr_store_area));
	memcpy(vmcs12_info->vmcs02_vmexit_msr_store_area,
		   (void *)vcpu->vmx_vaddr_msr_area_guest,
		   vcpu->vmcs.control_VM_exit_MSR_store_count * sizeof(msr_entry_t));
	/* vmcs02_vmexit_msr_load_area need to process the same MSRs as VMCS01 */
	memset(&vmcs12_info->vmcs02_vmexit_msr_load_area, 0,
		   sizeof(vmcs12_info->vmcs02_vmexit_msr_load_area));
	memcpy(vmcs12_info->vmcs02_vmexit_msr_load_area,
		   (void *)vcpu->vmx_vaddr_msr_area_host,
		   vcpu->vmcs.control_VM_exit_MSR_load_count * sizeof(msr_entry_t));
	/* vmcs02_vmentry_msr_load_area need to process the same MSRs as VMCS01 */
	memset(&vmcs12_info->vmcs02_vmentry_msr_load_area, 0,
		   sizeof(vmcs12_info->vmcs02_vmentry_msr_load_area));
	memcpy(vmcs12_info->vmcs02_vmentry_msr_load_area,
		   (void *)vcpu->vmx_vaddr_msr_area_guest,
		   vcpu->vmcs.control_VM_entry_MSR_load_count * sizeof(msr_entry_t));
	vmcs12_info->guest_ept_enable = 0;
	vmcs12_info->guest_ept_root = 0;
	vmcs12_info->guest_nmi_exiting = false;
	vmcs12_info->guest_virtual_nmis = false;
	vmcs12_info->guest_nmi_window_exiting = false;
	vmcs12_info->guest_block_nmi = false;
	vmcs12_info->guest_vmcs_block_nmi_overridden = false;
	vmcs12_info->guest_vmcs_block_nmi = false;
	return vmcs12_info;
}

/* Return whether the CPU has a current VMCS12 loaded */
static bool cpu_has_current_vmcs12(VCPU * vcpu)
{
	return vcpu->vmx_nested_cur_vmcs12 != INVALID_VMCS12_INDEX;
}

/*
 * Find VMCS12 pointed by current VMCS pointer.
 * It is illegal to call this function with a invalid current VMCS pointer.
 * This function will never return NULL.
 */
vmcs12_info_t *xmhf_nested_arch_x86vmx_find_current_vmcs12(VCPU * vcpu)
{
	HALT_ON_ERRORCOND(cpu_has_current_vmcs12(vcpu));
	HALT_ON_ERRORCOND(vcpu->vmx_nested_cur_vmcs12 < VMX_NESTED_MAX_ACTIVE_VMCS);
	return &cpu_active_vmcs12[vcpu->idx][vcpu->vmx_nested_cur_vmcs12];
}

/* The VMsucceed pseudo-function in SDM "29.2 CONVENTIONS" */
static void _vmx_nested_vm_succeed(VCPU * vcpu)
{
	vcpu->vmcs.guest_RFLAGS &= ~VMX_INST_RFLAGS_MASK;
}

static void _vmx_nested_vm_fail_valid(VCPU * vcpu, u32 error_number)
{
	vmcs12_info_t *vmcs12_info;
	vmcs12_info = xmhf_nested_arch_x86vmx_find_current_vmcs12(vcpu);
	vcpu->vmcs.guest_RFLAGS &= ~VMX_INST_RFLAGS_MASK;
	vcpu->vmcs.guest_RFLAGS |= EFLAGS_ZF;
	vmcs12_info->vmcs12_value.info_vminstr_error = error_number;
#ifdef VMX_NESTED_USE_SHADOW_VMCS
	if (_vmx_hasctl_vmcs_shadowing(&vcpu->vmx_caps)) {
		u64 cur_vmcs;
		HALT_ON_ERRORCOND(__vmx_vmptrst(&cur_vmcs));
		HALT_ON_ERRORCOND(cur_vmcs == hva2spa((void *)vcpu->vmx_vmcs_vaddr));
		HALT_ON_ERRORCOND(__vmx_vmptrld(vmcs12_info->vmcs12_shadow_ptr));
		__vmx_vmwrite32(VMCSENC_info_vminstr_error, error_number);
		HALT_ON_ERRORCOND(__vmx_vmptrld(cur_vmcs));
	}
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
}

static void _vmx_nested_vm_fail_invalid(VCPU * vcpu)
{
	vcpu->vmcs.guest_RFLAGS &= ~VMX_INST_RFLAGS_MASK;
	vcpu->vmcs.guest_RFLAGS |= EFLAGS_CF;
}

static void _vmx_nested_vm_fail(VCPU * vcpu, u32 error_number)
{
	if (cpu_has_current_vmcs12(vcpu)) {
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
static u32 _vmx_check_physical_addr_width(VCPU * vcpu, u64 addr)
{
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
		paddrmask &= (1ULL << 32) - 1ULL;
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
static u64 _vmx_guest_get_guest_cr0(VCPU * vcpu)
{
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
static u64 _vmx_guest_get_guest_cr4(VCPU * vcpu)
{
	return ((vcpu->vmcs.guest_CR4 & ~vcpu->vmcs.control_CR4_mask) |
			(vcpu->vmcs.control_CR4_shadow & vcpu->vmcs.control_CR4_mask));
}

/* Get CPL of guest */
static u32 _vmx_guest_get_cpl(VCPU * vcpu)
{
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
static u32 _vmx_nested_check_ud(VCPU * vcpu, int is_vmxon)
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
void xmhf_nested_arch_x86vmx_vcpu_init(VCPU * vcpu)
{
	u32 i;
	vcpu->vmx_nested_is_vmx_operation = 0;
	vcpu->vmx_nested_vmxon_pointer = 0;
	vcpu->vmx_nested_is_vmx_root_operation = 0;
	vcpu->vmx_nested_cur_vmcs12 = INVALID_VMCS12_INDEX;

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
		/* MSR bitmap not supported */
		mask &= ~(1ULL << (32 + VMX_PROCBASED_USE_MSR_BITMAPS));
		vcpu->vmx_nested_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] &= mask;
		vcpu->vmx_nested_msrs[INDEX_IA32_VMX_TRUE_PROCBASED_CTLS_MSR] &= mask;
	}
	{
		/* Modifying CET state not supported yet (need extra logic) */
		u64 mask = ~(1ULL << (32 + VMX_VMEXIT_LOAD_CET_STATE));
		vcpu->vmx_nested_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] &= mask;
	}
	{
		/* Modifying CET state not supported yet (need extra logic) */
		u64 mask = ~(1ULL << (32 + VMX_VMENTRY_LOAD_CET_STATE));
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
		/* "VMCS shadowing" not supported */
		u64 mask = ~(1ULL << (32 + VMX_SECPROCBASED_VMCS_SHADOWING));
		/* "Sub-page write permissions for EPT" not supported */
		mask &=
			~(1ULL <<
			  (32 + VMX_SECPROCBASED_SUB_PAGE_WRITE_PERMISSIONS_FOR_EPT));
		vcpu->vmx_nested_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] &= mask;
	}
	{
		/* "accessed and dirty flags for EPT" not supported */
		u64 mask = ~(1ULL << 21);
		vcpu->vmx_nested_msrs[INDEX_IA32_VMX_EPT_VPID_CAP_MSR] &= mask;
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
	vcpu->vmx_nested_ept02_flush_disable = false;
	vcpu->vmx_nested_ept02_flush_visited = false;

	/* Initialize EPT and VPID cache */
	xmhf_nested_arch_x86vmx_ept_init(vcpu);
	xmhf_nested_arch_x86vmx_vpid_init(vcpu);

#ifdef __DEBUG_QEMU__
	/* Compute is_in_kvm */
	{
		u32 eax, ebx, ecx, edx;
		cpuid(0x40000000U, &eax, &ebx, &ecx, &edx);
		if (ebx == 0x4b4d564bU && ecx == 0x564b4d56U && edx == 0x0000004d) {
			is_in_kvm = true;
			printf("CPU(0x%02x): KVM detected\n", vcpu->id);
		}
	}
#endif							/* !__DEBUG_QEMU__ */
}

void xmhf_nested_arch_x86vmx_handle_vmentry_fail(VCPU * vcpu, bool is_resume)
{
	const char *inst_name = is_resume ? "VMRESUME" : "VMLAUNCH";
	printf("CPU(0x%02x): %s error in nested virtualization\n", vcpu->id,
		   inst_name);
	xmhf_nested_arch_x86vmx_vmread_all(vcpu, "VMCS02.");
	printf("CPU(0x%02x): HALT!\n", vcpu->id);
	HALT();
}

void xmhf_nested_arch_x86vmx_handle_invept(VCPU * vcpu, struct regs *r)
{
	if (_vmx_nested_check_ud(vcpu, 0)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		/*
		 * Guest hypervisor is likely performing nested virtualization.
		 * This case should be handled in
		 * xmhf_parteventhub_arch_x86vmx_intercept_handler(). So panic if we
		 * end up here.
		 */
		HALT_ON_ERRORCOND(0 && "Nested vmexit should be handled elsewhere");
	} else if (_vmx_guest_get_cpl(vcpu) > 0) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
	} else {
		ulong_t type;
		gva_t pdescriptor;
		struct {
			u64 eptp;
			u64 reserved;
		} descriptor;
		guestmem_hptw_ctx_pair_t ctx_pair;
		_vmx_decode_r_m128(vcpu, r, &type, &pdescriptor);
		guestmem_init(vcpu, &ctx_pair);
		guestmem_copy_gv2h(&ctx_pair, 0, &descriptor, pdescriptor,
						   sizeof(descriptor));
		if (descriptor.reserved) {
			/* SDM does not say should fail, so just print a warning */
			printf("CPU(0x%02x): warning: INVEPT reserved 0x%016llx != 0\n",
				   vcpu->id, descriptor.reserved);
		}
		xmhf_nested_arch_x86vmx_block_ept02_flush(vcpu);
		switch (type) {
		case VMX_INVEPT_SINGLECONTEXT:
			{
				gpa_t ept12;
				/* Check whether EPTP will result in VMENTRY failure */
				if (!xmhf_nested_arch_x86vmx_check_ept_lower_bits
					(descriptor.eptp, &ept12)) {
					u32 errno = VM_INST_ERRNO_INVALID_OPERAND_INVEPT_INVVPID;
					printf("CPU(0x%02x): INVEPT rejects EPTP 0x%016llx\n",
						   vcpu->id, descriptor.eptp);
					_vmx_nested_vm_fail(vcpu, errno);
				} else {
					xmhf_nested_arch_x86vmx_invept_single_context(vcpu, ept12);
					_vmx_nested_vm_succeed(vcpu);
				}
			}
			break;
		case VMX_INVEPT_GLOBAL:
			xmhf_nested_arch_x86vmx_invept_global(vcpu);
			_vmx_nested_vm_succeed(vcpu);
			break;
		default:
			_vmx_nested_vm_fail(vcpu,
								VM_INST_ERRNO_INVALID_OPERAND_INVEPT_INVVPID);
			break;
		}
		xmhf_nested_arch_x86vmx_unblock_ept02_flush(vcpu);
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	}
}

void xmhf_nested_arch_x86vmx_handle_invvpid(VCPU * vcpu, struct regs *r)
{
	if (_vmx_nested_check_ud(vcpu, 0)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		/*
		 * Guest hypervisor is likely performing nested virtualization.
		 * This case should be handled in
		 * xmhf_parteventhub_arch_x86vmx_intercept_handler(). So panic if we
		 * end up here.
		 */
		HALT_ON_ERRORCOND(0 && "Nested vmexit should be handled elsewhere");
	} else if (_vmx_guest_get_cpl(vcpu) > 0) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
	} else {
		ulong_t type;
		gva_t pdescriptor;
		bool succeed = false;
		struct {
			u16 vpid;
			u16 reserved_31_16;
			u32 reserved_63_32;
			u64 linear_addr;
		} descriptor;
		guestmem_hptw_ctx_pair_t ctx_pair;
		_vmx_decode_r_m128(vcpu, r, &type, &pdescriptor);
		guestmem_init(vcpu, &ctx_pair);
		guestmem_copy_gv2h(&ctx_pair, 0, &descriptor, pdescriptor,
						   sizeof(descriptor));
		if (!descriptor.reserved_31_16 && !descriptor.reserved_63_32) {
			switch (type) {
			case VMX_INVVPID_INDIVIDUALADDRESS:
				if (descriptor.vpid) {
					if (xmhf_nested_arch_x86vmx_invvpid_indiv_addr
						(vcpu, descriptor.vpid, descriptor.linear_addr)) {
						succeed = true;
					}
				}
				break;
			case VMX_INVVPID_SINGLECONTEXT:
				if (descriptor.vpid) {
					xmhf_nested_arch_x86vmx_invvpid_single_ctx(vcpu,
															   descriptor.vpid);
					succeed = true;
				}
				break;
			case VMX_INVVPID_ALLCONTEXTS:
				xmhf_nested_arch_x86vmx_invvpid_all_ctx(vcpu);
				succeed = true;
				break;
			case VMX_INVVPID_SINGLECONTEXTGLOBAL:
				if (descriptor.vpid) {
					xmhf_nested_arch_x86vmx_invvpid_single_ctx_global
						(vcpu, descriptor.vpid);
					succeed = true;
				}
				break;
			default:
				break;
			}
		}
		if (succeed) {
			_vmx_nested_vm_succeed(vcpu);
		} else {
			_vmx_nested_vm_fail(vcpu,
								VM_INST_ERRNO_INVALID_OPERAND_INVEPT_INVVPID);
		}
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	}
}

void xmhf_nested_arch_x86vmx_handle_vmclear(VCPU * vcpu, struct regs *r)
{
	if (_vmx_nested_check_ud(vcpu, 0)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		/*
		 * Guest hypervisor is likely performing nested virtualization.
		 * This case should be handled in
		 * xmhf_parteventhub_arch_x86vmx_intercept_handler(). So panic if we
		 * end up here.
		 */
		HALT_ON_ERRORCOND(0 && "Nested vmexit should be handled elsewhere");
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
#ifdef VMX_NESTED_USE_SHADOW_VMCS
				/* Read VMCS12 values from the shadow VMCS */
				if (_vmx_hasctl_vmcs_shadowing(&vcpu->vmx_caps)) {
					struct nested_vmcs12 *vmcs12 = &vmcs12_info->vmcs12_value;
					HALT_ON_ERRORCOND(__vmx_vmptrld
									  (vmcs12_info->vmcs12_shadow_ptr));
					xmhf_nested_arch_x86vmx_vmcs_read_all(vcpu, vmcs12);
					HALT_ON_ERRORCOND(__vmx_vmptrld
									  (hva2spa((void *)vcpu->vmx_vmcs_vaddr)));
				}
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
				/* Write VMCS12 back to guest */
				HALT_ON_ERRORCOND(sizeof(vmcs12_info->vmcs12_value) <
								  PAGE_SIZE_4K - 8);
				guestmem_copy_h2gp(&ctx_pair, 0, vmcs_ptr + 8,
								   &vmcs12_info->vmcs12_value,
								   sizeof(vmcs12_info->vmcs12_value));
				/* Call VMCLEAR on VMCS02 */
				HALT_ON_ERRORCOND(__vmx_vmclear(vmcs12_info->vmcs02_ptr));
#ifdef VMX_NESTED_USE_SHADOW_VMCS
				if (_vmx_hasctl_vmcs_shadowing(&vcpu->vmx_caps)) {
					HALT_ON_ERRORCOND(__vmx_vmclear
									  (vmcs12_info->vmcs12_shadow_ptr));
				}
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
				/* Invalidate vmcs12_info */
				vmcs12_info->vmcs12_ptr = CUR_VMCS_PTR_INVALID;
				/* Check whether vmcs12_info is the current VMCS12 */
				if (vcpu->vmx_nested_cur_vmcs12 == vmcs12_info->index) {
					vcpu->vmx_nested_cur_vmcs12 = INVALID_VMCS12_INDEX;
#ifdef VMX_NESTED_USE_SHADOW_VMCS
					/*
					 * Make VMCS link pointer invalid so that VMCS shadowing
					 * will VMfailInvalid when guest executes VMREAD / VMWRITE.
					 */
					if (_vmx_hasctl_vmcs_shadowing(&vcpu->vmx_caps)) {
						vcpu->vmcs.guest_VMCS_link_pointer =
							CUR_VMCS_PTR_INVALID;
					}
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
				}
			}
			_vmx_nested_vm_succeed(vcpu);
		}
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	}
}

void xmhf_nested_arch_x86vmx_handle_vmlaunch_vmresume(VCPU * vcpu,
													  struct regs *r,
													  int is_vmresume)
{
	if (_vmx_nested_check_ud(vcpu, 0)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		/*
		 * Guest hypervisor is likely performing nested virtualization.
		 * This case should be handled in
		 * xmhf_parteventhub_arch_x86vmx_intercept_handler(). So panic if we
		 * end up here.
		 */
		HALT_ON_ERRORCOND(0 && "Nested vmexit should be handled elsewhere");
	} else if (_vmx_guest_get_cpl(vcpu) > 0) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
	} else {
		if (!cpu_has_current_vmcs12(vcpu)) {
			_vmx_nested_vm_fail_invalid(vcpu);
		} else if (vcpu->vmcs.guest_interruptibility & (1U << 1)) {
			/* Blocking by MOV SS */
			_vmx_nested_vm_fail_valid
				(vcpu, VM_INST_ERRNO_VMENTRY_EVENT_BLOCK_MOVSS);
		} else {
			u32 error_number;
			vmcs12_info_t *vmcs12_info;
			vmcs12_info = xmhf_nested_arch_x86vmx_find_current_vmcs12(vcpu);
			if (!is_vmresume && vmcs12_info->launched) {
				error_number = VM_INST_ERRNO_VMLAUNCH_NONCLEAR_VMCS;
			} else if (is_vmresume && !vmcs12_info->launched) {
				error_number = VM_INST_ERRNO_VMRESUME_NONLAUNCH_VMCS;
			} else {
				error_number =
					xmhf_nested_arch_x86vmx_handle_vmentry(vcpu, vmcs12_info,
														   r);
			}
			_vmx_nested_vm_fail_valid(vcpu, error_number);
		}
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	}
}

void xmhf_nested_arch_x86vmx_handle_vmptrld(VCPU * vcpu, struct regs *r)
{
	if (_vmx_nested_check_ud(vcpu, 0)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		/*
		 * Guest hypervisor is likely performing nested virtualization.
		 * This case should be handled in
		 * xmhf_parteventhub_arch_x86vmx_intercept_handler(). So panic if we
		 * end up here.
		 */
		HALT_ON_ERRORCOND(0 && "Nested vmexit should be handled elsewhere");
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
			if ((rev & (1U << 31)) || (rev != ((u32) basic_msr & 0x7fffffffU))) {
				_vmx_nested_vm_fail
					(vcpu, VM_INST_ERRNO_VMPTRLD_WITH_INCORRECT_VMCS_REV_ID);
			} else {
				vmcs12_info_t *vmcs12_info = find_active_vmcs12(vcpu, vmcs_ptr);
				if (vmcs12_info == NULL) {
					vmcs12_info = new_active_vmcs12(vcpu, vmcs_ptr, rev);
					/* Initialize VMCS12 from guest memory */
					HALT_ON_ERRORCOND(sizeof(vmcs12_info->vmcs12_value) <
									  PAGE_SIZE_4K - 8);
					guestmem_copy_gp2h(&ctx_pair, 0, &vmcs12_info->vmcs12_value,
									   vmcs_ptr + 8,
									   sizeof(vmcs12_info->vmcs12_value));
#ifdef VMX_NESTED_USE_SHADOW_VMCS
					/* Write VMCS12 values to the shadow VMCS */
					if (_vmx_hasctl_vmcs_shadowing(&vcpu->vmx_caps)) {
						struct nested_vmcs12 *vmcs12 =
							&vmcs12_info->vmcs12_value;
						HALT_ON_ERRORCOND(__vmx_vmptrld
										  (vmcs12_info->vmcs12_shadow_ptr));
						xmhf_nested_arch_x86vmx_vmcs_write_all(vcpu, vmcs12);
						HALT_ON_ERRORCOND(__vmx_vmptrld
										  (hva2spa
										   ((void *)vcpu->vmx_vmcs_vaddr)));
					}
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
				}
				vcpu->vmx_nested_cur_vmcs12 = vmcs12_info->index;
#ifdef VMX_NESTED_USE_SHADOW_VMCS
				/* Use VMCS shadowing when available */
				if (_vmx_hasctl_vmcs_shadowing(&vcpu->vmx_caps)) {
					vcpu->vmcs.guest_VMCS_link_pointer =
						vmcs12_info->vmcs12_shadow_ptr;
				}
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
				_vmx_nested_vm_succeed(vcpu);
			}
		}
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	}
}

void xmhf_nested_arch_x86vmx_handle_vmptrst(VCPU * vcpu, struct regs *r)
{
	if (_vmx_nested_check_ud(vcpu, 0)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		/*
		 * Guest hypervisor is likely performing nested virtualization.
		 * This case should be handled in
		 * xmhf_parteventhub_arch_x86vmx_intercept_handler(). So panic if we
		 * end up here.
		 */
		HALT_ON_ERRORCOND(0 && "Nested vmexit should be handled elsewhere");
	} else if (_vmx_guest_get_cpl(vcpu) > 0) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
	} else {
		gva_t addr = _vmx_decode_m64(vcpu, r);
		gpa_t vmcs_ptr = CUR_VMCS_PTR_INVALID;
		guestmem_hptw_ctx_pair_t ctx_pair;
		guestmem_init(vcpu, &ctx_pair);
		if (cpu_has_current_vmcs12(vcpu)) {
			vmcs12_info_t *vmcs12_info;
			vmcs12_info = xmhf_nested_arch_x86vmx_find_current_vmcs12(vcpu);
			vmcs_ptr = vmcs12_info->vmcs12_ptr;
		}
		guestmem_copy_h2gv(&ctx_pair, 0, addr, &vmcs_ptr, sizeof(vmcs_ptr));
		_vmx_nested_vm_succeed(vcpu);
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	}
}

void xmhf_nested_arch_x86vmx_handle_vmread(VCPU * vcpu, struct regs *r)
{
	if (_vmx_nested_check_ud(vcpu, 0)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		/*
		 * Guest hypervisor is likely performing nested virtualization.
		 * This case should be handled in
		 * xmhf_parteventhub_arch_x86vmx_intercept_handler(). So panic if we
		 * end up here.
		 */
		HALT_ON_ERRORCOND(0 && "Nested vmexit should be handled elsewhere");
	} else if (_vmx_guest_get_cpl(vcpu) > 0) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
	} else {
		if (!cpu_has_current_vmcs12(vcpu)) {
			/* Note: Currently does not support 1-setting of "VMCS shadowing" */
			_vmx_nested_vm_fail_invalid(vcpu);
		} else {
			ulong_t encoding;
			uintptr_t pvalue;
			int value_mem_reg;
			size_t size = _vmx_decode_vmread_vmwrite(vcpu, r, 1, &encoding,
													 &pvalue, &value_mem_reg);
			size_t offset = xmhf_nested_arch_x86vmx_vmcs_field_find(encoding);
#ifdef VMX_NESTED_USE_SHADOW_VMCS
			/* If using shadow VMCS, there should be no VMREAD exits */
			HALT_ON_ERRORCOND(!_vmx_hasctl_vmcs_shadowing(&vcpu->vmx_caps));
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
			if (offset == (size_t)(-1)) {
				_vmx_nested_vm_fail_valid
					(vcpu, VM_INST_ERRNO_VMRDWR_UNSUPP_VMCS_COMP);
			} else {
				/* Note: Currently does not support VMCS shadowing */
				vmcs12_info_t *vmcs12_info;
				ulong_t value;
				vmcs12_info = xmhf_nested_arch_x86vmx_find_current_vmcs12(vcpu);
				value = xmhf_nested_arch_x86vmx_vmcs_read
					(&vmcs12_info->vmcs12_value, offset, size);
				if (value_mem_reg) {
					memcpy((void *)pvalue, &value, size);
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

void xmhf_nested_arch_x86vmx_handle_vmwrite(VCPU * vcpu, struct regs *r)
{
	if (_vmx_nested_check_ud(vcpu, 0)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		/* Note: Currently does not support 1-setting of "VMCS shadowing" */
		/*
		 * Guest hypervisor is likely performing nested virtualization.
		 * This case should be handled in
		 * xmhf_parteventhub_arch_x86vmx_intercept_handler(). So panic if we
		 * end up here.
		 */
		HALT_ON_ERRORCOND(0 && "Nested vmexit should be handled elsewhere");
	} else if (_vmx_guest_get_cpl(vcpu) > 0) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
	} else {
		if (!cpu_has_current_vmcs12(vcpu)) {
			/* Note: Currently does not support 1-setting of "VMCS shadowing" */
			_vmx_nested_vm_fail_invalid(vcpu);
		} else {
			ulong_t encoding;
			uintptr_t pvalue;
			int value_mem_reg;
			size_t size = _vmx_decode_vmread_vmwrite(vcpu, r, 1, &encoding,
													 &pvalue, &value_mem_reg);
			size_t offset = xmhf_nested_arch_x86vmx_vmcs_field_find(encoding);
#ifdef VMX_NESTED_USE_SHADOW_VMCS
			/* If using shadow VMCS, there should be no VMWRITE exits */
			HALT_ON_ERRORCOND(!_vmx_hasctl_vmcs_shadowing(&vcpu->vmx_caps));
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
			if (offset == (size_t)(-1)) {
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
				ulong_t value = 0;
				vmcs12_info_t *vmcs12_info;
				vmcs12_info = xmhf_nested_arch_x86vmx_find_current_vmcs12(vcpu);
				if (value_mem_reg) {
					memcpy(&value, (void *)pvalue, size);
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

void xmhf_nested_arch_x86vmx_handle_vmxoff(VCPU * vcpu, struct regs *r)
{
	(void)r;
	if (_vmx_nested_check_ud(vcpu, 0)) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		/*
		 * Guest hypervisor is likely performing nested virtualization.
		 * This case should be handled in
		 * xmhf_parteventhub_arch_x86vmx_intercept_handler(). So panic if we
		 * end up here.
		 */
		HALT_ON_ERRORCOND(0 && "Nested vmexit should be handled elsewhere");
	} else if (_vmx_guest_get_cpl(vcpu) > 0) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
	} else {
		/* Note: ignoring all logic related to SMI, SMM, SMX */
		vcpu->vmx_nested_is_vmx_operation = 0;
		vcpu->vmx_nested_vmxon_pointer = 0;
		vcpu->vmx_nested_is_vmx_root_operation = 0;
		vcpu->vmx_nested_cur_vmcs12 = INVALID_VMCS12_INDEX;
#ifdef VMX_NESTED_USE_SHADOW_VMCS
		if (_vmx_hasctl_vmcs_shadowing(&vcpu->vmx_caps)) {
			vcpu->vmcs.guest_VMCS_link_pointer = CUR_VMCS_PTR_INVALID;

			/*
			 * Disable VMCS shadowing in VMC01. This is required, otherwise
			 * when the guest executes VMREAD / VMWRITE, VMfailInvalid is seen
			 * instead of #UD.
			 */
			vcpu->vmcs.control_VMX_seccpu_based &=
				~(1U << VMX_SECPROCBASED_VMCS_SHADOWING);
		}
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
		_vmx_nested_vm_succeed(vcpu);
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	}
}

void xmhf_nested_arch_x86vmx_handle_vmxon(VCPU * vcpu, struct regs *r)
{
#ifdef __DEBUG_QEMU__
	{
		static bool tested = false;
		if (vcpu->isbsp && !tested) {
			xmhf_nested_arch_x86vmx_check_fields_existence(vcpu);
			tested = true;
		}
	}
#endif							/* !__DEBUG_QEMU__ */
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
			guestmem_copy_gv2h(&ctx_pair, 0, &vmxon_ptr, addr,
							   sizeof(vmxon_ptr));
			if (!PA_PAGE_ALIGNED_4K(vmxon_ptr)
				|| !_vmx_check_physical_addr_width(vcpu, vmxon_ptr)) {
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
					vcpu->vmx_nested_cur_vmcs12 = INVALID_VMCS12_INDEX;
#ifdef VMX_NESTED_USE_SHADOW_VMCS
					if (_vmx_hasctl_vmcs_shadowing(&vcpu->vmx_caps)) {
						vcpu->vmcs.guest_VMCS_link_pointer =
							CUR_VMCS_PTR_INVALID;

						/* Enable VMCS shadowing in VMC01 */
						vcpu->vmcs.control_VMX_seccpu_based |=
							(1U << VMX_SECPROCBASED_VMCS_SHADOWING);

						/* Write VMREAD / VMWRITE bitmap */
						__vmx_vmwrite64(VMCSENC_control_VMREAD_bitmap_address,
										hva2spa(blank_page));
						__vmx_vmwrite64(VMCSENC_control_VMWRITE_bitmap_address,
										hva2spa(blank_page));
					}
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
					active_vmcs12_array_init(vcpu);
					_vmx_nested_vm_succeed(vcpu);
				}
			}
			vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
		}
	} else if (!vcpu->vmx_nested_is_vmx_root_operation) {
		/*
		 * Guest hypervisor is likely performing nested virtualization.
		 * This case should be handled in
		 * xmhf_parteventhub_arch_x86vmx_intercept_handler(). So panic if we
		 * end up here.
		 */
		HALT_ON_ERRORCOND(0 && "Nested vmexit should be handled elsewhere");
	} else if (_vmx_guest_get_cpl(vcpu) > 0) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
	} else {
		_vmx_nested_vm_fail(vcpu, VM_INST_ERRNO_VMXON_IN_VMXROOT);
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	}
}
