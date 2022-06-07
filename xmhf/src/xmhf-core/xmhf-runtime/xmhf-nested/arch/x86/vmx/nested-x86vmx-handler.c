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
	guestmem_hptw_ctx_pair_t ctx_pair;
	guestmem_init(vcpu, &ctx_pair);
	/* TODO: Check settings of VMX controls and host-state area */

	/* Translate VMCS12 to VMCS02 */
	HALT_ON_ERRORCOND(__vmx_vmptrld(vmcs12_info->vmcs02_ptr));

	/* Start VMCS translation */

	/* 16-Bit Control Fields */
	// Note: VIRTUAL PROCESSOR IDENTIFIERS (VPIDS) not supported yet
	// Need to multiplex vmcs12_info->vmcs12_value.control_vpid
	if (_vmx_has_enable_vpid(vcpu)) {
		u16 control_vpid = vmcs12_info->vmcs12_value.control_vpid;
		control_vpid = 0;
		__vmx_vmwrite16(0x0000, control_vpid);
	}
	if (_vmx_has_process_posted_interrupts(vcpu)) {
		__vmx_vmwrite16(0x0002,
			vmcs12_info->vmcs12_value.control_post_interrupt_notification_vec);
	}
	if (_vmx_has_ept_violation_ve(vcpu)) {
		__vmx_vmwrite16(0x0004, vmcs12_info->vmcs12_value.control_eptp_index);
	}

	/* 16-Bit Guest-State Fields */
	__vmx_vmwrite16(0x0800, vmcs12_info->vmcs12_value.guest_ES_selector);
	__vmx_vmwrite16(0x0802, vmcs12_info->vmcs12_value.guest_CS_selector);
	__vmx_vmwrite16(0x0804, vmcs12_info->vmcs12_value.guest_SS_selector);
	__vmx_vmwrite16(0x0806, vmcs12_info->vmcs12_value.guest_DS_selector);
	__vmx_vmwrite16(0x0808, vmcs12_info->vmcs12_value.guest_FS_selector);
	__vmx_vmwrite16(0x080A, vmcs12_info->vmcs12_value.guest_GS_selector);
	__vmx_vmwrite16(0x080C, vmcs12_info->vmcs12_value.guest_LDTR_selector);
	__vmx_vmwrite16(0x080E, vmcs12_info->vmcs12_value.guest_TR_selector);
	if (_vmx_has_virtual_interrupt_delivery(vcpu)) {
		__vmx_vmwrite16(0x0810,
			vmcs12_info->vmcs12_value.guest_interrupt_status);
	}
	if (_vmx_has_enable_pml(vcpu)) {
		__vmx_vmwrite16(0x0812, vmcs12_info->vmcs12_value.guest_PML_index);
	}

	/* 16-Bit Host-State Fields */
	__vmx_vmwrite16(0x0C00, vcpu->vmcs.host_ES_selector);
	__vmx_vmwrite16(0x0C02, vcpu->vmcs.host_CS_selector);
	__vmx_vmwrite16(0x0C04, vcpu->vmcs.host_SS_selector);
	__vmx_vmwrite16(0x0C06, vcpu->vmcs.host_DS_selector);
	__vmx_vmwrite16(0x0C08, vcpu->vmcs.host_FS_selector);
	__vmx_vmwrite16(0x0C0A, vcpu->vmcs.host_GS_selector);
	__vmx_vmwrite16(0x0C0C, vcpu->vmcs.host_TR_selector);

	/* 64-Bit Control Fields */
	{
		gpa_t addr = vmcs12_info->vmcs12_value.control_IO_BitmapA_address;
		__vmx_vmwrite64(0x2000, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	{
		gpa_t addr = vmcs12_info->vmcs12_value.control_IO_BitmapB_address;
		__vmx_vmwrite64(0x2002, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_has_use_msr_bitmaps(vcpu)) {
		gpa_t addr = vmcs12_info->vmcs12_value.control_MSR_Bitmaps_address;
		__vmx_vmwrite64(0x2004, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	{
		gpa_t addr = vmcs12_info->vmcs12_value.control_VM_exit_MSR_store_address;
		// TODO: need to multiplex MSR loading / storing, which is not implemented yet.
		addr = guestmem_gpa2spa_page(&ctx_pair, 0);
		__vmx_vmwrite64(0x2006, addr);
	}
	{
		gpa_t addr = vmcs12_info->vmcs12_value.control_VM_exit_MSR_load_address;
		// TODO: need to multiplex MSR loading / storing, which is not implemented yet.
		addr = guestmem_gpa2spa_page(&ctx_pair, 0);
		__vmx_vmwrite64(0x2008, addr);
	}
	{
		gpa_t addr = vmcs12_info->vmcs12_value.control_VM_entry_MSR_load_address;
		// TODO: need to multiplex MSR loading / storing, which is not implemented yet.
		addr = guestmem_gpa2spa_page(&ctx_pair, 0);
		__vmx_vmwrite64(0x200A, addr);
	}
	{
		gpa_t addr = vmcs12_info->vmcs12_value.control_Executive_VMCS_pointer;
		// TODO: related to SMM, check whether this restriction makes sense
		HALT_ON_ERRORCOND(addr == 0);
		// TODO: this should be considered KVM bug
#ifndef __DEBUG_QEMU__
		__vmx_vmwrite64(0x200C, guestmem_gpa2spa_page(&ctx_pair, addr));
#endif /* !__DEBUG_QEMU__ */
	}
	if (_vmx_has_enable_pml(vcpu)) {
		gpa_t addr = vmcs12_info->vmcs12_value.control_PML_address;
		__vmx_vmwrite64(0x200E, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	{
		__vmx_vmwrite64(0x2010, vmcs12_info->vmcs12_value.control_TSC_offset);
	}
	if (_vmx_has_virtualize_apic_access(vcpu)) {
		gpa_t addr = vmcs12_info->vmcs12_value.control_virtual_APIC_address;
		__vmx_vmwrite64(0x2012, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_has_process_posted_interrupts(vcpu)) {
		gpa_t addr = vmcs12_info->vmcs12_value.control_APIC_access_address;
		__vmx_vmwrite64(0x2014, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_has_process_posted_interrupts(vcpu)) {
		gpa_t addr = vmcs12_info->vmcs12_value.control_posted_interrupt_desc_address;
		__vmx_vmwrite64(0x2016, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_has_enable_vm_functions(vcpu)) {
		gpa_t addr = vmcs12_info->vmcs12_value.control_VM_function_controls;
		__vmx_vmwrite64(0x2018, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_has_enable_ept(vcpu)) {
		// Note: "Enable EPT" not supported for the guest, but XMHF needs EPT.
		gpa_t addr = vmcs12_info->vmcs12_value.control_EPT_pointer;
		// TODO: to support EPT for guest, need to sanitize the entier EPT
		HALT_ON_ERRORCOND(addr == 0);
		addr = guestmem_gpa2spa_page(&ctx_pair, addr);
		addr = vcpu->vmcs.control_EPT_pointer;
		__vmx_vmwrite64(0x201A, addr);
	}
	if (_vmx_has_virtual_interrupt_delivery(vcpu)) {
		__vmx_vmwrite64(0x201C, vmcs12_info->vmcs12_value.control_EOI_exit_bitmap_0);
		__vmx_vmwrite64(0x201E, vmcs12_info->vmcs12_value.control_EOI_exit_bitmap_1);
		__vmx_vmwrite64(0x2020, vmcs12_info->vmcs12_value.control_EOI_exit_bitmap_2);
		__vmx_vmwrite64(0x2022, vmcs12_info->vmcs12_value.control_EOI_exit_bitmap_3);
	}
	if (0) {
		// Note: EPTP Switching not supported
		gpa_t addr = vmcs12_info->vmcs12_value.control_EPTP_list_address;
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(addr == 0);
		__vmx_vmwrite64(0x2024, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_has_vmcs_shadowing(vcpu)) {
		gpa_t addr;
		addr = vmcs12_info->vmcs12_value.control_VMREAD_bitmap_address;
		__vmx_vmwrite64(0x2026, guestmem_gpa2spa_page(&ctx_pair, addr));
		addr = vmcs12_info->vmcs12_value.control_VMWRITE_bitmap_address;
		__vmx_vmwrite64(0x2028, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_has_ept_violation_ve(vcpu)) {
		gpa_t addr = vmcs12_info->vmcs12_value.control_virt_exception_info_address;
		__vmx_vmwrite64(0x202A, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_has_enable_xsaves_xrstors(vcpu)) {
		__vmx_vmwrite64(0x202C, vmcs12_info->vmcs12_value.control_XSS_exiting_bitmap);
	}
	if (_vmx_has_enable_encls_exiting(vcpu)) {
		__vmx_vmwrite64(0x202E, vmcs12_info->vmcs12_value.control_ENCLS_exiting_bitmap);
	}
	if (_vmx_has_sub_page_write_permissions_for_ept(vcpu)) {
		// Note: Sub-page write permissions for EPT
		gpa_t addr = vmcs12_info->vmcs12_value.control_subpage_permission_table_pointer;
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(addr == 0);
		__vmx_vmwrite64(0x2030, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_has_use_tsc_scaling(vcpu)) {
		__vmx_vmwrite64(0x2032, vmcs12_info->vmcs12_value.control_TSC_multiplier);
	}
	if (_vmx_has_activate_tertiary_controls(vcpu)) {
		// Note: Activate tertiary controls not supported
		u64 val = vmcs12_info->vmcs12_value.control_tertiary_proc_based_VMexec_ctls;
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(val == 0);
		__vmx_vmwrite64(0x2034, val);
	}
	if (_vmx_has_enable_enclv_exiting(vcpu)) {
		__vmx_vmwrite64(0x2036, vmcs12_info->vmcs12_value.control_ENCLV_exiting_bitmap);
	}

	/* 64-Bit Read-Only Data Field: skipped */

	/* 64-Bit Guest-State Fields */
	__vmx_vmwrite64(0x2800, vmcs12_info->vmcs12_value.guest_VMCS_link_pointer);
	__vmx_vmwrite64(0x2802, vmcs12_info->vmcs12_value.guest_IA32_DEBUGCTL);
	if (_vmx_has_vmexit_save_ia32_pat(vcpu) ||
		_vmx_has_vmentry_load_ia32_pat(vcpu)) {
		__vmx_vmwrite64(0x2804, vmcs12_info->vmcs12_value.guest_IA32_PAT);
	}
	if (_vmx_has_vmexit_save_ia32_efer(vcpu) ||
		_vmx_has_vmentry_load_ia32_efer(vcpu)) {
		__vmx_vmwrite64(0x2806, vmcs12_info->vmcs12_value.guest_IA32_EFER);
	}
	if (_vmx_has_vmentry_load_ia32_perf_global_ctrl(vcpu)) {
		__vmx_vmwrite64(0x2808, vmcs12_info->vmcs12_value.guest_IA32_PERF_GLOBAL_CTRL);
	}
	if (_vmx_has_enable_ept(vcpu)) {
		__vmx_vmwrite64(0x280A, vmcs12_info->vmcs12_value.guest_PDPTE0);
		__vmx_vmwrite64(0x280C, vmcs12_info->vmcs12_value.guest_PDPTE1);
		__vmx_vmwrite64(0x280E, vmcs12_info->vmcs12_value.guest_PDPTE2);
		__vmx_vmwrite64(0x2810, vmcs12_info->vmcs12_value.guest_PDPTE3);
	}
	if (_vmx_has_vmexit_clear_ia32_bndcfgs(vcpu) || 
		_vmx_has_vmentry_load_ia32_bndcfgs(vcpu)) {
		__vmx_vmwrite64(0x2812, vmcs12_info->vmcs12_value.guest_IA32_BNDCFGS);
	}
	if (_vmx_has_vmexit_clear_ia32_rtit_ctl(vcpu) ||
		_vmx_has_vmentry_load_ia32_rtit_ctl(vcpu)) {
		__vmx_vmwrite64(0x2814, vmcs12_info->vmcs12_value.guest_IA32_RTIT_CTL);
	}
	if (_vmx_has_vmentry_load_pkrs(vcpu)) {
		__vmx_vmwrite64(0x2818, vmcs12_info->vmcs12_value.guest_IA32_PKRS);
	}

	/* 64-Bit Host-State Fields */
	/*
	 * Note: looks like XMHF does not care about these fields. So we treat
	 * these similar to guest state fields.
	 */
	if (_vmx_has_vmexit_load_ia32_pat(vcpu)) {
		__vmx_vmwrite64(0x2C00, rdmsr64(MSR_IA32_PAT));
	}
	if (_vmx_has_vmexit_load_ia32_efer(vcpu)) {
		__vmx_vmwrite64(0x2C02, rdmsr64(MSR_EFER));
	}
	if (_vmx_has_vmexit_load_ia32_perf_global_ctrl(vcpu)) {
		u32 eax, ebx, ecx, edx;
		cpuid(0x0, &eax, &ebx, &ecx, &edx);
		if (eax >= 0xA) {
			cpuid(0xA, &eax, &ebx, &ecx, &edx);
			if (eax & 0xffU) {
				__vmx_vmwrite64(0x2C04, rdmsr64(IA32_PERF_GLOBAL_CTRL));
			}
		}
	}
	if (_vmx_has_vmexit_load_pkrs(vcpu)) {
		__vmx_vmwrite64(0x2C06, rdmsr64(IA32_PKRS));
	}

	/* 32-Bit Control Fields */
	{
		u32 val = vmcs12_info->vmcs12_value.control_VMX_pin_based;
		u32 fixed0 = vcpu->vmx_nested_pinbased_ctls;
		u32 fixed1 = vcpu->vmx_nested_pinbased_ctls >> 32;
		HALT_ON_ERRORCOND((~val & fixed0) == 0 && (val & ~fixed1) == 0);
		__vmx_vmwrite32(0x4000, val);
	}
	{
		u32 val = vmcs12_info->vmcs12_value.control_VMX_cpu_based;
		u32 fixed0 = vcpu->vmx_nested_procbased_ctls;
		u32 fixed1 = vcpu->vmx_nested_procbased_ctls >> 32;
		HALT_ON_ERRORCOND((~val & fixed0) == 0 && (val & ~fixed1) == 0);
		__vmx_vmwrite32(0x4002, val);
	}
	{
		u32 val = vmcs12_info->vmcs12_value.control_exception_bitmap;
		// TODO: in the future, need to merge with host's exception bitmap
		__vmx_vmwrite32(0x4004, val);
	}
	{
		u32 val = vmcs12_info->vmcs12_value.control_pagefault_errorcode_mask;
		__vmx_vmwrite32(0x4006, val);
	}
	{
		u32 val = vmcs12_info->vmcs12_value.control_pagefault_errorcode_match;
		__vmx_vmwrite32(0x4008, val);
	}
	{
		u32 val = vmcs12_info->vmcs12_value.control_CR3_target_count;
		__vmx_vmwrite32(0x400A, val);
	}
	{
		u32 val = vmcs12_info->vmcs12_value.control_VM_exit_controls;
		u32 fixed0 = vcpu->vmx_nested_exit_ctls;
		u32 fixed1 = vcpu->vmx_nested_exit_ctls >> 32;
		HALT_ON_ERRORCOND((~val & fixed0) == 0 && (val & ~fixed1) == 0);
		__vmx_vmwrite32(0x400C, val);
	}
	{
		u32 val = vmcs12_info->vmcs12_value.control_VM_exit_MSR_store_count;
		/* VM exit/entry MSR load/store not supported */
		HALT_ON_ERRORCOND(val == 0);
		__vmx_vmwrite32(0x400E, val);
	}
	{
		u32 val = vmcs12_info->vmcs12_value.control_VM_exit_MSR_load_count;
		/* VM exit/entry MSR load/store not supported */
		HALT_ON_ERRORCOND(val == 0);
		__vmx_vmwrite32(0x4010, val);
	}
	{
		u32 val = vmcs12_info->vmcs12_value.control_VM_entry_controls;
		u32 fixed0 = vcpu->vmx_nested_entry_ctls;
		u32 fixed1 = vcpu->vmx_nested_entry_ctls >> 32;
		HALT_ON_ERRORCOND((~val & fixed0) == 0 && (val & ~fixed1) == 0);
		__vmx_vmwrite32(0x4012, val);
	}
	{
		u32 val = vmcs12_info->vmcs12_value.control_VM_entry_MSR_load_count;
		/* VM exit/entry MSR load/store not supported */
		HALT_ON_ERRORCOND(val == 0);
		__vmx_vmwrite32(0x4014, val);
	}
	{
		u32 val = vmcs12_info->vmcs12_value.control_VM_entry_interruption_information;
		__vmx_vmwrite32(0x4016, val);
	}
	{
		u32 val = vmcs12_info->vmcs12_value.control_VM_entry_exception_errorcode;
		__vmx_vmwrite32(0x4018, val);
	}
	{
		u32 val = vmcs12_info->vmcs12_value.control_VM_entry_instruction_length;
		__vmx_vmwrite32(0x401A, val);
	}
	if (_vmx_has_use_tpr_shadow(vcpu)) {
		u32 val = vmcs12_info->vmcs12_value.control_Task_PRivilege_Threshold;
		__vmx_vmwrite32(0x401C, val);
	}
	if (_vmx_has_activate_secondary_controls(vcpu)) {
		u32 val = vmcs12_info->vmcs12_value.control_VMX_seccpu_based;
		u32 fixed0 = vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR];
		u32 fixed1 = vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32;
		HALT_ON_ERRORCOND((~val & fixed0) == 0 && (val & ~fixed1) == 0);
		/* XMHF needs the guest to run unrestricted and in EPT */
		val |= VMX_SECPROCBASED_ENABLE_EPT;
		val |= VMX_SECPROCBASED_UNRESTRICTED_GUEST;
		__vmx_vmwrite32(0x401E, val);
	}
	if (_vmx_has_pause_loop_exiting(vcpu)) {
		u32 val;
		val = vmcs12_info->vmcs12_value.control_PLE_gap;
		__vmx_vmwrite32(0x4020, val);
		val = vmcs12_info->vmcs12_value.control_PLE_window;
		__vmx_vmwrite32(0x4022, val);
	}

	/* 32-Bit Read-Only Data Fields */

	/* 32-Bit Guest-State Fields */
	__vmx_vmwrite32(0x4800, vmcs12_info->vmcs12_value.guest_ES_limit);
	__vmx_vmwrite32(0x4802, vmcs12_info->vmcs12_value.guest_CS_limit);
	__vmx_vmwrite32(0x4804, vmcs12_info->vmcs12_value.guest_SS_limit);
	__vmx_vmwrite32(0x4806, vmcs12_info->vmcs12_value.guest_DS_limit);
	__vmx_vmwrite32(0x4808, vmcs12_info->vmcs12_value.guest_FS_limit);
	__vmx_vmwrite32(0x480A, vmcs12_info->vmcs12_value.guest_GS_limit);
	__vmx_vmwrite32(0x480C, vmcs12_info->vmcs12_value.guest_LDTR_limit);
	__vmx_vmwrite32(0x480E, vmcs12_info->vmcs12_value.guest_TR_limit);
	__vmx_vmwrite32(0x4810, vmcs12_info->vmcs12_value.guest_GDTR_limit);
	__vmx_vmwrite32(0x4812, vmcs12_info->vmcs12_value.guest_IDTR_limit);
	__vmx_vmwrite32(0x4814, vmcs12_info->vmcs12_value.guest_ES_access_rights);
	__vmx_vmwrite32(0x4816, vmcs12_info->vmcs12_value.guest_CS_access_rights);
	__vmx_vmwrite32(0x4818, vmcs12_info->vmcs12_value.guest_SS_access_rights);
	__vmx_vmwrite32(0x481A, vmcs12_info->vmcs12_value.guest_DS_access_rights);
	__vmx_vmwrite32(0x481C, vmcs12_info->vmcs12_value.guest_FS_access_rights);
	__vmx_vmwrite32(0x481E, vmcs12_info->vmcs12_value.guest_GS_access_rights);
	__vmx_vmwrite32(0x4820, vmcs12_info->vmcs12_value.guest_LDTR_access_rights);
	__vmx_vmwrite32(0x4822, vmcs12_info->vmcs12_value.guest_TR_access_rights);
	__vmx_vmwrite32(0x4824, vmcs12_info->vmcs12_value.guest_interruptibility);
	__vmx_vmwrite32(0x4826, vmcs12_info->vmcs12_value.guest_activity_state);
#ifndef __DEBUG_QEMU__
	__vmx_vmwrite32(0x4828, vmcs12_info->vmcs12_value.guest_SMBASE);
#endif /* !__DEBUG_QEMU__ */
	__vmx_vmwrite32(0x482A, vmcs12_info->vmcs12_value.guest_SYSENTER_CS);
	if (_vmx_has_activate_vmx_preemption_timer(vcpu)) {
		u32 val = vmcs12_info->vmcs12_value.guest_VMX_preemption_timer_value;
		__vmx_vmwrite32(0x482E, val);
	}

	/* 32-Bit Host-State Field */
	__vmx_vmwrite32(0x4C00, vcpu->vmcs.host_SYSENTER_CS);

	/* Natural-Width Control Fields */
	{
		__vmx_vmwriteNW(0x6000, vmcs12_info->vmcs12_value.control_CR0_mask);
		__vmx_vmwriteNW(0x6002, vmcs12_info->vmcs12_value.control_CR4_mask);
		__vmx_vmwriteNW(0x6004, vmcs12_info->vmcs12_value.control_CR0_shadow);
		__vmx_vmwriteNW(0x6006, vmcs12_info->vmcs12_value.control_CR4_shadow);
#ifndef __DEBUG_QEMU__
		__vmx_vmwriteNW(0x6008, vmcs12_info->vmcs12_value.control_CR3_target0);
		__vmx_vmwriteNW(0x600A, vmcs12_info->vmcs12_value.control_CR3_target1);
		__vmx_vmwriteNW(0x600C, vmcs12_info->vmcs12_value.control_CR3_target2);
		__vmx_vmwriteNW(0x600E, vmcs12_info->vmcs12_value.control_CR3_target3);
#endif /* !__DEBUG_QEMU__ */
	}

	/* Natural-Width Read-Only Data Fields */

	/* Natural-Width Guest-State Fields */
	__vmx_vmwriteNW(0x6800, vmcs12_info->vmcs12_value.guest_CR0);
	__vmx_vmwriteNW(0x6802, vmcs12_info->vmcs12_value.guest_CR3);
	__vmx_vmwriteNW(0x6804, vmcs12_info->vmcs12_value.guest_CR4);
	__vmx_vmwriteNW(0x6806, vmcs12_info->vmcs12_value.guest_ES_base);
	__vmx_vmwriteNW(0x6808, vmcs12_info->vmcs12_value.guest_CS_base);
	__vmx_vmwriteNW(0x680A, vmcs12_info->vmcs12_value.guest_SS_base);
	__vmx_vmwriteNW(0x680C, vmcs12_info->vmcs12_value.guest_DS_base);
	__vmx_vmwriteNW(0x680E, vmcs12_info->vmcs12_value.guest_FS_base);
	__vmx_vmwriteNW(0x6810, vmcs12_info->vmcs12_value.guest_GS_base);
	__vmx_vmwriteNW(0x6812, vmcs12_info->vmcs12_value.guest_LDTR_base);
	__vmx_vmwriteNW(0x6814, vmcs12_info->vmcs12_value.guest_TR_base);
	__vmx_vmwriteNW(0x6816, vmcs12_info->vmcs12_value.guest_GDTR_base);
	__vmx_vmwriteNW(0x6818, vmcs12_info->vmcs12_value.guest_IDTR_base);
	__vmx_vmwriteNW(0x681A, vmcs12_info->vmcs12_value.guest_DR7);
	__vmx_vmwriteNW(0x681C, vmcs12_info->vmcs12_value.guest_RSP);
	__vmx_vmwriteNW(0x681E, vmcs12_info->vmcs12_value.guest_RIP);
	__vmx_vmwriteNW(0x6820, vmcs12_info->vmcs12_value.guest_RFLAGS);
	__vmx_vmwriteNW(0x6822, vmcs12_info->vmcs12_value.guest_pending_debug_x);
	__vmx_vmwriteNW(0x6824, vmcs12_info->vmcs12_value.guest_SYSENTER_ESP);
	__vmx_vmwriteNW(0x6826, vmcs12_info->vmcs12_value.guest_SYSENTER_EIP);
	if (_vmx_has_vmentry_load_cet_state(vcpu)) {
		__vmx_vmwriteNW(0x6828, vmcs12_info->vmcs12_value.guest_IA32_S_CET);
		__vmx_vmwriteNW(0x682A, vmcs12_info->vmcs12_value.guest_SSP);
		__vmx_vmwriteNW(0x682C,
			vmcs12_info->vmcs12_value.guest_IA32_INTERRUPT_SSP_TABLE_ADDR);
	}

	/* Natural-Width Host-State Fields */
	__vmx_vmwriteNW(0x6C00, vcpu->vmcs.host_CR0);
	__vmx_vmwriteNW(0x6C02, vcpu->vmcs.host_CR3);
	__vmx_vmwriteNW(0x6C04, vcpu->vmcs.host_CR4);
	__vmx_vmwriteNW(0x6C06, vcpu->vmcs.host_FS_base);
	__vmx_vmwriteNW(0x6C08, vcpu->vmcs.host_GS_base);
	__vmx_vmwriteNW(0x6C0A, vcpu->vmcs.host_TR_base);
	__vmx_vmwriteNW(0x6C0C, vcpu->vmcs.host_GDTR_base);
	__vmx_vmwriteNW(0x6C0E, vcpu->vmcs.host_IDTR_base);
	__vmx_vmwriteNW(0x6C10, vcpu->vmcs.host_SYSENTER_ESP);
	__vmx_vmwriteNW(0x6C12, vcpu->vmcs.host_SYSENTER_EIP);
	__vmx_vmwriteNW(0x6C14, vcpu->vmcs.host_RSP);
	__vmx_vmwriteNW(0x6C16, vcpu->vmcs.host_RIP);
	if (_vmx_has_vmexit_load_cet_state(vcpu)) {
		/*
		 * Currently VMX_VMEXIT_LOAD_CET_STATE is disabled for the guest.
		 * To implement load CET state correctly, need to modify:
		 * * encoding 0x6C18: host_IA32_S_CET
		 * * encoding 0x6C1A: host_SSP
		 * * encoding 0x6C1C: host_IA32_INTERRUPT_SSP_TABLE_ADDR
		*/
	}

	// TODO: for host-state fields, update vmcs of guest hv.

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

	/* End VMCS translation */

	vcpu->vmx_nested_is_vmx_root_operation = 0;

	if (vmcs12_info->launched) {
		__vmx_vmentry_vmresume(r);
	} else {
		vmcs12_info->launched = 1;
		__vmx_vmentry_vmlaunch(r);
	}

	/* When a problem happens, translate back to L1 guest */
	HALT_ON_ERRORCOND(__vmx_vmptrld(hva2spa((void*)vcpu->vmx_vmcs_vaddr)));
	HALT_ON_ERRORCOND(0 && "TODO frontier");
	// TODO
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

