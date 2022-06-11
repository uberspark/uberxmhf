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

// nested-x86vmx-vmcs12.c
// Handle VMCS in the guest
// author: Eric Li (xiaoyili@andrew.cmu.edu)
#include <xmhf.h>
#include "nested-x86vmx-vmcs12.h"
#include "nested-x86vmx-vminsterr.h"

/*
 * Given a VMCS field encoding (used in VMREAD and VMWRITE)
 * Return index of the field in struct nested_vmcs12
 * Return (size_t)(-1) when not found
 */
size_t xmhf_nested_arch_x86vmx_vmcs_field_find(ulong_t encoding)
{
	switch (encoding) {
#define DECLARE_FIELD_16(encoding, name, ...) \
		case encoding: return offsetof(struct nested_vmcs12, name);
#define DECLARE_FIELD_64(encoding, name, ...) \
		case encoding: return offsetof(struct nested_vmcs12, name); \
		case encoding + 1: return offsetof(struct nested_vmcs12, name) + 4;
#define DECLARE_FIELD_32(encoding, name, ...) \
		DECLARE_FIELD_16(encoding, name)
#define DECLARE_FIELD_NW(encoding, name, ...) \
		DECLARE_FIELD_16(encoding, name)
#include "nested-x86vmx-vmcs12-fields.h"
	default:
		printf("Warning: unknown encoding requested: 0x%04lx\n", encoding);
		return (size_t)(-1);
	}
}

int xmhf_nested_arch_x86vmx_vmcs_writable(size_t offset)
{
	switch (offset) {
#define DECLARE_FIELD_16_RO(encoding, name, ...) \
		case offsetof(struct nested_vmcs12, name): return 0;
#define DECLARE_FIELD_64_RO(encoding, name, ...) \
		case offsetof(struct nested_vmcs12, name): return 0; \
		case offsetof(struct nested_vmcs12, name) + 4: return 0;
#define DECLARE_FIELD_32_RO(encoding, name, ...) \
		DECLARE_FIELD_16_RO(encoding, name)
#define DECLARE_FIELD_NW_RO(encoding, name, ...) \
		DECLARE_FIELD_16_RO(encoding, name)
#define DECLARE_FIELD_16_RW(encoding, name, ...) \
		case offsetof(struct nested_vmcs12, name): return 1;
#define DECLARE_FIELD_64_RW(encoding, name, ...) \
		case offsetof(struct nested_vmcs12, name): return 1; \
		case offsetof(struct nested_vmcs12, name) + 4: return 1;
#define DECLARE_FIELD_32_RW(encoding, name, ...) \
		DECLARE_FIELD_16_RW(encoding, name)
#define DECLARE_FIELD_NW_RW(encoding, name, ...) \
		DECLARE_FIELD_16_RW(encoding, name)
#include "nested-x86vmx-vmcs12-fields.h"
	default:
		HALT_ON_ERRORCOND(0 && "Unknown guest VMCS field");
		return -1;
	}
}

ulong_t xmhf_nested_arch_x86vmx_vmcs_read(struct nested_vmcs12 *vmcs12,
											size_t offset, size_t size)
{
	switch (offset) {
#define DECLARE_FIELD_16(encoding, name, ...) \
	case offsetof(struct nested_vmcs12, name): \
		HALT_ON_ERRORCOND(size >= sizeof(u16)); \
		return (ulong_t) vmcs12->name;
#define DECLARE_FIELD_64(encoding, name, ...) \
	case offsetof(struct nested_vmcs12, name): \
		if (size == sizeof(u64)) { \
			return (ulong_t) vmcs12->name; \
		} else { \
			HALT_ON_ERRORCOND(size == sizeof(u32)); \
			return (ulong_t) *(u32 *)(void *)&vmcs12->name; \
		} \
	case offsetof(struct nested_vmcs12, name) + 4: \
		HALT_ON_ERRORCOND(size == sizeof(u32)); \
		return (ulong_t) ((u32 *)(void *)&vmcs12->name)[1];
#define DECLARE_FIELD_32(encoding, name, ...) \
	case offsetof(struct nested_vmcs12, name): \
		HALT_ON_ERRORCOND(size >= sizeof(u32)); \
		return (ulong_t) vmcs12->name;
#define DECLARE_FIELD_NW(encoding, name, ...) \
	case offsetof(struct nested_vmcs12, name): \
		HALT_ON_ERRORCOND(size >= sizeof(ulong_t)); \
		return (ulong_t) vmcs12->name;
#include "nested-x86vmx-vmcs12-fields.h"
	default:
		HALT_ON_ERRORCOND(0 && "Unknown guest VMCS field");
	}
}

void xmhf_nested_arch_x86vmx_vmcs_write(struct nested_vmcs12 *vmcs12,
										size_t offset, ulong_t value,
										size_t size)
{
	switch (offset) {
#define DECLARE_FIELD_16_RO(encoding, name, ...) \
	case offsetof(struct nested_vmcs12, name): \
		HALT_ON_ERRORCOND(0 && "Write to read-only VMCS field"); \
		break;
#define DECLARE_FIELD_64_RO(encoding, name, ...) \
	case offsetof(struct nested_vmcs12, name): \
		HALT_ON_ERRORCOND(0 && "Write to read-only VMCS field"); \
		break; \
	case offsetof(struct nested_vmcs12, name) + 4: \
		HALT_ON_ERRORCOND(0 && "Write to read-only VMCS field"); \
		break;
#define DECLARE_FIELD_32_RO(encoding, name, ...) \
		DECLARE_FIELD_16_RO(encoding, name)
#define DECLARE_FIELD_NW_RO(encoding, name, ...) \
		DECLARE_FIELD_16_RO(encoding, name)
#define DECLARE_FIELD_16_RW(encoding, name, ...) \
	case offsetof(struct nested_vmcs12, name): \
		HALT_ON_ERRORCOND(size >= sizeof(u16)); \
		vmcs12->name = (u16) value; \
		break;
#define DECLARE_FIELD_64_RW(encoding, name, ...) \
	case offsetof(struct nested_vmcs12, name): \
		if (size == sizeof(u64)) { \
			vmcs12->name = (u64) value; \
		} else { \
			HALT_ON_ERRORCOND(size == sizeof(u32)); \
			*(u32 *)(void *)&vmcs12->name = (u32) value; \
		} \
		break; \
	case offsetof(struct nested_vmcs12, name) + 4: \
		HALT_ON_ERRORCOND(size == sizeof(u32)); \
		((u32 *)(void *)&vmcs12->name)[1] = (u32) value; \
		break;
#define DECLARE_FIELD_32_RW(encoding, name, ...) \
	case offsetof(struct nested_vmcs12, name): \
		HALT_ON_ERRORCOND(size >= sizeof(u32)); \
		vmcs12->name = (u32) value; \
		break;
#define DECLARE_FIELD_NW_RW(encoding, name, ...) \
	case offsetof(struct nested_vmcs12, name): \
		HALT_ON_ERRORCOND(size >= sizeof(ulong_t)); \
		vmcs12->name = (ulong_t) value; \
		break;
#include "nested-x86vmx-vmcs12-fields.h"
	default:
		HALT_ON_ERRORCOND(0 && "Unknown guest VMCS field");
	}
}

/* Dump all fields in vmcs12 */
void xmhf_nested_arch_x86vmx_vmcs_dump(VCPU *vcpu, struct nested_vmcs12 *vmcs12,
										char *prefix)
{
#define DECLARE_FIELD_16(encoding, name, ...) \
	printf("CPU(0x%02x): %s" #name " = 0x%04x\n", vcpu->id, prefix, \
			(u32) vmcs12->name);
#define DECLARE_FIELD_64(encoding, name, ...) \
	printf("CPU(0x%02x): %s" #name " = 0x%016llx\n", vcpu->id, prefix, \
			vmcs12->name);
#define DECLARE_FIELD_32(encoding, name, ...) \
	printf("CPU(0x%02x): %s" #name " = 0x%08x\n", vcpu->id, prefix, \
			vmcs12->name);
#ifdef __AMD64__
#define DECLARE_FIELD_NW(encoding, name, ...) \
	printf("CPU(0x%02x): %s" #name " = 0x%016lx\n", vcpu->id, prefix, \
			vmcs12->name);
#elif defined(__I386__)
#define DECLARE_FIELD_NW(encoding, name, ...) \
	printf("CPU(0x%02x): %s" #name " = 0x%08lx\n", vcpu->id, prefix, \
			vmcs12->name);
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
#include "nested-x86vmx-vmcs12-fields.h"
}

/* Dump all fields in current physical VMCS (using vmread) */
void xmhf_nested_arch_x86vmx_vmread_all(VCPU *vcpu, char *prefix)
{
#define DECLARE_FIELD_16(encoding, name, ...) \
	{ \
		unsigned long value; \
		if (__vmx_vmread(encoding, &value)) { \
			printf("CPU(0x%02x): (0x%04x) %s" #name " = 0x%04lx\n", \
					vcpu->id, (u32) encoding, prefix, value); \
		} else { \
			printf("CPU(0x%02x): (0x%04x) %s" #name " = unavailable\n", \
					vcpu->id, (u32) encoding, prefix); \
		} \
	}
#ifdef __AMD64__
#define DECLARE_FIELD_64(encoding, name, ...) \
	{ \
		unsigned long value; \
		if (__vmx_vmread(encoding, &value)) { \
			printf("CPU(0x%02x): (0x%04x) %s" #name " = 0x%016lx\n", \
					vcpu->id, (u32) encoding, prefix, value); \
		} else { \
			printf("CPU(0x%02x): (0x%04x) %s" #name " = unavailable\n", \
					vcpu->id, (u32) encoding, prefix); \
		} \
	}
#elif defined(__I386__)
#define DECLARE_FIELD_64(encoding, name, ...) \
	{ \
		unsigned long value0, value1; \
		if (__vmx_vmread(encoding, &value0) && \
			__vmx_vmread(encoding + 1, &value1)) { \
			printf("CPU(0x%02x): (0x%04x) %s" #name " = 0x%08lx%08lx\n", \
					vcpu->id, (u32) encoding, prefix, value1, value0); \
		} else { \
			printf("CPU(0x%02x): (0x%04x) %s" #name " = unavailable\n", \
					vcpu->id, (u32) encoding, prefix); \
		} \
	}
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
#define DECLARE_FIELD_32(encoding, name, ...) \
	{ \
		unsigned long value; \
		if (__vmx_vmread(encoding, &value)) { \
			printf("CPU(0x%02x): (0x%04x) %s" #name " = 0x%08lx\n", \
					vcpu->id, (u32) encoding, prefix, value); \
		} else { \
			printf("CPU(0x%02x): (0x%04x) %s" #name " = unavailable\n", \
					vcpu->id, (u32) encoding, prefix); \
		} \
	}
#ifdef __AMD64__
#define DECLARE_FIELD_NW(encoding, name, ...) \
	{ \
		unsigned long value; \
		if (__vmx_vmread(encoding, &value)) { \
			printf("CPU(0x%02x): (0x%04x) %s" #name " = 0x%016lx\n", \
					vcpu->id, (u32) encoding, prefix, value); \
		} else { \
			printf("CPU(0x%02x): (0x%04x) %s" #name " = unavailable\n", \
					vcpu->id, (u32) encoding, prefix); \
		} \
	}
#elif defined(__I386__)
#define DECLARE_FIELD_NW(encoding, name, ...) \
	{ \
		unsigned long value; \
		if (__vmx_vmread(encoding, &value)) { \
			printf("CPU(0x%02x): (0x%04x) %s" #name " = 0x%08lx\n", \
					vcpu->id, (u32) encoding, prefix, value); \
		} else { \
			printf("CPU(0x%02x): (0x%04x) %s" #name " = unavailable\n", \
					vcpu->id, (u32) encoding, prefix); \
		} \
	}
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
#include "nested-x86vmx-vmcs12-fields.h"
}

/*
 * Extract ctls information to ctls from selected fields in VMCS12.
 * Return an error code following VM instruction error number, or 0 when
 * success.
 */
static u32 _vmcs12_get_ctls(VCPU *vcpu, struct nested_vmcs12 *vmcs12,
							vmx_ctls_t *ctls)
{
	{
		u32 val = vmcs12->control_VMX_pin_based;
		u32 fixed0 = vcpu->vmx_nested_pinbased_ctls;
		u32 fixed1 = vcpu->vmx_nested_pinbased_ctls >> 32;
		if (!((~val & fixed0) == 0 && (val & ~fixed1) == 0)) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		ctls->pinbased_ctls = val;
	}
	{
		u32 val = vmcs12->control_VMX_cpu_based;
		u32 fixed0 = vcpu->vmx_nested_procbased_ctls;
		u32 fixed1 = vcpu->vmx_nested_procbased_ctls >> 32;
		if (!((~val & fixed0) == 0 && (val & ~fixed1) == 0)) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		ctls->procbased_ctls = val;
	}
	{
		u32 val = vmcs12->control_VM_exit_controls;
		u32 fixed0 = vcpu->vmx_nested_exit_ctls;
		u32 fixed1 = vcpu->vmx_nested_exit_ctls >> 32;
		if (!((~val & fixed0) == 0 && (val & ~fixed1) == 0)) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		ctls->exit_ctls = val;
	}
	{
		u32 val = vmcs12->control_VM_entry_controls;
		u32 fixed0 = vcpu->vmx_nested_entry_ctls;
		u32 fixed1 = vcpu->vmx_nested_entry_ctls >> 32;
		if (!((~val & fixed0) == 0 && (val & ~fixed1) == 0)) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		ctls->entry_ctls = val;
	}
	{
		u32 val = 0;
		u32 fixed0 = vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR];
		u32 fixed1 = vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32;
		/* Check whether guest enables secondary controls */
		if (_vmx_hasctl_activate_secondary_controls(ctls)) {
			val = vmcs12->control_VMX_seccpu_based;
		}
		if (!((~val & fixed0) == 0 && (val & ~fixed1) == 0)) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		ctls->procbased_ctls2 = val;
	}
	return 0;
}

/*
 * Translate VMCS12 (vmcs12) to VMCS02 (already loaded as current VMCS).
 * Return an error code following VM instruction error number, or 0 when
 * success.
 */
u32 xmhf_nested_arch_x86vmx_vmcs12_to_vmcs02(VCPU *vcpu,
											struct nested_vmcs12 *vmcs12)
{
	vmx_ctls_t ctls;
	guestmem_hptw_ctx_pair_t ctx_pair;
	u32 status = _vmcs12_get_ctls(vcpu, vmcs12, &ctls);
	guestmem_init(vcpu, &ctx_pair);
	if (status != 0) {
		return status;
	}
	/* TODO: Check settings of VMX controls and host-state area */

	/* 16-Bit Control Fields */
	if (_vmx_hasctl_enable_vpid(&ctls)) {
		u16 control_vpid = vmcs12->control_vpid;
		// Note: VIRTUAL PROCESSOR IDENTIFIERS (VPIDS) not supported yet
		// Need to multiplex vmcs12->control_vpid
		control_vpid = 0;
		__vmx_vmwrite16(0x0000, control_vpid);
	}
	if (_vmx_hasctl_process_posted_interrupts(&ctls)) {
		__vmx_vmwrite16(0x0002,
			vmcs12->control_post_interrupt_notification_vec);
	}
	if (_vmx_hasctl_ept_violation_ve(&ctls)) {
		__vmx_vmwrite16(0x0004, vmcs12->control_eptp_index);
	}

	/* 16-Bit Guest-State Fields */
	__vmx_vmwrite16(0x0800, vmcs12->guest_ES_selector);
	__vmx_vmwrite16(0x0802, vmcs12->guest_CS_selector);
	__vmx_vmwrite16(0x0804, vmcs12->guest_SS_selector);
	__vmx_vmwrite16(0x0806, vmcs12->guest_DS_selector);
	__vmx_vmwrite16(0x0808, vmcs12->guest_FS_selector);
	__vmx_vmwrite16(0x080A, vmcs12->guest_GS_selector);
	__vmx_vmwrite16(0x080C, vmcs12->guest_LDTR_selector);
	__vmx_vmwrite16(0x080E, vmcs12->guest_TR_selector);
	if (_vmx_hasctl_virtual_interrupt_delivery(&ctls)) {
		__vmx_vmwrite16(0x0810,
			vmcs12->guest_interrupt_status);
	}
	if (_vmx_hasctl_enable_pml(&ctls)) {
		__vmx_vmwrite16(0x0812, vmcs12->guest_PML_index);
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
		gpa_t addr = vmcs12->control_IO_BitmapA_address;
		__vmx_vmwrite64(0x2000, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	{
		gpa_t addr = vmcs12->control_IO_BitmapB_address;
		__vmx_vmwrite64(0x2002, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_hasctl_use_msr_bitmaps(&ctls)) {
		gpa_t addr = vmcs12->control_MSR_Bitmaps_address;
		__vmx_vmwrite64(0x2004, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	{
		gpa_t addr = vmcs12->control_VM_exit_MSR_store_address;
		// TODO: need to multiplex MSR loading / storing, which is not implemented yet.
		addr = guestmem_gpa2spa_page(&ctx_pair, 0);
		__vmx_vmwrite64(0x2006, addr);
	}
	{
		gpa_t addr = vmcs12->control_VM_exit_MSR_load_address;
		// TODO: need to multiplex MSR loading / storing, which is not implemented yet.
		addr = guestmem_gpa2spa_page(&ctx_pair, 0);
		__vmx_vmwrite64(0x2008, addr);
	}
	{
		gpa_t addr = vmcs12->control_VM_entry_MSR_load_address;
		// TODO: need to multiplex MSR loading / storing, which is not implemented yet.
		addr = guestmem_gpa2spa_page(&ctx_pair, 0);
		__vmx_vmwrite64(0x200A, addr);
	}
	{
		gpa_t addr = vmcs12->control_Executive_VMCS_pointer;
		// TODO: related to SMM, check whether this restriction makes sense
		HALT_ON_ERRORCOND(addr == 0);
#ifndef __DEBUG_QEMU__
		__vmx_vmwrite64(0x200C, guestmem_gpa2spa_page(&ctx_pair, addr));
#endif /* !__DEBUG_QEMU__ */
	}
	if (_vmx_hasctl_enable_pml(&ctls)) {
		gpa_t addr = vmcs12->control_PML_address;
		__vmx_vmwrite64(0x200E, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	{
		__vmx_vmwrite64(0x2010, vmcs12->control_TSC_offset);
	}
	if (_vmx_hasctl_virtualize_apic_access(&ctls)) {
		gpa_t addr = vmcs12->control_virtual_APIC_address;
		__vmx_vmwrite64(0x2012, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_hasctl_process_posted_interrupts(&ctls)) {
		gpa_t addr = vmcs12->control_APIC_access_address;
		__vmx_vmwrite64(0x2014, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_hasctl_process_posted_interrupts(&ctls)) {
		gpa_t addr = vmcs12->control_posted_interrupt_desc_address;
		__vmx_vmwrite64(0x2016, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_hasctl_enable_vm_functions(&ctls)) {
		gpa_t addr = vmcs12->control_VM_function_controls;
		__vmx_vmwrite64(0x2018, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	{
		// Note: "Enable EPT" not supported for the guest, but XMHF needs EPT.
		// Since hypervisor needs EPT, this block is unconditional
		gpa_t addr = vmcs12->control_EPT_pointer;
		HALT_ON_ERRORCOND(_vmx_hasctl_enable_ept(&vcpu->vmx_caps));
		// TODO: to support EPT for guest, need to sanitize the entier EPT
		if (_vmx_hasctl_enable_ept(&ctls)) {
			HALT_ON_ERRORCOND(0 && "Not implemented");
		}
		HALT_ON_ERRORCOND(addr == 0);
		addr = guestmem_gpa2spa_page(&ctx_pair, addr);
		addr = vcpu->vmcs.control_EPT_pointer;
		__vmx_vmwrite64(0x201A, addr);
	}
	if (_vmx_hasctl_virtual_interrupt_delivery(&ctls)) {
		__vmx_vmwrite64(0x201C, vmcs12->control_EOI_exit_bitmap_0);
		__vmx_vmwrite64(0x201E, vmcs12->control_EOI_exit_bitmap_1);
		__vmx_vmwrite64(0x2020, vmcs12->control_EOI_exit_bitmap_2);
		__vmx_vmwrite64(0x2022, vmcs12->control_EOI_exit_bitmap_3);
	}
	if (0) {
		// Note: EPTP Switching not supported
		gpa_t addr = vmcs12->control_EPTP_list_address;
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(addr == 0);
		__vmx_vmwrite64(0x2024, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_hasctl_vmcs_shadowing(&ctls)) {
		gpa_t addr;
		addr = vmcs12->control_VMREAD_bitmap_address;
		__vmx_vmwrite64(0x2026, guestmem_gpa2spa_page(&ctx_pair, addr));
		addr = vmcs12->control_VMWRITE_bitmap_address;
		__vmx_vmwrite64(0x2028, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_hasctl_ept_violation_ve(&ctls)) {
		gpa_t addr = vmcs12->control_virt_exception_info_address;
		__vmx_vmwrite64(0x202A, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_hasctl_enable_xsaves_xrstors(&ctls)) {
		__vmx_vmwrite64(0x202C, vmcs12->control_XSS_exiting_bitmap);
	}
	if (_vmx_hasctl_enable_encls_exiting(&ctls)) {
		__vmx_vmwrite64(0x202E, vmcs12->control_ENCLS_exiting_bitmap);
	}
	if (_vmx_hasctl_sub_page_write_permissions_for_ept(&ctls)) {
		// Note: Sub-page write permissions for EPT
		gpa_t addr = vmcs12->control_subpage_permission_table_pointer;
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(addr == 0);
		__vmx_vmwrite64(0x2030, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_hasctl_use_tsc_scaling(&ctls)) {
		__vmx_vmwrite64(0x2032, vmcs12->control_TSC_multiplier);
	}
	if (_vmx_hasctl_activate_tertiary_controls(&ctls)) {
		// Note: Activate tertiary controls not supported
		u64 val = vmcs12->control_tertiary_proc_based_VMexec_ctls;
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(val == 0);
		__vmx_vmwrite64(0x2034, val);
	}
	if (_vmx_hasctl_enable_enclv_exiting(&ctls)) {
		__vmx_vmwrite64(0x2036, vmcs12->control_ENCLV_exiting_bitmap);
	}

	/* 64-Bit Read-Only Data Field: skipped */

	/* 64-Bit Guest-State Fields */
	__vmx_vmwrite64(0x2800, vmcs12->guest_VMCS_link_pointer);
	__vmx_vmwrite64(0x2802, vmcs12->guest_IA32_DEBUGCTL);
	if (_vmx_hasctl_vmexit_save_ia32_pat(&ctls) ||
		_vmx_hasctl_vmentry_load_ia32_pat(&ctls)) {
		__vmx_vmwrite64(0x2804, vmcs12->guest_IA32_PAT);
	}
	if (_vmx_hasctl_vmexit_save_ia32_efer(&ctls) ||
		_vmx_hasctl_vmentry_load_ia32_efer(&ctls)) {
		__vmx_vmwrite64(0x2806, vmcs12->guest_IA32_EFER);
	}
	if (_vmx_hasctl_vmentry_load_ia32_perf_global_ctrl(&ctls)) {
		__vmx_vmwrite64(0x2808, vmcs12->guest_IA32_PERF_GLOBAL_CTRL);
	}
	if (_vmx_hasctl_enable_ept(&ctls)) {
		__vmx_vmwrite64(0x280A, vmcs12->guest_PDPTE0);
		__vmx_vmwrite64(0x280C, vmcs12->guest_PDPTE1);
		__vmx_vmwrite64(0x280E, vmcs12->guest_PDPTE2);
		__vmx_vmwrite64(0x2810, vmcs12->guest_PDPTE3);
	}
	if (_vmx_hasctl_vmexit_clear_ia32_bndcfgs(&ctls) || 
		_vmx_hasctl_vmentry_load_ia32_bndcfgs(&ctls)) {
		__vmx_vmwrite64(0x2812, vmcs12->guest_IA32_BNDCFGS);
	}
	if (_vmx_hasctl_vmexit_clear_ia32_rtit_ctl(&ctls) ||
		_vmx_hasctl_vmentry_load_ia32_rtit_ctl(&ctls)) {
		__vmx_vmwrite64(0x2814, vmcs12->guest_IA32_RTIT_CTL);
	}
	if (_vmx_hasctl_vmentry_load_pkrs(&ctls)) {
		__vmx_vmwrite64(0x2818, vmcs12->guest_IA32_PKRS);
	}

	/* 64-Bit Host-State Fields */
	if (_vmx_hasctl_vmexit_load_ia32_pat(&ctls)) {
		__vmx_vmwrite64(0x2C00, rdmsr64(MSR_IA32_PAT));
	}
	if (_vmx_hasctl_vmexit_load_ia32_efer(&ctls)) {
		__vmx_vmwrite64(0x2C02, rdmsr64(MSR_EFER));
	}
	if (_vmx_hasctl_vmexit_load_ia32_perf_global_ctrl(&ctls)) {
		u32 eax, ebx, ecx, edx;
		cpuid(0x0, &eax, &ebx, &ecx, &edx);
		if (eax >= 0xA) {
			cpuid(0xA, &eax, &ebx, &ecx, &edx);
			if (eax & 0xffU) {
				__vmx_vmwrite64(0x2C04, rdmsr64(IA32_PERF_GLOBAL_CTRL));
			}
		}
	}
	if (_vmx_hasctl_vmexit_load_pkrs(&ctls)) {
		__vmx_vmwrite64(0x2C06, rdmsr64(IA32_PKRS));
	}

	/* 32-Bit Control Fields */
	{
		u32 val = vmcs12->control_VMX_pin_based;
		u32 fixed0 = vcpu->vmx_nested_pinbased_ctls;
		u32 fixed1 = vcpu->vmx_nested_pinbased_ctls >> 32;
		if (!((~val & fixed0) == 0 && (val & ~fixed1) == 0)) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		__vmx_vmwrite32(0x4000, val);
	}
	{
		u32 val = vmcs12->control_VMX_cpu_based;
		u32 fixed0 = vcpu->vmx_nested_procbased_ctls;
		u32 fixed1 = vcpu->vmx_nested_procbased_ctls >> 32;
		if (!((~val & fixed0) == 0 && (val & ~fixed1) == 0)) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		__vmx_vmwrite32(0x4002, val);
	}
	{
		u32 val = vmcs12->control_exception_bitmap;
		// TODO: in the future, need to merge with host's exception bitmap
		__vmx_vmwrite32(0x4004, val);
	}
	{
		u32 val = vmcs12->control_pagefault_errorcode_mask;
		__vmx_vmwrite32(0x4006, val);
	}
	{
		u32 val = vmcs12->control_pagefault_errorcode_match;
		__vmx_vmwrite32(0x4008, val);
	}
	{
		u32 val = vmcs12->control_CR3_target_count;
		__vmx_vmwrite32(0x400A, val);
	}
	{
		u32 val = vmcs12->control_VM_exit_controls;
		u32 fixed0 = vcpu->vmx_nested_exit_ctls;
		u32 fixed1 = vcpu->vmx_nested_exit_ctls >> 32;
		if (!((~val & fixed0) == 0 && (val & ~fixed1) == 0)) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		__vmx_vmwrite32(0x400C, val);
	}
	{
		u32 val = vmcs12->control_VM_exit_MSR_store_count;
		/* VM exit/entry MSR load/store not supported */
		HALT_ON_ERRORCOND(val == 0);
		__vmx_vmwrite32(0x400E, val);
	}
	{
		u32 val = vmcs12->control_VM_exit_MSR_load_count;
		/* VM exit/entry MSR load/store not supported */
		HALT_ON_ERRORCOND(val == 0);
		__vmx_vmwrite32(0x4010, val);
	}
	{
		u32 val = vmcs12->control_VM_entry_controls;
		u32 fixed0 = vcpu->vmx_nested_entry_ctls;
		u32 fixed1 = vcpu->vmx_nested_entry_ctls >> 32;
		if (!((~val & fixed0) == 0 && (val & ~fixed1) == 0)) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		__vmx_vmwrite32(0x4012, val);
	}
	{
		u32 val = vmcs12->control_VM_entry_MSR_load_count;
		/* VM exit/entry MSR load/store not supported */
		HALT_ON_ERRORCOND(val == 0);
		__vmx_vmwrite32(0x4014, val);
	}
	{
		u32 val = vmcs12->control_VM_entry_interruption_information;
		__vmx_vmwrite32(0x4016, val);
	}
	{
		u32 val = vmcs12->control_VM_entry_exception_errorcode;
		__vmx_vmwrite32(0x4018, val);
	}
	{
		u32 val = vmcs12->control_VM_entry_instruction_length;
		__vmx_vmwrite32(0x401A, val);
	}
	if (_vmx_hasctl_use_tpr_shadow(&ctls)) {
		u32 val = vmcs12->control_Task_PRivilege_Threshold;
		__vmx_vmwrite32(0x401C, val);
	}
	if (1) {
		/* TODO: ignoring _vmx_hasctl_activate_secondary_controls(&ctls) */
		u32 val = vmcs12->control_VMX_seccpu_based;
		u32 fixed0 = vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR];
		u32 fixed1 = vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32;
		if (!((~val & fixed0) == 0 && (val & ~fixed1) == 0)) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		/* XMHF needs the guest to run in EPT to protect memory */
		val |= (1U << VMX_SECPROCBASED_ENABLE_EPT);
		__vmx_vmwrite32(0x401E, val);
	}
	if (_vmx_hasctl_pause_loop_exiting(&ctls)) {
		u32 val;
		val = vmcs12->control_PLE_gap;
		__vmx_vmwrite32(0x4020, val);
		val = vmcs12->control_PLE_window;
		__vmx_vmwrite32(0x4022, val);
	}

	/* 32-Bit Read-Only Data Fields: skipped */

	/* 32-Bit Guest-State Fields */
	__vmx_vmwrite32(0x4800, vmcs12->guest_ES_limit);
	__vmx_vmwrite32(0x4802, vmcs12->guest_CS_limit);
	__vmx_vmwrite32(0x4804, vmcs12->guest_SS_limit);
	__vmx_vmwrite32(0x4806, vmcs12->guest_DS_limit);
	__vmx_vmwrite32(0x4808, vmcs12->guest_FS_limit);
	__vmx_vmwrite32(0x480A, vmcs12->guest_GS_limit);
	__vmx_vmwrite32(0x480C, vmcs12->guest_LDTR_limit);
	__vmx_vmwrite32(0x480E, vmcs12->guest_TR_limit);
	__vmx_vmwrite32(0x4810, vmcs12->guest_GDTR_limit);
	__vmx_vmwrite32(0x4812, vmcs12->guest_IDTR_limit);
	__vmx_vmwrite32(0x4814, vmcs12->guest_ES_access_rights);
	__vmx_vmwrite32(0x4816, vmcs12->guest_CS_access_rights);
	__vmx_vmwrite32(0x4818, vmcs12->guest_SS_access_rights);
	__vmx_vmwrite32(0x481A, vmcs12->guest_DS_access_rights);
	__vmx_vmwrite32(0x481C, vmcs12->guest_FS_access_rights);
	__vmx_vmwrite32(0x481E, vmcs12->guest_GS_access_rights);
	__vmx_vmwrite32(0x4820, vmcs12->guest_LDTR_access_rights);
	__vmx_vmwrite32(0x4822, vmcs12->guest_TR_access_rights);
	__vmx_vmwrite32(0x4824, vmcs12->guest_interruptibility);
	__vmx_vmwrite32(0x4826, vmcs12->guest_activity_state);
#ifndef __DEBUG_QEMU__
	__vmx_vmwrite32(0x4828, vmcs12->guest_SMBASE);
#endif /* !__DEBUG_QEMU__ */
	__vmx_vmwrite32(0x482A, vmcs12->guest_SYSENTER_CS);
	if (_vmx_hasctl_activate_vmx_preemption_timer(&ctls)) {
		u32 val = vmcs12->guest_VMX_preemption_timer_value;
		__vmx_vmwrite32(0x482E, val);
	}

	/* 32-Bit Host-State Field */
	__vmx_vmwrite32(0x4C00, vcpu->vmcs.host_SYSENTER_CS);

	/* Natural-Width Control Fields */
	{
		__vmx_vmwriteNW(0x6000, vmcs12->control_CR0_mask);
		__vmx_vmwriteNW(0x6002, vmcs12->control_CR4_mask);
		__vmx_vmwriteNW(0x6004, vmcs12->control_CR0_shadow);
		__vmx_vmwriteNW(0x6006, vmcs12->control_CR4_shadow);
#ifndef __DEBUG_QEMU__
		__vmx_vmwriteNW(0x6008, vmcs12->control_CR3_target0);
		__vmx_vmwriteNW(0x600A, vmcs12->control_CR3_target1);
		__vmx_vmwriteNW(0x600C, vmcs12->control_CR3_target2);
		__vmx_vmwriteNW(0x600E, vmcs12->control_CR3_target3);
#endif /* !__DEBUG_QEMU__ */
	}

	/* Natural-Width Read-Only Data Fields: skipped */

	/* Natural-Width Guest-State Fields */
	__vmx_vmwriteNW(0x6800, vmcs12->guest_CR0);
	__vmx_vmwriteNW(0x6802, vmcs12->guest_CR3);
	__vmx_vmwriteNW(0x6804, vmcs12->guest_CR4);
	__vmx_vmwriteNW(0x6806, vmcs12->guest_ES_base);
	__vmx_vmwriteNW(0x6808, vmcs12->guest_CS_base);
	__vmx_vmwriteNW(0x680A, vmcs12->guest_SS_base);
	__vmx_vmwriteNW(0x680C, vmcs12->guest_DS_base);
	__vmx_vmwriteNW(0x680E, vmcs12->guest_FS_base);
	__vmx_vmwriteNW(0x6810, vmcs12->guest_GS_base);
	__vmx_vmwriteNW(0x6812, vmcs12->guest_LDTR_base);
	__vmx_vmwriteNW(0x6814, vmcs12->guest_TR_base);
	__vmx_vmwriteNW(0x6816, vmcs12->guest_GDTR_base);
	__vmx_vmwriteNW(0x6818, vmcs12->guest_IDTR_base);
	__vmx_vmwriteNW(0x681A, vmcs12->guest_DR7);
	__vmx_vmwriteNW(0x681C, vmcs12->guest_RSP);
	__vmx_vmwriteNW(0x681E, vmcs12->guest_RIP);
	__vmx_vmwriteNW(0x6820, vmcs12->guest_RFLAGS);
	__vmx_vmwriteNW(0x6822, vmcs12->guest_pending_debug_x);
	__vmx_vmwriteNW(0x6824, vmcs12->guest_SYSENTER_ESP);
	__vmx_vmwriteNW(0x6826, vmcs12->guest_SYSENTER_EIP);
	if (_vmx_hasctl_vmentry_load_cet_state(&ctls)) {
		__vmx_vmwriteNW(0x6828, vmcs12->guest_IA32_S_CET);
		__vmx_vmwriteNW(0x682A, vmcs12->guest_SSP);
		__vmx_vmwriteNW(0x682C,
			vmcs12->guest_IA32_INTERRUPT_SSP_TABLE_ADDR);
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
	if (_vmx_hasctl_vmexit_load_cet_state(&ctls)) {
		/*
		 * Currently VMX_VMEXIT_LOAD_CET_STATE is disabled for the guest.
		 * To implement load CET state correctly, need to modify:
		 * * encoding 0x6C18: host_IA32_S_CET
		 * * encoding 0x6C1A: host_SSP
		 * * encoding 0x6C1C: host_IA32_INTERRUPT_SSP_TABLE_ADDR
		 */
	}

	return 0;
}

/*
 * Translate VMCS02 (already loaded as current VMCS) to VMCS12 (vmcs12)
 */
void xmhf_nested_arch_x86vmx_vmcs02_to_vmcs12(VCPU *vcpu,
												struct nested_vmcs12 *vmcs12)
{	// TODO
	vmx_ctls_t ctls;
	HALT_ON_ERRORCOND(_vmcs12_get_ctls(vcpu, vmcs12, &ctls) == 0);

	/* 16-Bit Control Fields */
	if (_vmx_hasctl_enable_vpid(&ctls)) {
		// Note: VIRTUAL PROCESSOR IDENTIFIERS (VPIDS) not supported yet
		// Need to multiplex vmcs12->control_vpid
		HALT_ON_ERRORCOND(__vmx_vmread16(0x0000) == 0);
		// vmcs12->control_vpid = __vmx_vmread16(0x0000);
	}
	if (_vmx_hasctl_process_posted_interrupts(&ctls)) {
		vmcs12->control_post_interrupt_notification_vec = __vmx_vmread16(0x0002);
	}
	if (_vmx_hasctl_ept_violation_ve(&ctls)) {
		vmcs12->control_eptp_index = __vmx_vmread16(0x0004);
	}

	/* 16-Bit Guest-State Fields */
	vmcs12->guest_ES_selector = __vmx_vmread16(0x0800);
	vmcs12->guest_CS_selector = __vmx_vmread16(0x0802);
	vmcs12->guest_SS_selector = __vmx_vmread16(0x0804);
	vmcs12->guest_DS_selector = __vmx_vmread16(0x0806);
	vmcs12->guest_FS_selector = __vmx_vmread16(0x0808);
	vmcs12->guest_GS_selector = __vmx_vmread16(0x080A);
	vmcs12->guest_LDTR_selector = __vmx_vmread16(0x080C);
	vmcs12->guest_TR_selector = __vmx_vmread16(0x080E);
	if (_vmx_hasctl_virtual_interrupt_delivery(&ctls)) {
		vmcs12->guest_interrupt_status = __vmx_vmread16(0x0810);
	}
	if (_vmx_hasctl_enable_pml(&ctls)) {
		vmcs12->guest_PML_index = __vmx_vmread16(0x0812);
	}

	/* 16-Bit Host-State Fields */
	HALT_ON_ERRORCOND(vcpu->vmcs.host_ES_selector == __vmx_vmread16(0x0C00));
	HALT_ON_ERRORCOND(vcpu->vmcs.host_CS_selector == __vmx_vmread16(0x0C02));
	HALT_ON_ERRORCOND(vcpu->vmcs.host_SS_selector == __vmx_vmread16(0x0C04));
	HALT_ON_ERRORCOND(vcpu->vmcs.host_DS_selector == __vmx_vmread16(0x0C06));
	HALT_ON_ERRORCOND(vcpu->vmcs.host_FS_selector == __vmx_vmread16(0x0C08));
	HALT_ON_ERRORCOND(vcpu->vmcs.host_GS_selector == __vmx_vmread16(0x0C0A));
	HALT_ON_ERRORCOND(vcpu->vmcs.host_TR_selector == __vmx_vmread16(0x0C0C));

	/* 16-Bit fields: VMCS12 host -> VMCS02 guest */
	vcpu->vmcs.guest_ES_selector = vmcs12->host_ES_selector;
	vcpu->vmcs.guest_CS_selector = vmcs12->host_CS_selector;
	vcpu->vmcs.guest_SS_selector = vmcs12->host_SS_selector;
	vcpu->vmcs.guest_DS_selector = vmcs12->host_DS_selector;
	vcpu->vmcs.guest_FS_selector = vmcs12->host_FS_selector;
	vcpu->vmcs.guest_GS_selector = vmcs12->host_GS_selector;
	{
		/*
		 * SDM volume 3 26.5.2 "Loading Host Segment and Descriptor-Table
		 * Registers": "the selector is cleared to 0000H".
		 */
		vcpu->vmcs.guest_LDTR_selector = 0x0000U;
	}
	vcpu->vmcs.guest_TR_selector = vmcs12->host_TR_selector;

	/* 64-Bit Control Fields */
	{
		vmcs12->control_IO_BitmapA_address = __vmx_vmread64(0x2000);
	}
	{
		vmcs12->control_IO_BitmapB_address = __vmx_vmread64(0x2002);
	}
	if (_vmx_hasctl_use_msr_bitmaps(&ctls)) {
		vmcs12->control_MSR_Bitmaps_address = __vmx_vmread64(0x2004);
	}
	{
		// TODO: need to multiplex MSR loading / storing, which is not implemented yet.
		HALT_ON_ERRORCOND(__vmx_vmread64(0x2006) == 0);
		// vmcs12->control_VM_exit_MSR_store_address = ...
	}
	{
		// TODO: need to multiplex MSR loading / storing, which is not implemented yet.
		HALT_ON_ERRORCOND(__vmx_vmread64(0x2008) == 0);
		// vmcs12->control_VM_exit_MSR_load_address = ...;
	}
	{
		// TODO: need to multiplex MSR loading / storing, which is not implemented yet.
		HALT_ON_ERRORCOND(__vmx_vmread64(0x200A) == 0);
		// vmcs12->control_VM_entry_MSR_load_address = ...;
	}
	{
		// TODO: related to SMM, check whether this restriction makes sense
#ifndef __DEBUG_QEMU__
		HALT_ON_ERRORCOND(__vmx_vmread64(0x200C) == 0);
#endif /* !__DEBUG_QEMU__ */
		// vmcs12->control_Executive_VMCS_pointer = ...;
	}
	if (_vmx_hasctl_enable_pml(&ctls)) {
		vmcs12->control_PML_address = __vmx_vmread64(0x200E);
	}
	{
		vmcs12->control_TSC_offset = __vmx_vmread64(0x2010);
	}
	if (_vmx_hasctl_virtualize_apic_access(&ctls)) {
		vmcs12->control_virtual_APIC_address = __vmx_vmread64(0x2012);
	}
	if (_vmx_hasctl_process_posted_interrupts(&ctls)) {
		vmcs12->control_APIC_access_address = __vmx_vmread64(0x2014);
	}
	if (_vmx_hasctl_process_posted_interrupts(&ctls)) {
		vmcs12->control_posted_interrupt_desc_address = __vmx_vmread64(0x2016);
	}
	if (_vmx_hasctl_enable_vm_functions(&ctls)) {
		vmcs12->control_VM_function_controls = __vmx_vmread64(0x2018);
	}
	if (1) {
		// Note: "Enable EPT" not supported for the guest, but XMHF needs EPT.
		// Since hypervisor needs EPT, this block is unconditional
		gpa_t addr = vcpu->vmcs.control_EPT_pointer;
		HALT_ON_ERRORCOND(_vmx_hasctl_enable_ept(&vcpu->vmx_caps));
		// TODO: to support EPT for guest, need to sanitize the entier EPT
		if (_vmx_hasctl_enable_ept(&ctls)) {
			HALT_ON_ERRORCOND(0 && "Not implemented");
		}
		HALT_ON_ERRORCOND(__vmx_vmread64(0x201A) == addr);
		addr = 0;
		// vmcs12->control_EPT_pointer = ...
	}
	if (_vmx_hasctl_virtual_interrupt_delivery(&ctls)) {
		vmcs12->control_EOI_exit_bitmap_0 = __vmx_vmread64(0x201C);
		vmcs12->control_EOI_exit_bitmap_1 = __vmx_vmread64(0x201E);
		vmcs12->control_EOI_exit_bitmap_2 = __vmx_vmread64(0x2020);
		vmcs12->control_EOI_exit_bitmap_3 = __vmx_vmread64(0x2022);
	}
	if (0) {
		// Note: EPTP Switching not supported
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(__vmx_vmread64(0x2024) == 0);
		// vmcs12->control_EPTP_list_address = ...
	}
	if (_vmx_hasctl_vmcs_shadowing(&ctls)) {
		vmcs12->control_VMREAD_bitmap_address = __vmx_vmread64(0x2026);
		vmcs12->control_VMWRITE_bitmap_address = __vmx_vmread64(0x2028);
	}
	if (_vmx_hasctl_ept_violation_ve(&ctls)) {
		vmcs12->control_virt_exception_info_address = __vmx_vmread64(0x202A);
	}
	if (_vmx_hasctl_enable_xsaves_xrstors(&ctls)) {
		vmcs12->control_XSS_exiting_bitmap = __vmx_vmread64(0x202C);
	}
	if (_vmx_hasctl_enable_encls_exiting(&ctls)) {
		vmcs12->control_ENCLS_exiting_bitmap = __vmx_vmread64(0x202E);
	}
	if (_vmx_hasctl_sub_page_write_permissions_for_ept(&ctls)) {
		// Note: Sub-page write permissions for EPT
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(__vmx_vmread64(0x2030) == 0);
		// vmcs12->control_subpage_permission_table_pointer = ...
	}
	if (_vmx_hasctl_use_tsc_scaling(&ctls)) {
		vmcs12->control_TSC_multiplier = __vmx_vmread64(0x2032);
	}
	if (_vmx_hasctl_activate_tertiary_controls(&ctls)) {
		// Note: Activate tertiary controls not supported
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(__vmx_vmread64(0x2034) == 0);
		// vmcs12->control_tertiary_proc_based_VMexec_ctls = ...
	}
	if (_vmx_hasctl_enable_enclv_exiting(&ctls)) {
		vmcs12->control_ENCLV_exiting_bitmap = __vmx_vmread64(0x2036);
	}

	/* 64-Bit Read-Only Data Field */
	if (_vmx_hasctl_enable_ept(&ctls)) {
		vmcs12->guest_paddr = __vmx_vmread64(0x2400);
	}

	/* 64-Bit Guest-State Fields */
	vmcs12->guest_VMCS_link_pointer = __vmx_vmread64(0x2800);
	vmcs12->guest_IA32_DEBUGCTL = __vmx_vmread64(0x2802);
	if (_vmx_hasctl_vmexit_save_ia32_pat(&ctls) ||
		_vmx_hasctl_vmentry_load_ia32_pat(&ctls)) {
		vmcs12->guest_IA32_PAT = __vmx_vmread64(0x2804);
	}
	if (_vmx_hasctl_vmexit_save_ia32_efer(&ctls) ||
		_vmx_hasctl_vmentry_load_ia32_efer(&ctls)) {
		vmcs12->guest_IA32_EFER = __vmx_vmread64(0x2806);
	}
	if (_vmx_hasctl_vmentry_load_ia32_perf_global_ctrl(&ctls)) {
		vmcs12->guest_IA32_PERF_GLOBAL_CTRL = __vmx_vmread64(0x2808);
	}
	if (_vmx_hasctl_enable_ept(&ctls)) {
		vmcs12->guest_PDPTE0 = __vmx_vmread64(0x280A);
		vmcs12->guest_PDPTE1 = __vmx_vmread64(0x280C);
		vmcs12->guest_PDPTE2 = __vmx_vmread64(0x280E);
		vmcs12->guest_PDPTE3 = __vmx_vmread64(0x2810);
	}
	if (_vmx_hasctl_vmexit_clear_ia32_bndcfgs(&ctls) || 
		_vmx_hasctl_vmentry_load_ia32_bndcfgs(&ctls)) {
		vmcs12->guest_IA32_BNDCFGS = __vmx_vmread64(0x2812);
	}
	if (_vmx_hasctl_vmexit_clear_ia32_rtit_ctl(&ctls) ||
		_vmx_hasctl_vmentry_load_ia32_rtit_ctl(&ctls)) {
		vmcs12->guest_IA32_RTIT_CTL = __vmx_vmread64(0x2814);
	}
	if (_vmx_hasctl_vmentry_load_pkrs(&ctls)) {
		vmcs12->guest_IA32_PKRS = __vmx_vmread64(0x2818);
	}

	/* 64-Bit Host-State Fields */
	if (_vmx_hasctl_vmexit_load_ia32_pat(&ctls)) {
		HALT_ON_ERRORCOND(__vmx_vmread64(0x2C00) == rdmsr64(MSR_IA32_PAT));
	}
	if (_vmx_hasctl_vmexit_load_ia32_efer(&ctls)) {
		HALT_ON_ERRORCOND(__vmx_vmread64(0x2C02) == rdmsr64(MSR_EFER));
	}
	if (_vmx_hasctl_vmexit_load_ia32_perf_global_ctrl(&ctls)) {
		u32 eax, ebx, ecx, edx;
		cpuid(0x0, &eax, &ebx, &ecx, &edx);
		if (eax >= 0xA) {
			cpuid(0xA, &eax, &ebx, &ecx, &edx);
			if (eax & 0xffU) {
				HALT_ON_ERRORCOND(__vmx_vmread64(0x2C04) ==
									rdmsr64(IA32_PERF_GLOBAL_CTRL));
			}
		}
	}
	if (_vmx_hasctl_vmexit_load_pkrs(&ctls)) {
		HALT_ON_ERRORCOND(__vmx_vmread64(0x2C06) == rdmsr64(IA32_PKRS));
	}

	/* 64-Bit fields: VMCS12 host -> VMCS02 guest */
	if (_vmx_hasctl_vmexit_load_ia32_pat(&ctls)) {
		// TODO: check whether guest hypervisor enables the feature
		if (0) {
			wrmsr64(MSR_IA32_PAT, __vmx_vmread64(0x2C00));
		}
	}
	if (_vmx_hasctl_vmexit_load_ia32_efer(&ctls)) {
		// TODO: check whether guest hypervisor enables the feature
		if (0) {
			wrmsr64(MSR_EFER, __vmx_vmread64(0x2C02));
		}
	}
	if (_vmx_hasctl_vmexit_load_ia32_perf_global_ctrl(&ctls)) {
		u32 eax, ebx, ecx, edx;
		cpuid(0x0, &eax, &ebx, &ecx, &edx);
		if (eax >= 0xA) {
			cpuid(0xA, &eax, &ebx, &ecx, &edx);
			if (eax & 0xffU) {
				// TODO: check whether guest hypervisor enables the feature
				if (0) {
					wrmsr64(IA32_PERF_GLOBAL_CTRL, __vmx_vmread64(0x2C04));
				}
			}
		}
	}
	if (_vmx_hasctl_vmexit_load_pkrs(&ctls)) {
		// TODO: check whether guest hypervisor enables the feature
		if (0) {
			wrmsr64(IA32_PKRS, __vmx_vmread64(0x2C06));
		}
	}


	/* 32-Bit Control Fields */
	{
		vmcs12->control_VMX_pin_based = __vmx_vmread32(0x4000);
	}
	{
		vmcs12->control_VMX_cpu_based = __vmx_vmread32(0x4002);
	}
	{
		// TODO: in the future, need to merge with host's exception bitmap
		vmcs12->control_exception_bitmap = __vmx_vmread32(0x4004);
	}
	{
		vmcs12->control_pagefault_errorcode_mask = __vmx_vmread32(0x4006);
	}
	{
		vmcs12->control_pagefault_errorcode_match = __vmx_vmread32(0x4008);
	}
	{
		vmcs12->control_CR3_target_count = __vmx_vmread32(0x400A);
	}
	{
		vmcs12->control_VM_exit_controls = __vmx_vmread32(0x400C);
	}
	{
		vmcs12->control_VM_exit_MSR_store_count = __vmx_vmread32(0x400E);
	}
	{
		vmcs12->control_VM_exit_MSR_load_count = __vmx_vmread32(0x4010);
	}
	{
		vmcs12->control_VM_entry_controls = __vmx_vmread32(0x4012);
	}
	{
		vmcs12->control_VM_entry_MSR_load_count = __vmx_vmread32(0x4014);
	}
	{
		vmcs12->control_VM_entry_interruption_information = __vmx_vmread32(0x4016);
	}
	{
		vmcs12->control_VM_entry_exception_errorcode = __vmx_vmread32(0x4018);
	}
	{
		vmcs12->control_VM_entry_instruction_length = __vmx_vmread32(0x401A);
	}
	if (_vmx_hasctl_use_tpr_shadow(&ctls)) {
		vmcs12->control_Task_PRivilege_Threshold = __vmx_vmread32(0x401C);
	}
	if (1) {
		/* TODO: ignoring _vmx_hasctl_activate_secondary_controls(&ctls) */
		u32 val = __vmx_vmread32(0x401E);
		/* XMHF needs the guest to run in EPT to protect memory */
		val &= ~(1U << VMX_SECPROCBASED_ENABLE_EPT);
		vmcs12->control_VMX_seccpu_based = val;
	}
	if (_vmx_hasctl_pause_loop_exiting(&ctls)) {
		vmcs12->control_PLE_gap = __vmx_vmread32(0x4020);
		vmcs12->control_PLE_window = __vmx_vmread32(0x4022);
	}

	/* 32-Bit Read-Only Data Fields */
	vmcs12->info_vminstr_error = __vmx_vmread32(0x4400);
	vmcs12->info_vmexit_reason = __vmx_vmread32(0x4402);
	vmcs12->info_vmexit_interrupt_information = __vmx_vmread32(0x4404);
	vmcs12->info_vmexit_interrupt_error_code = __vmx_vmread32(0x4406);
	vmcs12->info_IDT_vectoring_information = __vmx_vmread32(0x4408);
	vmcs12->info_IDT_vectoring_error_code = __vmx_vmread32(0x440A);
	vmcs12->info_vmexit_instruction_length = __vmx_vmread32(0x440C);
	vmcs12->info_vmx_instruction_information = __vmx_vmread32(0x440E);

	/* 32-Bit Guest-State Fields */
	vmcs12->guest_ES_limit = __vmx_vmread32(0x4800);
	vmcs12->guest_CS_limit = __vmx_vmread32(0x4802);
	vmcs12->guest_SS_limit = __vmx_vmread32(0x4804);
	vmcs12->guest_DS_limit = __vmx_vmread32(0x4806);
	vmcs12->guest_FS_limit = __vmx_vmread32(0x4808);
	vmcs12->guest_GS_limit = __vmx_vmread32(0x480A);
	vmcs12->guest_LDTR_limit = __vmx_vmread32(0x480C);
	vmcs12->guest_TR_limit = __vmx_vmread32(0x480E);
	vmcs12->guest_GDTR_limit = __vmx_vmread32(0x4810);
	vmcs12->guest_IDTR_limit = __vmx_vmread32(0x4812);
	vmcs12->guest_ES_access_rights = __vmx_vmread32(0x4814);
	vmcs12->guest_CS_access_rights = __vmx_vmread32(0x4816);
	vmcs12->guest_SS_access_rights = __vmx_vmread32(0x4818);
	vmcs12->guest_DS_access_rights = __vmx_vmread32(0x481A);
	vmcs12->guest_FS_access_rights = __vmx_vmread32(0x481C);
	vmcs12->guest_GS_access_rights = __vmx_vmread32(0x481E);
	vmcs12->guest_LDTR_access_rights = __vmx_vmread32(0x4820);
	vmcs12->guest_TR_access_rights = __vmx_vmread32(0x4822);
	vmcs12->guest_interruptibility = __vmx_vmread32(0x4824);
	vmcs12->guest_activity_state = __vmx_vmread32(0x4826);
#ifndef __DEBUG_QEMU__
	vmcs12->guest_SMBASE = __vmx_vmread32(0x4828);
#endif /* !__DEBUG_QEMU__ */
	vmcs12->guest_SYSENTER_CS = __vmx_vmread32(0x482A);
	if (_vmx_hasctl_activate_vmx_preemption_timer(&ctls)) {
		vmcs12->guest_VMX_preemption_timer_value = __vmx_vmread32(0x482E);
	}

	/* 32-Bit Host-State Field */
	HALT_ON_ERRORCOND(vcpu->vmcs.host_SYSENTER_CS == __vmx_vmread32(0x4C00));

	/* 32-Bit fields: VMCS12 host -> VMCS02 guest */
	vcpu->vmcs.guest_SYSENTER_CS = vmcs12->host_IA32_SYSENTER_CS;

	/* Natural-Width Control Fields */
	{
		vmcs12->control_CR0_mask = __vmx_vmreadNW(0x6000);
		vmcs12->control_CR4_mask = __vmx_vmreadNW(0x6002);
		vmcs12->control_CR0_shadow = __vmx_vmreadNW(0x6004);
		vmcs12->control_CR4_shadow = __vmx_vmreadNW(0x6006);
#ifndef __DEBUG_QEMU__
		vmcs12->control_CR3_target0 = __vmx_vmreadNW(0x6008);
		vmcs12->control_CR3_target1 = __vmx_vmreadNW(0x600A);
		vmcs12->control_CR3_target2 = __vmx_vmreadNW(0x600C);
		vmcs12->control_CR3_target3 = __vmx_vmreadNW(0x600E);
#endif /* !__DEBUG_QEMU__ */
	}

	/* Natural-Width Read-Only Data Fields */
	vmcs12->info_exit_qualification = __vmx_vmreadNW(0x6400);
#ifndef __DEBUG_QEMU__
	vmcs12->info_IO_RCX = __vmx_vmreadNW(0x6402);
	vmcs12->info_IO_RSI = __vmx_vmreadNW(0x6404);
	vmcs12->info_IO_RDI = __vmx_vmreadNW(0x6406);
	vmcs12->info_IO_RIP = __vmx_vmreadNW(0x6408);
#endif /* !__DEBUG_QEMU__ */
	vmcs12->info_guest_linear_address = __vmx_vmreadNW(0x640A);

	/* Natural-Width Guest-State Fields */
	vmcs12->guest_CR0 = __vmx_vmreadNW(0x6800);
	vmcs12->guest_CR3 = __vmx_vmreadNW(0x6802);
	vmcs12->guest_CR4 = __vmx_vmreadNW(0x6804);
	vmcs12->guest_ES_base = __vmx_vmreadNW(0x6806);
	vmcs12->guest_CS_base = __vmx_vmreadNW(0x6808);
	vmcs12->guest_SS_base = __vmx_vmreadNW(0x680A);
	vmcs12->guest_DS_base = __vmx_vmreadNW(0x680C);
	vmcs12->guest_FS_base = __vmx_vmreadNW(0x680E);
	vmcs12->guest_GS_base = __vmx_vmreadNW(0x6810);
	vmcs12->guest_LDTR_base = __vmx_vmreadNW(0x6812);
	vmcs12->guest_TR_base = __vmx_vmreadNW(0x6814);
	vmcs12->guest_GDTR_base = __vmx_vmreadNW(0x6816);
	vmcs12->guest_IDTR_base = __vmx_vmreadNW(0x6818);
	vmcs12->guest_DR7 = __vmx_vmreadNW(0x681A);
	vmcs12->guest_RSP = __vmx_vmreadNW(0x681C);
	vmcs12->guest_RIP = __vmx_vmreadNW(0x681E);
	vmcs12->guest_RFLAGS = __vmx_vmreadNW(0x6820);
	vmcs12->guest_pending_debug_x = __vmx_vmreadNW(0x6822);
	vmcs12->guest_SYSENTER_ESP = __vmx_vmreadNW(0x6824);
	vmcs12->guest_SYSENTER_EIP = __vmx_vmreadNW(0x6826);
	if (_vmx_hasctl_vmentry_load_cet_state(&ctls)) {
		vmcs12->guest_IA32_S_CET = __vmx_vmreadNW(0x6828);
		vmcs12->guest_SSP = __vmx_vmreadNW(0x682A);
		vmcs12->guest_IA32_INTERRUPT_SSP_TABLE_ADDR = __vmx_vmreadNW(0x682C);
	}

	/* Natural-Width Host-State Fields */
	HALT_ON_ERRORCOND(__vmx_vmreadNW(0x6C00) == vcpu->vmcs.host_CR0);
	HALT_ON_ERRORCOND(__vmx_vmreadNW(0x6C02) == vcpu->vmcs.host_CR3);
	HALT_ON_ERRORCOND(__vmx_vmreadNW(0x6C04) == vcpu->vmcs.host_CR4);
	HALT_ON_ERRORCOND(__vmx_vmreadNW(0x6C06) == vcpu->vmcs.host_FS_base);
	HALT_ON_ERRORCOND(__vmx_vmreadNW(0x6C08) == vcpu->vmcs.host_GS_base);
	HALT_ON_ERRORCOND(__vmx_vmreadNW(0x6C0A) == vcpu->vmcs.host_TR_base);
	HALT_ON_ERRORCOND(__vmx_vmreadNW(0x6C0C) == vcpu->vmcs.host_GDTR_base);
	HALT_ON_ERRORCOND(__vmx_vmreadNW(0x6C0E) == vcpu->vmcs.host_IDTR_base);
	HALT_ON_ERRORCOND(__vmx_vmreadNW(0x6C10) == vcpu->vmcs.host_SYSENTER_ESP);
	HALT_ON_ERRORCOND(__vmx_vmreadNW(0x6C12) == vcpu->vmcs.host_SYSENTER_EIP);
	HALT_ON_ERRORCOND(__vmx_vmreadNW(0x6C14) == vcpu->vmcs.host_RSP);
	HALT_ON_ERRORCOND(__vmx_vmreadNW(0x6C16) == vcpu->vmcs.host_RIP);
	if (_vmx_hasctl_vmexit_load_cet_state(&ctls)) {
		/*
		 * Currently VMX_VMEXIT_LOAD_CET_STATE is disabled for the guest.
		 * To implement load CET state correctly, need to modify:
		 * * encoding 0x6C18: host_IA32_S_CET
		 * * encoding 0x6C1A: host_SSP
		 * * encoding 0x6C1C: host_IA32_INTERRUPT_SSP_TABLE_ADDR
		 */
	}

	/* Natural-Width fields: VMCS12 host -> VMCS02 guest */
	vcpu->vmcs.guest_CR0 = vmcs12->host_CR0;
	vcpu->vmcs.guest_CR3 = vmcs12->host_CR3;
	vcpu->vmcs.guest_CR4 = vmcs12->host_CR4;
	vcpu->vmcs.guest_FS_base = vmcs12->host_FS_base;
	vcpu->vmcs.guest_GS_base = vmcs12->host_GS_base;
	vcpu->vmcs.guest_TR_base = vmcs12->host_TR_base;
	vcpu->vmcs.guest_GDTR_base = vmcs12->host_GDTR_base;
	vcpu->vmcs.guest_IDTR_base = vmcs12->host_IDTR_base;
	vcpu->vmcs.guest_SYSENTER_ESP = vmcs12->host_SYSENTER_ESP;
	vcpu->vmcs.guest_SYSENTER_EIP = vmcs12->host_SYSENTER_EIP;
	vcpu->vmcs.guest_RSP = vmcs12->host_RSP;
	vcpu->vmcs.guest_RIP = vmcs12->host_RIP;
	if (_vmx_hasctl_vmexit_load_cet_state(&ctls)) {
		/*
		 * Currently VMX_VMEXIT_LOAD_CET_STATE is disabled for the guest.
		 * To implement load CET state correctly, need to modify:
		 * * encoding 0x6C18: host_IA32_S_CET
		 * * encoding 0x6C1A: host_SSP
		 * * encoding 0x6C1C: host_IA32_INTERRUPT_SSP_TABLE_ADDR
		 */
	}
}
