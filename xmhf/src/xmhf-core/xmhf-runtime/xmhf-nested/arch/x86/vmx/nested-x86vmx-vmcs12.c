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

#define FIELD_CTLS_ARG (&ctls)
#define DECLARE_FIELD_16_RW(encoding, name, prop, exist, ...) \
	if (exist) { \
		if (prop & FIELD_PROP_ID_GUEST) { \
			__vmx_vmwrite16(encoding, vmcs12->name); \
		} \
	}
#define DECLARE_FIELD_64_RW(encoding, name, prop, exist, ...) \
	if (exist) { \
		if (prop & FIELD_PROP_ID_GUEST) { \
			__vmx_vmwrite64(encoding, vmcs12->name); \
		} else if (prop & FIELD_PROP_GPADDR) { \
			gpa_t addr = vmcs12->name; \
			__vmx_vmwrite64(encoding, guestmem_gpa2spa_page(&ctx_pair, addr)); \
		} \
	}
#define DECLARE_FIELD_32_RW(encoding, name, prop, exist, ...) \
	if (exist) { \
		if (prop & FIELD_PROP_ID_GUEST) { \
			__vmx_vmwrite32(encoding, vmcs12->name); \
		} \
	}
#define DECLARE_FIELD_NW_RW(encoding, name, prop, exist, ...) \
	if (exist) { \
		if (prop & FIELD_PROP_ID_GUEST) { \
			__vmx_vmwriteNW(encoding, vmcs12->name); \
		} \
	}
#include "nested-x86vmx-vmcs12-fields.h"

	/* 16-Bit Control Fields */
	if (_vmx_hasctl_enable_vpid(&ctls)) {
		u16 control_vpid = vmcs12->control_vpid;
		// Note: VIRTUAL PROCESSOR IDENTIFIERS (VPIDS) not supported yet
		// Need to multiplex vmcs12->control_vpid
		control_vpid = 0;
		__vmx_vmwrite16(0x0000, control_vpid);
	}

	/* 16-Bit Guest-State Fields */

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
	if (0) {
		// Note: EPTP Switching not supported
		gpa_t addr = vmcs12->control_EPTP_list_address;
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(addr == 0);
		__vmx_vmwrite64(0x2024, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_hasctl_sub_page_write_permissions_for_ept(&ctls)) {
		// Note: Sub-page write permissions for EPT
		gpa_t addr = vmcs12->control_subpage_permission_table_pointer;
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(addr == 0);
		__vmx_vmwrite64(0x2030, guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_hasctl_activate_tertiary_controls(&ctls)) {
		// Note: Activate tertiary controls not supported
		u64 val = vmcs12->control_tertiary_proc_based_VMexec_ctls;
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(val == 0);
		__vmx_vmwrite64(0x2034, val);
	}

	/* 64-Bit Read-Only Data Field: skipped */

	/* 64-Bit Guest-State Fields */

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
		__vmx_vmwrite32(0x4000, val);
	}
	{
		u32 val = vmcs12->control_VMX_cpu_based;
		/* XMHF needs to activate secondary controls because of EPT */
		val |= (1U << VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS);
		__vmx_vmwrite32(0x4002, val);
	}
	{
		u32 val = vmcs12->control_exception_bitmap;
		// TODO: in the future, need to merge with host's exception bitmap
		__vmx_vmwrite32(0x4004, val);
	}
	{
		u32 val = vmcs12->control_VM_exit_controls;
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
		__vmx_vmwrite32(0x4012, val);
	}
	{
		u32 val = vmcs12->control_VM_entry_MSR_load_count;
		/* VM exit/entry MSR load/store not supported */
		HALT_ON_ERRORCOND(val == 0);
		__vmx_vmwrite32(0x4014, val);
	}
	if (1) {
		/* TODO: ignoring _vmx_hasctl_activate_secondary_controls(&ctls) */
		u32 val = vmcs12->control_VMX_seccpu_based;
		/* XMHF needs the guest to run in EPT to protect memory */
		val |= (1U << VMX_SECPROCBASED_ENABLE_EPT);
		__vmx_vmwrite32(0x401E, val);
	}

	/* 32-Bit Read-Only Data Fields: skipped */

	/* 32-Bit Guest-State Fields */

	/* 32-Bit Host-State Field */
	// TODO: this can probably be FIELD_PROP_ID_HOST, but need to rename to host_IA32_SYSENTER_CS
	__vmx_vmwrite32(0x4C00, vcpu->vmcs.host_SYSENTER_CS);

	/* Natural-Width Control Fields */

	/* Natural-Width Read-Only Data Fields: skipped */

	/* Natural-Width Guest-State Fields */

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
		HALT_ON_ERRORCOND(0 && "Not implemented");
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

#define FIELD_CTLS_ARG (&ctls)
#define DECLARE_FIELD_16(encoding, name, prop, exist, ...) \
	if (exist) { \
		if (prop & FIELD_PROP_ID_GUEST) { \
			vmcs12->name = __vmx_vmread16(encoding); \
		} \
	}
#define DECLARE_FIELD_64(encoding, name, prop, exist, ...) \
	if (exist) { \
		if (prop & FIELD_PROP_ID_GUEST) { \
			vmcs12->name = __vmx_vmread64(encoding); \
		} else if (prop & FIELD_PROP_GPADDR) { \
			vmcs12->name = __vmx_vmread64(encoding); \
		} \
	}
#define DECLARE_FIELD_32(encoding, name, prop, exist, ...) \
	if (exist) { \
		if (prop & FIELD_PROP_ID_GUEST) { \
			vmcs12->name = __vmx_vmread32(encoding); \
		} \
	}
#define DECLARE_FIELD_NW(encoding, name, prop, exist, ...) \
	if (exist) { \
		if (prop & FIELD_PROP_ID_GUEST) { \
			vmcs12->name = __vmx_vmreadNW(encoding); \
		} \
	}
#include "nested-x86vmx-vmcs12-fields.h"

	/* 16-Bit Control Fields */
	if (_vmx_hasctl_enable_vpid(&ctls)) {
		// Note: VIRTUAL PROCESSOR IDENTIFIERS (VPIDS) not supported yet
		// Need to multiplex vmcs12->control_vpid
		HALT_ON_ERRORCOND(__vmx_vmread16(0x0000) == 0);
		// vmcs12->control_vpid = __vmx_vmread16(0x0000);
	}

	/* 16-Bit Guest-State Fields */

	/* 16-Bit Host-State Fields */
	HALT_ON_ERRORCOND(vcpu->vmcs.host_ES_selector == __vmx_vmread16(0x0C00));
	HALT_ON_ERRORCOND(vcpu->vmcs.host_CS_selector == __vmx_vmread16(0x0C02));
	HALT_ON_ERRORCOND(vcpu->vmcs.host_SS_selector == __vmx_vmread16(0x0C04));
	HALT_ON_ERRORCOND(vcpu->vmcs.host_DS_selector == __vmx_vmread16(0x0C06));
	HALT_ON_ERRORCOND(vcpu->vmcs.host_FS_selector == __vmx_vmread16(0x0C08));
	HALT_ON_ERRORCOND(vcpu->vmcs.host_GS_selector == __vmx_vmread16(0x0C0A));
	HALT_ON_ERRORCOND(vcpu->vmcs.host_TR_selector == __vmx_vmread16(0x0C0C));

	/* 16-Bit fields: VMCS12 host -> VMCS01 guest */
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
	if (0) {
		// Note: EPTP Switching not supported
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(__vmx_vmread64(0x2024) == 0);
		// vmcs12->control_EPTP_list_address = ...
	}
	if (_vmx_hasctl_sub_page_write_permissions_for_ept(&ctls)) {
		// Note: Sub-page write permissions for EPT
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(__vmx_vmread64(0x2030) == 0);
		// vmcs12->control_subpage_permission_table_pointer = ...
	}
	if (_vmx_hasctl_activate_tertiary_controls(&ctls)) {
		// Note: Activate tertiary controls not supported
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(__vmx_vmread64(0x2034) == 0);
		// vmcs12->control_tertiary_proc_based_VMexec_ctls = ...
	}

	/* 64-Bit Read-Only Data Field */

	/* 64-Bit Guest-State Fields */

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

	/* 64-Bit fields: VMCS12 host -> VMCS01 guest */
	if (_vmx_hasctl_vmexit_load_ia32_pat(&ctls)) {
		wrmsr64(MSR_IA32_PAT, __vmx_vmread64(0x2C00));
	}
	if (_vmx_hasctl_vmexit_load_ia32_efer(&ctls)) {
		wrmsr64(MSR_EFER, __vmx_vmread64(0x2C02));
	}
	if (_vmx_hasctl_vmexit_load_ia32_perf_global_ctrl(&ctls)) {
		u32 eax, ebx, ecx, edx;
		cpuid(0x0, &eax, &ebx, &ecx, &edx);
		if (eax >= 0xA) {
			cpuid(0xA, &eax, &ebx, &ecx, &edx);
			if (eax & 0xffU) {
				wrmsr64(IA32_PERF_GLOBAL_CTRL, __vmx_vmread64(0x2C04));
			}
		}
	}
	if (_vmx_hasctl_vmexit_load_pkrs(&ctls)) {
		wrmsr64(IA32_PKRS, __vmx_vmread64(0x2C06));
	}

	/* 32-Bit Control Fields */
	{
		vmcs12->control_VMX_pin_based = __vmx_vmread32(0x4000);
	}
	{
		u32 val = __vmx_vmread32(0x4002);
		HALT_ON_ERRORCOND(val == (
			vmcs12->control_VMX_cpu_based |
			(1U << VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS)));
	}
	{
		// TODO: in the future, need to merge with host's exception bitmap
		vmcs12->control_exception_bitmap = __vmx_vmread32(0x4004);
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
	if (1) {
		/* TODO: ignoring _vmx_hasctl_activate_secondary_controls(&ctls) */
		u32 val = __vmx_vmread32(0x401E);
		/* XMHF needs the guest to run in EPT to protect memory */
		val &= ~(1U << VMX_SECPROCBASED_ENABLE_EPT);
		vmcs12->control_VMX_seccpu_based = val;
	}

	/* 32-Bit Read-Only Data Fields */

	/* 32-Bit Guest-State Fields */

	/* 32-Bit Host-State Field */
	HALT_ON_ERRORCOND(vcpu->vmcs.host_SYSENTER_CS == __vmx_vmread32(0x4C00));

	/* 32-Bit fields: VMCS12 host -> VMCS02 guest */
	vcpu->vmcs.guest_SYSENTER_CS = vmcs12->host_IA32_SYSENTER_CS;

	/* Natural-Width Control Fields */

	/* Natural-Width Read-Only Data Fields */

	/* Natural-Width Guest-State Fields */

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
		HALT_ON_ERRORCOND(0 && "Not implemented");
	}

	/* Natural-Width fields: VMCS12 host -> VMCS01 guest */
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
		HALT_ON_ERRORCOND(0 && "Not implemented");
	}
}
