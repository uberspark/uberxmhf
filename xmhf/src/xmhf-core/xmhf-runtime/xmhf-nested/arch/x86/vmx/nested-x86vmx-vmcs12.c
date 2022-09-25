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
#include "nested-x86vmx-handler2.h"
#include "nested-x86vmx-vminsterr.h"
#include "nested-x86vmx-ept12.h"

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
		return (ulong_t) vmcs12->name;
#define DECLARE_FIELD_NW(encoding, name, ...) \
	case offsetof(struct nested_vmcs12, name): \
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
		vmcs12->name = (u32) value; \
		break;
#define DECLARE_FIELD_NW_RW(encoding, name, ...) \
	case offsetof(struct nested_vmcs12, name): \
		vmcs12->name = (ulong_t) value; \
		break;
#include "nested-x86vmx-vmcs12-fields.h"
	default:
		HALT_ON_ERRORCOND(0 && "Unknown guest VMCS field");
	}
}

/* VMREAD all fields in current VMCS and put the result to vmcs12 */
void xmhf_nested_arch_x86vmx_vmcs_read_all(VCPU * vcpu,
										   struct nested_vmcs12 *vmcs12)
{
#define FIELD_CTLS_ARG (&vcpu->vmx_caps)
#define DECLARE_FIELD_16(encoding, name, prop, exist, ...) \
	if (exist) { \
		vmcs12->name = __vmx_vmread16(encoding); \
	}
#define DECLARE_FIELD_64(encoding, name, prop, exist, ...) \
	if (exist) { \
		vmcs12->name = __vmx_vmread64(encoding); \
	}
#define DECLARE_FIELD_32(encoding, name, prop, exist, ...) \
	if (exist) { \
		vmcs12->name = __vmx_vmread32(encoding); \
	}
#define DECLARE_FIELD_NW(encoding, name, prop, exist, ...) \
	if (exist) { \
		vmcs12->name = __vmx_vmreadNW(encoding); \
	}
#include "nested-x86vmx-vmcs12-fields.h"
}

/* VMWRITE all fields of current VMCS using the values from vmcs12 */
void xmhf_nested_arch_x86vmx_vmcs_write_all(VCPU * vcpu,
											struct nested_vmcs12 *vmcs12)
{
#define FIELD_CTLS_ARG (&vcpu->vmx_caps)
#define DECLARE_FIELD_16(encoding, name, prop, exist, ...) \
	if (exist) { \
		__vmx_vmwrite16(encoding, vmcs12->name); \
	}
#define DECLARE_FIELD_64(encoding, name, prop, exist, ...) \
	if (exist) { \
		__vmx_vmwrite64(encoding, vmcs12->name); \
	}
#define DECLARE_FIELD_32(encoding, name, prop, exist, ...) \
	if (exist) { \
		__vmx_vmwrite32(encoding, vmcs12->name); \
	}
#define DECLARE_FIELD_NW(encoding, name, prop, exist, ...) \
	if (exist) { \
		__vmx_vmwriteNW(encoding, vmcs12->name); \
	}
#include "nested-x86vmx-vmcs12-fields.h"
}

/* Dump all fields in vmcs12 */
void xmhf_nested_arch_x86vmx_vmcs_dump(VCPU * vcpu,
									   struct nested_vmcs12 *vmcs12,
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
#else							/* !defined(__I386__) && !defined(__AMD64__) */
#error "Unsupported Arch"
#endif							/* !defined(__I386__) && !defined(__AMD64__) */
#include "nested-x86vmx-vmcs12-fields.h"
}

/* Dump all fields in current physical VMCS (using vmread) */
void xmhf_nested_arch_x86vmx_vmread_all(VCPU * vcpu, char *prefix)
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
#else							/* !defined(__I386__) && !defined(__AMD64__) */
#error "Unsupported Arch"
#endif							/* !defined(__I386__) && !defined(__AMD64__) */
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
#else							/* !defined(__I386__) && !defined(__AMD64__) */
#error "Unsupported Arch"
#endif							/* !defined(__I386__) && !defined(__AMD64__) */
#include "nested-x86vmx-vmcs12-fields.h"
}

/*
 * Extract ctls information to ctls from selected fields in VMCS12.
 * Return an error code following VM instruction error number, or 0 when
 * success.
 */
static u32 _vmcs12_get_ctls(VCPU * vcpu, struct nested_vmcs12 *vmcs12,
							vmx_ctls_t * ctls)
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
		u32 fixed0 = vcpu->vmx_nested_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR];
		u32 fixed1 =
			vcpu->vmx_nested_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32;
		/* Check whether guest enables secondary controls */
		if (_vmx_hasctl_activate_secondary_controls(ctls)) {
			val = vmcs12->control_VMX_seccpu_based;
		}
		if (!((~val & fixed0) == 0 && (val & ~fixed1) == 0)) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		ctls->procbased_ctls2 = val;
	}
	return VM_INST_SUCCESS;
}

/*
 * Translate VMCS12 (vmcs12) to VMCS02 (already loaded as current VMCS).
 * Return an error code following VM instruction error number, or 0 when
 * success.
 */
u32 xmhf_nested_arch_x86vmx_vmcs12_to_vmcs02(VCPU * vcpu,
											 vmcs12_info_t * vmcs12_info)
{
	struct nested_vmcs12 *vmcs12 = &vmcs12_info->vmcs12_value;
	vmx_ctls_t ctls;
	guestmem_hptw_ctx_pair_t ctx_pair;
	u32 status = _vmcs12_get_ctls(vcpu, vmcs12, &ctls);
	if (status != 0) {
		return status;
	}
	guestmem_init(vcpu, &ctx_pair);
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

#define DECLARE_FIELDPAIR_16(guest_encoding, host_encoding, name) \
	{ \
		__vmx_vmwrite16(host_encoding, vcpu->vmcs.host_##name); \
	}
#define DECLARE_FIELDPAIR_64(guest_encoding, host_encoding, name) \
	{ \
		__vmx_vmwrite64(host_encoding, vcpu->vmcs.host_##name); \
	}
#define DECLARE_FIELDPAIR_32(guest_encoding, host_encoding, name) \
	{ \
		__vmx_vmwrite32(host_encoding, vcpu->vmcs.host_##name); \
	}
#define DECLARE_FIELDPAIR_NW(guest_encoding, host_encoding, name) \
	{ \
		__vmx_vmwriteNW(host_encoding, vcpu->vmcs.host_##name); \
	}
#include "nested-x86vmx-vmcs12-guesthost.h"

	/* 16-Bit Control Fields */
	{
		u16 vpid02;
		if (_vmx_hasctl_enable_vpid(&ctls)) {
			bool cache_hit;
			u16 vpid12 = vmcs12->control_vpid;
			if (vpid12 == 0) {
				return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
			}
			vpid02 = xmhf_nested_arch_x86vmx_get_vpid02(vcpu, vpid12,
														&cache_hit);
		} else {
			/*
			 * When VPID is not enabled, VMENTRY and VMEXIT in L1 should result
			 * in flushing linear and combination TLB. We simulate this effect
			 * here by setting VPID of L2 guest to the same as L1 guest
			 * (VPID = 1) and manually executing INVVPID for every VNENTRY and
			 * VMEXIT.
			 */
			vpid02 = 1;
			HALT_ON_ERRORCOND(__vmx_invvpid(VMX_INVVPID_SINGLECONTEXT, 1, 0));
		}
		__vmx_vmwrite16(VMCSENC_control_vpid, vpid02);
	}

	/* 16-Bit Guest-State Fields */

	/* 16-Bit Host-State Fields */

	/* 64-Bit Control Fields */
	/*
	 * control_VM_exit_MSR_store_address: see control_VM_exit_MSR_store_count
	 * control_VM_exit_MSR_load_address: see control_VM_exit_MSR_load_count
	 * control_VM_entry_MSR_load_address: see control_VM_entry_MSR_load_count
	 */
	{
		gpa_t addr = vmcs12->control_Executive_VMCS_pointer;
		// TODO: related to SMM, check whether this restriction makes sense
		HALT_ON_ERRORCOND(addr == 0);
#ifndef __DEBUG_QEMU__
		__vmx_vmwrite64(VMCSENC_control_Executive_VMCS_pointer,
						guestmem_gpa2spa_page(&ctx_pair, addr));
#endif							/* !__DEBUG_QEMU__ */
	}
	if (_vmx_hasctl_process_posted_interrupts(&ctls)) {
		gpa_t addr = vmcs12->control_posted_interrupt_desc_address;
		if (addr & (64 - 1)) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		__vmx_vmwrite64(VMCSENC_control_posted_interrupt_desc_address,
						guestmem_gpa2spa_size(&ctx_pair, addr, 64));
	}
	{
		/* XMHF always needs EPT, so this block is unconditional */
		spa_t ept02;
		HALT_ON_ERRORCOND(_vmx_hasctl_enable_ept(&vcpu->vmx_caps));
		if (_vmx_hasctl_enable_ept(&ctls)) {
			/* Construct shadow EPT */
			u64 eptp12 = vmcs12->control_EPT_pointer;
			gpa_t ept12;
			ept02_cache_line_t *cache_line;
			bool cache_hit;
			vmcs12_info->guest_ept_enable = 1;
			if (!xmhf_nested_arch_x86vmx_check_ept_lower_bits(eptp12, &ept12)) {
				return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
			}
			ept02 = xmhf_nested_arch_x86vmx_get_ept02(vcpu, ept12, &cache_hit,
													  &cache_line);
			vmcs12_info->guest_ept_cache_line = cache_line;
			vmcs12_info->guest_ept_root = ept12;
#ifdef __DEBUG_QEMU__
			/*
			 * Workaround a KVM bug:
			 * https://bugzilla.kernel.org/show_bug.cgi?id=216212
			 *
			 * Looks like KVM has a problem setting CR0.PG when nested guest's
			 * PDPTEs are not in guest hypervisor's EPT. So we always make sure
			 * the EPT entry for PDPTEs is available. To achieve this effect,
			 * simulating a EPT violation by calling
			 * xmhf_nested_arch_x86vmx_handle_ept02_exit() with guest2_paddr =
			 * CR3.
			 */
			if (vmcs12->guest_CR3 != 0) {
				xmhf_nested_arch_x86vmx_hardcode_ept(vcpu, cache_line,
													 vmcs12->guest_CR3);
			}
#endif							/* !__DEBUG_QEMU__ */
		} else {
			/* Guest does not use EPT, just use XMHF's EPT */
			vmcs12_info->guest_ept_enable = 0;
			ept02 = vcpu->vmcs.control_EPT_pointer;
		}
		__vmx_vmwrite64(VMCSENC_control_EPT_pointer, ept02);
	}
	if (0) {
		// Note: EPTP Switching not supported
		gpa_t addr = vmcs12->control_EPTP_list_address;
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(addr == 0);
		__vmx_vmwrite64(VMCSENC_control_EPTP_list_address,
						guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_hasctl_sub_page_write_permissions_for_ept(&ctls)) {
		// Note: Sub-page write permissions for EPT not supported
		gpa_t addr = vmcs12->control_subpage_permission_table_pointer;
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(addr == 0);
		__vmx_vmwrite64(VMCSENC_control_subpage_permission_table_pointer,
						guestmem_gpa2spa_page(&ctx_pair, addr));
	}
	if (_vmx_hasctl_activate_tertiary_controls(&ctls)) {
		// Note: Activate tertiary controls not supported
		u64 val = vmcs12->control_tertiary_proc_based_VMexec_ctls;
		// Note: likely need to sanitize input
		HALT_ON_ERRORCOND(val == 0);
		__vmx_vmwrite64(VMCSENC_control_tertiary_proc_based_VMexec_ctls, val);
	}

	/* 64-Bit Read-Only Data Field: skipped */

	/* 64-Bit Guest-State Fields */
	if (!_vmx_hasctl_enable_ept(&ctls)) {
		/*
		 * Guest does not use EPT, but XMHF uses EPT. When the guest is running
		 * in PAE mode, the guest PDPTEs need to be computed by XMHF in
		 * software. Otherwise the nested guest may triple fault.
		 */
		u32 pae = (vmcs12->guest_CR0 & CR0_PG) && (vmcs12->guest_CR4 & CR4_PAE);
#ifdef __AMD64__
		if (_vmx_hasctl_vmentry_ia_32e_mode_guest(&ctls)) {
			pae = 0;
		}
#elif !defined(__I386__)
#error "Unsupported Arch"
#endif							/* !defined(__I386__) */
		if (pae) {
			/* Walk EPT and retrieve values for guest_PDPTE* */
			u64 pdptes[4];
			u64 addr = vmcs12->guest_CR3 & ~0x1FUL;
			guestmem_copy_gp2h(&ctx_pair, 0, pdptes, addr, sizeof(pdptes));
			__vmx_vmwrite64(VMCSENC_guest_PDPTE0, pdptes[0]);
			__vmx_vmwrite64(VMCSENC_guest_PDPTE1, pdptes[1]);
			__vmx_vmwrite64(VMCSENC_guest_PDPTE2, pdptes[2]);
			__vmx_vmwrite64(VMCSENC_guest_PDPTE3, pdptes[3]);
		}
	}

	/* 64-Bit Host-State Fields */
	if (_vmx_hasctl_vmexit_load_ia32_pat(&ctls)) {
		__vmx_vmwrite64(VMCSENC_host_IA32_PAT, rdmsr64(MSR_IA32_PAT));
	}
	if (_vmx_hasctl_vmexit_load_ia32_efer(&ctls)) {
		__vmx_vmwrite64(VMCSENC_host_IA32_EFER, rdmsr64(MSR_EFER));
	}
	if (_vmx_hasctl_vmexit_load_ia32_perf_global_ctrl(&ctls)) {
		u32 eax, ebx, ecx, edx;
		cpuid(0x0, &eax, &ebx, &ecx, &edx);
		if (eax >= 0xA) {
			cpuid(0xA, &eax, &ebx, &ecx, &edx);
			if (eax & 0xffU) {
				__vmx_vmwrite64(VMCSENC_host_IA32_PERF_GLOBAL_CTRL,
								rdmsr64(IA32_PERF_GLOBAL_CTRL));
			}
		}
	}
	if (_vmx_hasctl_vmexit_load_pkrs(&ctls)) {
		__vmx_vmwrite64(VMCSENC_host_IA32_PKRS, rdmsr64(IA32_PKRS));
	}

	/* 32-Bit Control Fields */
	{
		u32 val = vmcs12->control_VMX_pin_based;
		/* Check for relationship between "NMI exiting" and "virtual NMIs" */
		vmcs12_info->guest_nmi_exiting = _vmx_hasctl_nmi_exiting(&ctls);
		vmcs12_info->guest_virtual_nmis = _vmx_hasctl_virtual_nmis(&ctls);
		if (!vmcs12_info->guest_nmi_exiting && vmcs12_info->guest_virtual_nmis) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		/*
		 * Disallow NMI injection if NMI exiting = 0.
		 * This is a limitation of XMHF. The correct behavior is to make NMI
		 * not blocked after injecting NMI. However, this requires non-trivial
		 * XMHF implementation effort. So not implemented, at least for now.
		 */
		if (!vmcs12_info->guest_nmi_exiting) {
			u32 injection = vmcs12->control_VM_entry_interruption_information;
			if (xmhf_nested_arch_x86vmx_is_interruption_nmi(injection)) {
				HALT_ON_ERRORCOND(0 && "Not supported (XMHF limitation)");
			}
		}
		/* Enable NMI exiting because needed by quiesce */
		val |= (1U << VMX_PINBASED_NMI_EXITING);
		val |= (1U << VMX_PINBASED_VIRTUAL_NMIS);
		__vmx_vmwrite32(VMCSENC_control_VMX_pin_based, val);
	}
	{
		u32 val = vmcs12->control_VMX_cpu_based;
		/*
		 * Check for relationship between "virtual NMIs" and "NMI-window
		 * exiting"
		 */
		vmcs12_info->guest_nmi_window_exiting =
			_vmx_hasctl_nmi_window_exiting(&ctls);
		if (!vmcs12_info->guest_virtual_nmis &&
			vmcs12_info->guest_nmi_window_exiting) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		/* XMHF needs to activate secondary controls because of EPT */
		val |= (1U << VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS);
		__vmx_vmwrite32(VMCSENC_control_VMX_cpu_based, val);
	}
	{
		u32 val = vmcs12->control_exception_bitmap;
		// TODO: in the future, need to merge with host's exception bitmap
		__vmx_vmwrite32(VMCSENC_control_exception_bitmap, val);
	}
	{
		u32 val = vmcs12->control_VM_exit_controls;
		/* Check the "IA-32e mode guest" bit of the guest hypervisor */
		if (val & (1U << VMX_VMEXIT_HOST_ADDRESS_SPACE_SIZE)) {
			HALT_ON_ERRORCOND(VCPU_g64(vcpu));
		} else {
			HALT_ON_ERRORCOND(!VCPU_g64(vcpu));
		}
		/*
		 * The "IA-32e mode guest" bit need to match XMHF. A mismatch can only
		 * happen when amd64 XMHF runs i386 guest hypervisor.
		 */
#ifdef __AMD64__
		val |= (1U << VMX_VMEXIT_HOST_ADDRESS_SPACE_SIZE);
#elif !defined(__I386__)
#error "Unsupported Arch"
#endif							/* !defined(__I386__) */
		__vmx_vmwrite32(VMCSENC_control_VM_exit_controls, val);
	}
	{
		__vmx_vmwrite32(VMCSENC_control_VM_exit_MSR_store_count,
						vcpu->vmcs.control_VM_exit_MSR_store_count);
		__vmx_vmwrite64(VMCSENC_control_VM_exit_MSR_store_address,
						hva2spa(vmcs12_info->vmcs02_vmexit_msr_store_area));

		/* VMX control is not checked here; will check in VMEXIT handler */
	}
	{
		__vmx_vmwrite32(VMCSENC_control_VM_exit_MSR_load_count,
						vcpu->vmcs.control_VM_exit_MSR_load_count);
		__vmx_vmwrite64(VMCSENC_control_VM_exit_MSR_load_address,
						hva2spa(vmcs12_info->vmcs02_vmexit_msr_load_area));

		/* VMX control is not checked here; will check in VMEXIT handler */
	}
	{
		u32 val = vmcs12->control_VM_entry_controls;
		__vmx_vmwrite32(VMCSENC_control_VM_entry_controls, val);
	}
	{
		u32 i;
		gva_t guest_addr = vmcs12->control_VM_entry_MSR_load_address;

		/*
		 * By default, most MSRs in L1 are not changed after VMENTRY to L2.
		 * This memcpy makes sure that XMHF managed MSRs follow this behavior.
		 */
		memcpy(vmcs12_info->vmcs02_vmentry_msr_load_area,
			   (void *)vcpu->vmx_vaddr_msr_area_guest,
			   vcpu->vmcs.control_VM_entry_MSR_load_count *
			   sizeof(msr_entry_t));
		__vmx_vmwrite32(VMCSENC_control_VM_entry_MSR_load_count,
						vcpu->vmcs.control_VM_entry_MSR_load_count);
		__vmx_vmwrite64(VMCSENC_control_VM_entry_MSR_load_address,
						hva2spa(vmcs12_info->vmcs02_vmentry_msr_load_area));

		/*
		 * According to SDM, IA32_EFER is changed as following:
		 * * IA32_EFER.LMA = "IA-32e mode guest"
		 * * If CR0.PG = 1, IA32_EFER.LME = "IA-32e mode guest"
		 */
		{
			u32 index;
			msr_entry_t *entry;
			u64 mask = (1ULL << EFER_LMA);
			if (vmcs12->guest_CR0 & CR0_PG) {
				mask |= (1ULL << EFER_LME);
			}
			if (xmhf_partition_arch_x86vmx_get_xmhf_msr(MSR_EFER, &index)) {
				entry = &vmcs12_info->vmcs02_vmentry_msr_load_area[index];
				if (_vmx_hasctl_vmentry_ia_32e_mode_guest(&ctls)) {
					entry->data |= mask;
				} else {
					entry->data &= ~mask;
				}
			} else {
				HALT_ON_ERRORCOND(0 && "MSR_EFER not found");
			}
		}

		/* Write the MSRs requested by guest */
		for (i = 0; i < vmcs12->control_VM_entry_MSR_load_count; i++) {
			u32 index;
			msr_entry_t guest_entry;
			guestmem_copy_gp2h(&ctx_pair, 0, &guest_entry,
							   guest_addr + sizeof(msr_entry_t) * i,
							   sizeof(msr_entry_t));
			if (xmhf_partition_arch_x86vmx_get_xmhf_msr(guest_entry.index,
														&index)) {
				msr_entry_t *entry =
					&vmcs12_info->vmcs02_vmentry_msr_load_area[index];
				HALT_ON_ERRORCOND(entry->index == guest_entry.index);
				entry->data = guest_entry.data;
			} else {
				if (xmhf_parteventhub_arch_x86vmx_handle_wrmsr
					(vcpu, guest_entry.index, guest_entry.data)) {
					/*
					 * Likely need to fail VMENTRY, but need to double check.
					 */
					HALT_ON_ERRORCOND(0 && "WRMSR fail, what should I do?");
				}
			}
		}
	}
	{
		u32 val = vmcs12->control_VM_entry_interruption_information;
		__vmx_vmwrite32(VMCSENC_control_VM_entry_interruption_information, val);
	}
	{
		u32 val = vmcs12->control_VM_entry_exception_errorcode;
		__vmx_vmwrite32(VMCSENC_control_VM_entry_exception_errorcode, val);
	}
	{
		u32 val = vmcs12->control_VM_entry_instruction_length;
		__vmx_vmwrite32(VMCSENC_control_VM_entry_instruction_length, val);
	}
	{
		/* Note: VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS is enabled above */
		u32 val = vmcs12->control_VMX_seccpu_based;
		/* XMHF needs the guest to run in EPT to protect memory */
		val |= (1U << VMX_SECPROCBASED_ENABLE_EPT);
		__vmx_vmwrite32(VMCSENC_control_VMX_seccpu_based, val);
	}

	/* 32-Bit Read-Only Data Fields: skipped */

	/* 32-Bit Guest-State Fields */
	{
		u32 val = vmcs12->guest_interruptibility;
		if (vmcs12_info->guest_nmi_exiting) {
			if (vmcs12_info->guest_virtual_nmis) {
				/* NMI Exiting = 1, virtual NMIs = 1 */
				vmcs12_info->guest_block_nmi = false;
			} else {
				/* NMI Exiting = 1, virtual NMIs = 0 */
				vmcs12_info->guest_block_nmi = val & (1U << 3);
			}
		} else {
			/* NMI Exiting = 0, virtual NMIs = 0, guest_block_nmi is ignored */
		}
		HALT_ON_ERRORCOND(!vmcs12_info->guest_vmcs_block_nmi_overridden);
		__vmx_vmwrite32(VMCSENC_guest_interruptibility, val);
	}

	/* 32-Bit Host-State Field */

	/* Natural-Width Control Fields */

	/* Natural-Width Read-Only Data Fields: skipped */

	/* Natural-Width Guest-State Fields */

	/* Natural-Width Host-State Fields */
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

	return VM_INST_SUCCESS;
}

/*
 * Translate VMCS02 (already loaded as current VMCS) to VMCS12 (vmcs12)
 */
void xmhf_nested_arch_x86vmx_vmcs02_to_vmcs12(VCPU * vcpu,
											  vmcs12_info_t * vmcs12_info)
{
	struct nested_vmcs12 *vmcs12 = &vmcs12_info->vmcs12_value;
	vmx_ctls_t ctls;
	guestmem_hptw_ctx_pair_t ctx_pair;
	HALT_ON_ERRORCOND(_vmcs12_get_ctls(vcpu, vmcs12, &ctls) == 0);
	guestmem_init(vcpu, &ctx_pair);

#define FIELD_CTLS_ARG (&ctls)
#define DECLARE_FIELD_16(encoding, name, prop, exist, ...) \
	if (exist) { \
		if (prop & FIELD_PROP_ID_GUEST) { \
			if (prop & FIELD_PROP_SWWRONLY) { \
				HALT_ON_ERRORCOND(vmcs12->name == __vmx_vmread16(encoding)); \
			} else { \
				vmcs12->name = __vmx_vmread16(encoding); \
			} \
		} \
	}
#define DECLARE_FIELD_64(encoding, name, prop, exist, ...) \
	if (exist) { \
		if ((prop & FIELD_PROP_ID_GUEST) || (prop & FIELD_PROP_GPADDR)) { \
			if (prop & FIELD_PROP_SWWRONLY) { \
				/* Note: currently for FIELD_PROP_GPADDR, assuming spa=gpa */ \
				HALT_ON_ERRORCOND(vmcs12->name == __vmx_vmread64(encoding)); \
			} else { \
				vmcs12->name = __vmx_vmread64(encoding); \
			} \
		} \
	}
#define DECLARE_FIELD_32(encoding, name, prop, exist, ...) \
	if (exist) { \
		if (prop & FIELD_PROP_ID_GUEST) { \
			if (prop & FIELD_PROP_SWWRONLY) { \
				HALT_ON_ERRORCOND(vmcs12->name == __vmx_vmread32(encoding)); \
			} else { \
				vmcs12->name = __vmx_vmread32(encoding); \
			} \
		} \
	}
#define DECLARE_FIELD_NW(encoding, name, prop, exist, ...) \
	if (exist) { \
		if (prop & FIELD_PROP_ID_GUEST) { \
			if (prop & FIELD_PROP_SWWRONLY) { \
				HALT_ON_ERRORCOND(vmcs12->name == __vmx_vmreadNW(encoding)); \
			} else { \
				vmcs12->name = __vmx_vmreadNW(encoding); \
			} \
		} \
	}
#include "nested-x86vmx-vmcs12-fields.h"

#define DECLARE_FIELDPAIR_16(guest_encoding, host_encoding, name) \
	{ \
		HALT_ON_ERRORCOND(__vmx_vmread16(host_encoding) == vcpu->vmcs.host_##name); \
		vcpu->vmcs.guest_##name = vmcs12->host_##name; \
	}
#define DECLARE_FIELDPAIR_64(guest_encoding, host_encoding, name) \
	{ \
		HALT_ON_ERRORCOND(__vmx_vmread64(host_encoding) == vcpu->vmcs.host_##name); \
		vcpu->vmcs.guest_##name = vmcs12->host_##name; \
	}
#define DECLARE_FIELDPAIR_32(guest_encoding, host_encoding, name) \
	{ \
		HALT_ON_ERRORCOND(__vmx_vmread32(host_encoding) == vcpu->vmcs.host_##name); \
		vcpu->vmcs.guest_##name = vmcs12->host_##name; \
	}
#define DECLARE_FIELDPAIR_NW(guest_encoding, host_encoding, name) \
	{ \
		HALT_ON_ERRORCOND(__vmx_vmreadNW(host_encoding) == vcpu->vmcs.host_##name); \
		vcpu->vmcs.guest_##name = vmcs12->host_##name; \
	}
#include "nested-x86vmx-vmcs12-guesthost.h"

	/* 16-Bit Control Fields */
	{
		u16 vpid02;
		if (_vmx_hasctl_enable_vpid(&ctls)) {
			bool cache_hit;
			u16 vpid12 = vmcs12->control_vpid;
			HALT_ON_ERRORCOND(vpid12 != 0);
			vpid02 = xmhf_nested_arch_x86vmx_get_vpid02(vcpu, vpid12,
														&cache_hit);
			HALT_ON_ERRORCOND(cache_hit);
		} else {
			/*
			 * When VPID is not enabled, VMENTRY and VMEXIT in L1 should result
			 * in flushing linear and combination TLB. We simulate this effect
			 * here by setting VPID of L2 guest to the same as L1 guest
			 * (VPID = 1) and manually executing INVVPID for every VNENTRY and
			 * VMEXIT.
			 */
			vpid02 = 1;
			HALT_ON_ERRORCOND(__vmx_invvpid(VMX_INVVPID_SINGLECONTEXT, 1, 0));
		}
		HALT_ON_ERRORCOND(__vmx_vmread16(VMCSENC_control_vpid) == vpid02);
	}

	/* 16-Bit Guest-State Fields */

	/* 16-Bit Host-State Fields */

	/* 16-Bit fields: VMCS12 host -> VMCS01 guest */
	{
		/*
		 * SDM volume 3 26.5.2 "Loading Host Segment and Descriptor-Table
		 * Registers": "the selector is cleared to 0000H".
		 */
		vcpu->vmcs.guest_LDTR_selector = 0x0000U;
	}

	/* 64-Bit Control Fields */
	/*
	 * control_VM_exit_MSR_store_address: see control_VM_exit_MSR_store_count
	 * control_VM_exit_MSR_load_address: see control_VM_exit_MSR_load_count
	 * control_VM_entry_MSR_load_address: see control_VM_entry_MSR_load_count
	 */
	{
		// TODO: related to SMM, check whether this restriction makes sense
#ifndef __DEBUG_QEMU__
		u16 encoding = VMCSENC_control_Executive_VMCS_pointer;
		HALT_ON_ERRORCOND(__vmx_vmread64(encoding) == 0);
#endif							/* !__DEBUG_QEMU__ */
		// vmcs12->control_Executive_VMCS_pointer = ...;
	}
	if (_vmx_hasctl_process_posted_interrupts(&ctls)) {
		u16 encoding = VMCSENC_control_posted_interrupt_desc_address;
		/* Note: currently assuming spa=gpa */
		HALT_ON_ERRORCOND(vmcs12->control_posted_interrupt_desc_address ==
						  __vmx_vmread64(encoding));
	}
	{
		/* XMHF always needs EPT, so this block is unconditional */
		spa_t ept02;
		u16 encoding = VMCSENC_control_EPT_pointer;
		HALT_ON_ERRORCOND(_vmx_hasctl_enable_ept(&vcpu->vmx_caps));
		if (_vmx_hasctl_enable_ept(&ctls)) {
			gpa_t ept12 = vmcs12_info->guest_ept_root;
			ept02_cache_line_t *cache_line;
			bool cache_hit;
			ept02 = xmhf_nested_arch_x86vmx_get_ept02(vcpu, ept12, &cache_hit,
													  &cache_line);
			HALT_ON_ERRORCOND(cache_hit);
		} else {
			ept02 = vcpu->vmcs.control_EPT_pointer;
		}
		HALT_ON_ERRORCOND(__vmx_vmread64(encoding) == ept02);
		/* vmcs12->control_EPT_pointer is ignored here */
	}
	if (0) {
		// Note: EPTP Switching not supported
		// Note: likely need to sanitize input
		u16 encoding = VMCSENC_control_EPTP_list_address;
		HALT_ON_ERRORCOND(__vmx_vmread64(encoding) == 0);
		// vmcs12->control_EPTP_list_address = ...
	}
	if (_vmx_hasctl_sub_page_write_permissions_for_ept(&ctls)) {
		// Note: Sub-page write permissions for EPT not supported
		// Note: likely need to sanitize input
		u16 encoding = VMCSENC_control_subpage_permission_table_pointer;
		HALT_ON_ERRORCOND(__vmx_vmread64(encoding) == 0);
		// vmcs12->control_subpage_permission_table_pointer = ...
	}
	if (_vmx_hasctl_activate_tertiary_controls(&ctls)) {
		// Note: Activate tertiary controls not supported
		// Note: likely need to sanitize input
		u16 encoding = VMCSENC_control_tertiary_proc_based_VMexec_ctls;
		HALT_ON_ERRORCOND(__vmx_vmread64(encoding) == 0);
		// vmcs12->control_tertiary_proc_based_VMexec_ctls = ...
	}

	/* 64-Bit Read-Only Data Field */

	/* 64-Bit Guest-State Fields */

	/* 64-Bit Host-State Fields */
	if (_vmx_hasctl_vmexit_load_ia32_pat(&ctls)) {
		HALT_ON_ERRORCOND(__vmx_vmread64(VMCSENC_host_IA32_PAT) ==
						  rdmsr64(MSR_IA32_PAT));
	}
	if (_vmx_hasctl_vmexit_load_ia32_efer(&ctls)) {
		HALT_ON_ERRORCOND(__vmx_vmread64(VMCSENC_host_IA32_EFER) ==
						  rdmsr64(MSR_EFER));
	}
	if (_vmx_hasctl_vmexit_load_ia32_perf_global_ctrl(&ctls)) {
		u32 eax, ebx, ecx, edx;
		cpuid(0x0, &eax, &ebx, &ecx, &edx);
		if (eax >= 0xA) {
			cpuid(0xA, &eax, &ebx, &ecx, &edx);
			if (eax & 0xffU) {
				u16 encoding = VMCSENC_host_IA32_PERF_GLOBAL_CTRL;
				HALT_ON_ERRORCOND(__vmx_vmread64(encoding) ==
								  rdmsr64(IA32_PERF_GLOBAL_CTRL));
			}
		}
	}
	if (_vmx_hasctl_vmexit_load_pkrs(&ctls)) {
		HALT_ON_ERRORCOND(__vmx_vmread64(VMCSENC_host_IA32_PKRS) ==
						  rdmsr64(IA32_PKRS));
	}

	/* 64-Bit fields: VMCS12 host -> VMCS01 guest */
	{
		/* The IA32_DEBUGCTL MSR is cleared to 00000000_00000000H */
		vcpu->vmcs.guest_IA32_DEBUGCTL = 0ULL;
	}
	if (_vmx_hasctl_vmexit_load_ia32_pat(&ctls)) {
		wrmsr64(MSR_IA32_PAT, __vmx_vmread64(VMCSENC_host_IA32_PAT));
	}
	if (_vmx_hasctl_vmexit_load_ia32_efer(&ctls)) {
		wrmsr64(MSR_EFER, __vmx_vmread64(VMCSENC_host_IA32_EFER));
	}
	if (_vmx_hasctl_vmexit_load_ia32_perf_global_ctrl(&ctls)) {
		u32 eax, ebx, ecx, edx;
		cpuid(0x0, &eax, &ebx, &ecx, &edx);
		if (eax >= 0xA) {
			cpuid(0xA, &eax, &ebx, &ecx, &edx);
			if (eax & 0xffU) {
				wrmsr64(IA32_PERF_GLOBAL_CTRL,
						__vmx_vmread64(VMCSENC_host_IA32_PERF_GLOBAL_CTRL));
			}
		}
	}
	if (_vmx_hasctl_vmexit_load_pkrs(&ctls)) {
		wrmsr64(IA32_PKRS, __vmx_vmread64(VMCSENC_host_IA32_PKRS));
	}

	/* 32-Bit Control Fields */
	{
		u32 val = vmcs12->control_VMX_pin_based;
		/* Enable NMI exiting because needed by quiesce */
		val |= (1U << VMX_PINBASED_NMI_EXITING);
		val |= (1U << VMX_PINBASED_VIRTUAL_NMIS);
		HALT_ON_ERRORCOND(val == __vmx_vmread32(VMCSENC_control_VMX_pin_based));
	}
	{
		u32 val12 = vmcs12->control_VMX_cpu_based;
		u32 val02 = __vmx_vmread32(VMCSENC_control_VMX_cpu_based);
		/* Secondary controls are always required in VMCS02 for EPT */
		val12 |= (1U << VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS);
		/* NMI window exiting may change due to L0 */
		val12 &= ~(1U << VMX_PROCBASED_NMI_WINDOW_EXITING);
		val02 &= ~(1U << VMX_PROCBASED_NMI_WINDOW_EXITING);
		HALT_ON_ERRORCOND(val12 == val02);
	}
	{
		// TODO: in the future, need to merge with host's exception bitmap
		u32 val = vmcs12->control_exception_bitmap;
		u16 encoding = VMCSENC_control_exception_bitmap;
		HALT_ON_ERRORCOND(val == __vmx_vmread32(encoding));
	}
	{
		u32 val = vmcs12->control_VM_exit_controls;
		u16 encoding = VMCSENC_control_VM_exit_controls;
		/*
		 * The "IA-32e mode guest" bit need to match XMHF. A mismatch can only
		 * happen when amd64 XMHF runs i386 guest hypervisor.
		 */
#ifdef __AMD64__
		val |= (1U << VMX_VMEXIT_HOST_ADDRESS_SPACE_SIZE);
#elif !defined(__I386__)
#error "Unsupported Arch"
#endif							/* !defined(__I386__) */
		HALT_ON_ERRORCOND(val == __vmx_vmread32(encoding));
	}
	{
		u32 i;
		gva_t guest_addr = vmcs12->control_VM_exit_MSR_store_address;

		/* VMCS02 needs to always process the same MSRs as VMCS01 */
		u16 encoding = VMCSENC_control_VM_exit_MSR_store_count;
		HALT_ON_ERRORCOND(vcpu->vmcs.control_VM_exit_MSR_store_count ==
						  __vmx_vmread32(encoding));
		encoding = VMCSENC_control_VM_exit_MSR_store_address;
		HALT_ON_ERRORCOND(hva2spa(vmcs12_info->vmcs02_vmexit_msr_store_area) ==
						  __vmx_vmread64(encoding));

		/* Read MSRs and write to guest */
		for (i = 0; i < vmcs12->control_VM_exit_MSR_store_count; i++) {
			u32 index;
			msr_entry_t guest_entry;
			guestmem_copy_gp2h(&ctx_pair, 0, &guest_entry,
							   guest_addr + sizeof(msr_entry_t) * i,
							   sizeof(msr_entry_t));
			if (xmhf_partition_arch_x86vmx_get_xmhf_msr(guest_entry.index,
														&index)) {
				msr_entry_t *entry =
					&vmcs12_info->vmcs02_vmexit_msr_store_area[index];
				HALT_ON_ERRORCOND(entry->index == guest_entry.index);
				guest_entry.data = entry->data;
			} else {
				if (xmhf_parteventhub_arch_x86vmx_handle_rdmsr
					(vcpu, guest_entry.index, &guest_entry.data)) {
					/*
					 * Likely need to fail VMEXIT, but need to double check.
					 */
					HALT_ON_ERRORCOND(0 && "RDMSR fail, what should I do?");
				}
			}
			guestmem_copy_h2gp(&ctx_pair, 0,
							   guest_addr + sizeof(msr_entry_t) * i,
							   &guest_entry, sizeof(msr_entry_t));
		}
	}
	{
		u32 i;
		gva_t guest_addr = vmcs12->control_VM_exit_MSR_load_address;

		/* VMCS02 needs to always process the same MSRs as VMCS01 */
		u16 encoding = VMCSENC_control_VM_exit_MSR_store_count;
		HALT_ON_ERRORCOND(vcpu->vmcs.control_VM_exit_MSR_load_count ==
						  __vmx_vmread32(encoding));
		encoding = VMCSENC_control_VM_exit_MSR_load_address;
		HALT_ON_ERRORCOND(hva2spa(vmcs12_info->vmcs02_vmexit_msr_load_area) ==
						  __vmx_vmread64(encoding));

		/*
		 * By default, most MSRs in L2 are not changed after VMEXIT to L1.
		 * This memcpy makes sure that XMHF managed MSRs follow this behavior.
		 */
		memcpy((void *)vcpu->vmx_vaddr_msr_area_guest,
			   vmcs12_info->vmcs02_vmentry_msr_load_area,
			   vcpu->vmcs.control_VM_entry_MSR_load_count *
			   sizeof(msr_entry_t));

		/*
		 * According to SDM, IA32_EFER is changed as following:
		 * * IA32_EFER.LMA = "host address-space size"
		 * * IA32_EFER.LME = "host address-space size"
		 */
		{
			u32 index;
			msr_entry_t *entry;
			u64 mask = (1ULL << EFER_LMA) | (1ULL << EFER_LME);
			if (xmhf_partition_arch_x86vmx_get_xmhf_msr(MSR_EFER, &index)) {
				entry =
					&((msr_entry_t *) vcpu->vmx_vaddr_msr_area_guest)[index];
				if (_vmx_hasctl_vmexit_host_address_space_size(&ctls)) {
					entry->data |= mask;
				} else {
					entry->data &= ~mask;
				}
			} else {
				HALT_ON_ERRORCOND(0 && "MSR_EFER not found");
			}
		}

		/* Write MSRs as requested by guest */
		for (i = 0; i < vmcs12->control_VM_exit_MSR_load_count; i++) {
			u32 index;
			msr_entry_t guest_entry;
			guestmem_copy_gp2h(&ctx_pair, 0, &guest_entry,
							   guest_addr + sizeof(msr_entry_t) * i,
							   sizeof(msr_entry_t));
			if (xmhf_partition_arch_x86vmx_get_xmhf_msr(guest_entry.index,
														&index)) {
				msr_entry_t *entry =
					&((msr_entry_t *) vcpu->vmx_vaddr_msr_area_guest)[index];
				HALT_ON_ERRORCOND(entry->index == guest_entry.index);
				entry->data = guest_entry.data;
			} else {
				if (xmhf_parteventhub_arch_x86vmx_handle_wrmsr
					(vcpu, guest_entry.index, guest_entry.data)) {
					/*
					 * Likely need to fail VMEXIT, but need to double check.
					 */
					HALT_ON_ERRORCOND(0 && "WRMSR fail, what should I do?");
				}
			}
		}
	}
	{
		u32 val = __vmx_vmread32(VMCSENC_control_VM_entry_controls);
		/* mask is bits that cannot change */
		u32 mask = ~(1U << VMX_VMENTRY_IA_32E_MODE_GUEST);
		HALT_ON_ERRORCOND((vmcs12->control_VM_entry_controls & mask) ==
						  (val & mask));
		vmcs12->control_VM_entry_controls = val;
	}
	{
		/* VMCS02 needs to always process the same MSRs as VMCS01 */
		u16 encoding = VMCSENC_control_VM_entry_MSR_load_count;
		HALT_ON_ERRORCOND(vcpu->vmcs.control_VM_entry_MSR_load_count ==
						  __vmx_vmread32(encoding));
		encoding = VMCSENC_control_VM_entry_MSR_load_address;
		HALT_ON_ERRORCOND(hva2spa(vmcs12_info->vmcs02_vmentry_msr_load_area)
						  == __vmx_vmread64(encoding));
	}
	{
		/*
		 * control_VM_entry_interruption_information may be changed in VMCS02
		 * for nested virtualization operations, so do not copy to VMCS12.
		 * Just clear bit 31 of VMCS12 as required by SDM.
		 */
		vmcs12->control_VM_entry_interruption_information &=
			~INTR_INFO_VALID_MASK;
	}
	/*
	 * control_VM_entry_exception_errorcode and
	 * control_VM_entry_instruction_length may be changed in VMCS02 for nested
	 * virtualization operations, so do not copy to VMCS12. Just leave the
	 * values in VMCS12 unchanged.
	 */
	{
		/* Note: VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS is always enabled */
		u32 val = vmcs12->control_VMX_seccpu_based;
		u16 encoding = VMCSENC_control_VMX_seccpu_based;
		/* XMHF needs the guest to run in EPT to protect memory */
		val |= (1U << VMX_SECPROCBASED_ENABLE_EPT);
		HALT_ON_ERRORCOND(val == __vmx_vmread32(encoding));
	}

	/* 32-Bit Read-Only Data Fields */

	/* 32-Bit Guest-State Fields */
	{
		/* Handle "Blocking by NMI" */
		u32 val = __vmx_vmread32(VMCSENC_guest_interruptibility);
		if (vmcs12_info->guest_vmcs_block_nmi_overridden) {
			vmcs12_info->guest_vmcs_block_nmi_overridden = false;
			if (vmcs12_info->guest_vmcs_block_nmi) {
				val |= (1U << 3);
			} else {
				val &= ~(1U << 3);
			}
		}
		if (vmcs12_info->guest_nmi_exiting) {
			/* Copy guest NMI blocking to host (VMCS01) */
			if (vmcs12_info->guest_block_nmi) {
				vcpu->vmcs.guest_interruptibility |= (1U << 3);
			} else {
				vcpu->vmcs.guest_interruptibility &= ~(1U << 3);
			}
			/* Set guest interruptibility state in VMCS12 */
			if (!vmcs12_info->guest_virtual_nmis) {
				if (vmcs12_info->guest_block_nmi) {
					val |= (1U << 3);
				} else {
					val &= ~(1U << 3);
				}
			}
		} else {
			/* Copy guest NMI blocking to host (VMCS01) */
			if (val & (1U << 3)) {
				vcpu->vmcs.guest_interruptibility |= (1U << 3);
			} else {
				vcpu->vmcs.guest_interruptibility &= ~(1U << 3);
			}
		}
		vmcs12->guest_interruptibility = val;
		/* There is no blocking by STI or by MOV SS after a VM exit */
		vcpu->vmcs.guest_interruptibility &= ~((1U << 0) | (1U << 1));
	}

	/* 32-Bit Host-State Field */

	/* 32-Bit fields: VMCS12 host -> VMCS01 guest */
	{
		/* Undefined if the segment is unusable; otherwise, set to FFFFFFFFH */
		vcpu->vmcs.guest_ES_limit = 0xffffffff;
	}
	{
		/* The segment limit is set as follows: CS. Set to FFFFFFFFH */
		vcpu->vmcs.guest_CS_limit = 0xffffffff;
	}
	{
		/* Undefined if the segment is unusable; otherwise, set to FFFFFFFFH */
		vcpu->vmcs.guest_SS_limit = 0xffffffff;
	}
	{
		/* Undefined if the segment is unusable; otherwise, set to FFFFFFFFH */
		vcpu->vmcs.guest_DS_limit = 0xffffffff;
	}
	{
		/* Undefined if the segment is unusable; otherwise, set to FFFFFFFFH */
		vcpu->vmcs.guest_FS_limit = 0xffffffff;
	}
	{
		/* Undefined if the segment is unusable; otherwise, set to FFFFFFFFH */
		vcpu->vmcs.guest_GS_limit = 0xffffffff;
	}
	{
		/* Undefined */
		vcpu->vmcs.guest_LDTR_limit = 0x0;
	}
	{
		/* Set to 00000067H */
		vcpu->vmcs.guest_TR_limit = 0x67;
	}
	{
		/* Set to FFFFH */
		vcpu->vmcs.guest_GDTR_limit = 0xffff;
	}
	{
		/* Set to FFFFH */
		vcpu->vmcs.guest_IDTR_limit = 0xffff;
	}
	{
		/* Type=3, S=1, DPL=0, P=1, D/B=1, G=1 */
		u32 mask = (0xfU << 0) | (1U << 4) | (3U << 5) | (1U << 7) |
				   (1U << 14) | (1U << 15);
		u32 val = (3U << 0) | (1U << 4) | (1U << 7) | (1U << 14) | (1U << 15);
		vcpu->vmcs.guest_ES_access_rights =
			(vcpu->vmcs.guest_ES_access_rights & ~mask) | val;
	}
	{
		/*
		 * Type=11, S=1, DPL=0, P=1, L="host address-space size",
		 * D/B=!"host address-space size", G=1.
		 */
		u32 mask = (0xfU << 0) | (1U << 4) | (3U << 5) | (1U << 7) |
				   (1U << 13) | (1U << 14) | (1U << 15);
		u32 val = (11U << 0) | (1U << 4) | (1U << 7) | (1U << 15);
		if (_vmx_hasctl_vmexit_host_address_space_size(&ctls)) {
			val |= (1U << 13);
		} else {
			val |= (1U << 14);
		}
		vcpu->vmcs.guest_CS_access_rights =
			(vcpu->vmcs.guest_CS_access_rights & ~mask) | val;
	}
	{
		/* Type=3, S=1, DPL=0, P=1, D/B=1, G=1 */
		u32 mask = (0xfU << 0) | (1U << 4) | (3U << 5) | (1U << 7) |
				   (1U << 14) | (1U << 15);
		u32 val = (3U << 0) | (1U << 4) | (1U << 7) | (1U << 14) | (1U << 15);
		vcpu->vmcs.guest_SS_access_rights =
			(vcpu->vmcs.guest_SS_access_rights & ~mask) | val;
	}
	{
		/* Type=3, S=1, DPL=0, P=1, D/B=1, G=1 */
		u32 mask = (0xfU << 0) | (1U << 4) | (3U << 5) | (1U << 7) |
				   (1U << 14) | (1U << 15);
		u32 val = (3U << 0) | (1U << 4) | (1U << 7) | (1U << 14) | (1U << 15);
		vcpu->vmcs.guest_DS_access_rights =
			(vcpu->vmcs.guest_DS_access_rights & ~mask) | val;
	}
	{
		/* Type=3, S=1, DPL=0, P=1, D/B=1, G=1 */
		u32 mask = (0xfU << 0) | (1U << 4) | (3U << 5) | (1U << 7) |
				   (1U << 14) | (1U << 15);
		u32 val = (3U << 0) | (1U << 4) | (1U << 7) | (1U << 14) | (1U << 15);
		vcpu->vmcs.guest_FS_access_rights =
			(vcpu->vmcs.guest_FS_access_rights & ~mask) | val;
	}
	{
		/* Type=3, S=1, DPL=0, P=1, D/B=1, G=1 */
		u32 mask = (0xfU << 0) | (1U << 4) | (3U << 5) | (1U << 7) |
				   (1U << 14) | (1U << 15);
		u32 val = (3U << 0) | (1U << 4) | (1U << 7) | (1U << 14) | (1U << 15);
		vcpu->vmcs.guest_GS_access_rights =
			(vcpu->vmcs.guest_GS_access_rights & ~mask) | val;
	}
	{
		/* Unusable */
		vcpu->vmcs.guest_LDTR_access_rights = (1U << 16);
	}
	{
		/* Type=11, S=0, DPL=0, P=1, D/B=0, G=0 */
		u32 mask = (0xfU << 0) | (1U << 4) | (3U << 5) | (1U << 7) |
				   (1U << 14) | (1U << 15);
		u32 val = (11U << 0) | (1U << 7);
		vcpu->vmcs.guest_TR_access_rights =
			(vcpu->vmcs.guest_TR_access_rights & ~mask) | val;
	}

	/* Natural-Width Control Fields */

	/* Natural-Width Read-Only Data Fields */

	/* Natural-Width Guest-State Fields */

	/* Natural-Width Host-State Fields */
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
	{
		/*
		 * CR4.PAE is set to 1 if the "host address-space size" VM-exit control
		 * is 1. CR4.PCIDE is set to 0 if the “host address-space size” VM-exit
		 * control is 0.
		 */
		if (_vmx_hasctl_vmexit_host_address_space_size(&ctls)) {
			vcpu->vmcs.guest_CR4 |= CR4_PAE;
		} else {
			vcpu->vmcs.guest_CR4 &= ~CR4_PCIDE;
		}
	}
	{
		/* Undefined if the segment is unusable; otherwise, cleared to zero */
		vcpu->vmcs.guest_ES_base = 0;
	}
	{
		/* The base address is set as follows: CS. Cleared to zero */
		vcpu->vmcs.guest_CS_base = 0;
	}
	{
		/* Undefined if the segment is unusable; otherwise, cleared to zero */
		vcpu->vmcs.guest_SS_base = 0;
	}
	{
		/* Undefined if the segment is unusable; otherwise, cleared to zero */
		vcpu->vmcs.guest_DS_base = 0;
	}
	{
		/* Undefined */
		vcpu->vmcs.guest_LDTR_base = 0;
	}
	{
		/* DR7 is set to 400H */
		vcpu->vmcs.guest_DR7 = 0x400UL;
	}
	{
		/* RFLAGS is cleared, except bit 1, which is always set */
		vcpu->vmcs.guest_RFLAGS = (1UL << 1);
	}
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

#ifdef __DEBUG_QEMU__
/*
 * Check whether VMCS fields exist as specified in the SDM. Return true if
 * everything is well.
 */
bool xmhf_nested_arch_x86vmx_check_fields_existence(VCPU * vcpu)
{
	bool success;
	printf("CPU(0x%02x): %s() is checking VMCS fields\n", vcpu->id, __func__);
#define FIELD_CTLS_ARG (&vcpu->vmx_caps)
#define DECLARE_FIELD_16(encoding, name, prop, exist, ...) \
	{ \
		unsigned long value; \
		bool actual = !!__vmx_vmread(encoding, &value); \
		bool expected = !!exist; \
		if (actual != expected) { \
			printf("CPU(0x%02x): Warning: unexpected field existence: " \
				   "encoding=0x%04x, expected=%u, actual=%u, name=%s\n", \
				   vcpu->id, (u32) encoding, (u32) expected, (u32) actual, \
				   #name); \
			success = false; \
		} \
	}
#define DECLARE_FIELD_64(...) DECLARE_FIELD_16(__VA_ARGS__)
#define DECLARE_FIELD_32(...) DECLARE_FIELD_16(__VA_ARGS__)
#define DECLARE_FIELD_NW(...) DECLARE_FIELD_16(__VA_ARGS__)
#include "nested-x86vmx-vmcs12-fields.h"
	return success;
}
#endif							/* !__DEBUG_QEMU__ */
