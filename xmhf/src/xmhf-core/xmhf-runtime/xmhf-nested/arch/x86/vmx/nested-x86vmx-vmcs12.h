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

// nested-x86vmx-vmcs12.h
// Handle VMCS in the guest
// author: Eric Li (xiaoyili@andrew.cmu.edu)

#ifndef _NESTED_X86VMX_VMCS12_H_
#define _NESTED_X86VMX_VMCS12_H_

#include "nested-x86vmx-ept12.h"

/*
 * Rules:
 * * Exactly one bit should be set in mask 0xf
 * * At most one bit should be set in mask 0x1f0
 * * FIELD_PROP_GPADDR (0x20) can only be set for 64-bit fields
 * * FIELD_PROP_SWWRONLY (0x200) can only be set when 0x10 or 0x20 is set
 * Notes:
 * * FIELD_PROP_ID_HOST is implicitly ignored. nested-x86vmx-vmcs12-guesthost.h
 *   is used instead.
 * * Fields marked as FIELD_PROP_UNSUPP cannot be computed as exist.
 */
#define FIELD_PROP_GUEST	0x00000001	/* Guest field */
#define FIELD_PROP_HOST		0x00000002	/* Host field */
#define FIELD_PROP_CTRL		0x00000004	/* Control field */
#define FIELD_PROP_RO		0x00000008	/* Read-only field */
#define FIELD_PROP_ID_GUEST	0x00000010	/* VMCS12 value = VMCS02 value = any */
#define FIELD_PROP_GPADDR	0x00000020	/* VMCS12 value = VMCS02 value = gpa */
#define FIELD_PROP_ID_HOST	0x00000040	/* VMCS12 value = VMCS01 value */
#define FIELD_PROP_IGNORE	0x00000080	/* VMCS12 value is ignored */
#define FIELD_PROP_UNSUPP	0x00000100	/* VMCS12 field is not supported */
#define FIELD_PROP_SWWRONLY	0x00000200	/* Read-only by hardware */

/*
 * Control whether XMHF (L0) uses shadow VMCS if provided by hardware.
 * Ideally this should be a configuration option, but not implemented yet.
 */
#define VMX_NESTED_USE_SHADOW_VMCS

/*
 * Maximum number of MSRs in VMCS02's VMENTRY/VMEXIT MSR load / store. This
 * value only needs to be larger than or equal to vmx_msr_area_msrs_count.
 * It is not related to VMCS12's MSR load/store.
 */
#define VMX_NESTED_MAX_MSR_COUNT 8

/*
 * Maximum number of active VMCS per CPU. If this number is exceeded, XMHF will
 * halt.
 */
#define VMX_NESTED_MAX_ACTIVE_VMCS 8

/* Format of an active VMCS12 tracked by a CPU */
typedef struct vmcs12_info {
	/* Index of this VMCS12 in the CPU */
	u32 index;
	/*
	 * Pointer to VMCS12 in guest.
	 *
	 * When a VMCS is invalid, this field is CUR_VMCS_PTR_INVALID, and all
	 * other fields are undefined.
	 */
	gpa_t vmcs12_ptr;
	/* Pointer to VMCS02 in host */
	spa_t vmcs02_ptr;
#ifdef VMX_NESTED_USE_SHADOW_VMCS
	/* Pointer to shadow VMCS12 in host */
	spa_t vmcs12_shadow_ptr;
#endif							/* VMX_NESTED_USE_SHADOW_VMCS */
	/* Whether this VMCS has launched */
	int launched;
	/* Content of VMCS12, stored in XMHF's format */
	struct _vmx_vmcsfields vmcs12_value;
	/* VMEXIT MSR store area */
	msr_entry_t vmcs02_vmexit_msr_store_area[VMX_NESTED_MAX_MSR_COUNT]
		__attribute__((aligned(16)));
	/* VMEXIT MSR load area */
	msr_entry_t vmcs02_vmexit_msr_load_area[VMX_NESTED_MAX_MSR_COUNT]
		__attribute__((aligned(16)));
	/* VMENTRY MSR load area */
	msr_entry_t vmcs02_vmentry_msr_load_area[VMX_NESTED_MAX_MSR_COUNT]
		__attribute__((aligned(16)));
	/* Whether using EPT12 */
	int guest_ept_enable;
	/*
	 * When guest_ept_enable, EPT02 cache line.
	 *
	 * This variable can be asynchronously invalidated when another CPU's EPT01
	 * changes. So use xmhf_nested_arch_x86vmx_block_ept02_flush() to protect
	 * it when accessing.
	 */
	ept02_cache_line_t *guest_ept_cache_line;
	/* When guest_ept_enable, pointer to EPT12 root */
	gpa_t guest_ept_root;
	/* "NMI exiting" in VMCS */
	bool guest_nmi_exiting;
	/* "Virtual NMIs" in VMCS */
	bool guest_virtual_nmis;
	/* "NMI-window exiting" in VMCS */
	bool guest_nmi_window_exiting;
	/*
	 * When "NMI exiting" = 1, whether the guest is blocking NMIs.
	 * Note: when "NMI exiting" = 0, this field is undefined. Use guest
	 * interruptibility field in VMCS02.
	 */
	bool guest_block_nmi;
	/*
	 * If true, guest_vmcs_block_nmi contains the original L2 NMI blocking bit.
	 * If false, L2 NMI blocking bit is in VMCS02 guest interruptibility field.
	 */
	bool guest_vmcs_block_nmi_overridden;
	/* L2 NMI blocking bit if guest_vmcs_block_nmi_overridden is true */
	bool guest_vmcs_block_nmi;
	/* During L2 operation, control information in VMCS12 */
	vmx_ctls_t ctls12;
} vmcs12_info_t;

size_t xmhf_nested_arch_x86vmx_vmcs_field_find(ulong_t encoding);
int xmhf_nested_arch_x86vmx_vmcs_writable(size_t offset);
ulong_t xmhf_nested_arch_x86vmx_vmcs_read(struct _vmx_vmcsfields *vmcs12,
										  size_t offset, size_t size);
void xmhf_nested_arch_x86vmx_vmcs_write(struct _vmx_vmcsfields *vmcs12,
										size_t offset, ulong_t value,
										size_t size);
void xmhf_nested_arch_x86vmx_vmcs_read_all(VCPU * vcpu,
										   struct _vmx_vmcsfields *vmcs12);
void xmhf_nested_arch_x86vmx_vmcs_write_all(VCPU * vcpu,
											struct _vmx_vmcsfields *vmcs12);
void xmhf_nested_arch_x86vmx_vmcs_dump(VCPU * vcpu,
									   struct _vmx_vmcsfields *vmcs12,
									   char *prefix);
void xmhf_nested_arch_x86vmx_vmread_all(VCPU * vcpu, char *prefix);
u32 xmhf_nested_arch_x86vmx_vmcs12_to_vmcs02(VCPU * vcpu,
											 vmcs12_info_t * vmcs12_info);
void xmhf_nested_arch_x86vmx_vmcs02_to_vmcs12(VCPU * vcpu,
											  vmcs12_info_t * vmcs12_info);
void xmhf_nested_arch_x86vmx_rewalk_ept01(VCPU * vcpu,
										  vmcs12_info_t * vmcs12_info);
#ifdef __DEBUG_QEMU__
bool xmhf_nested_arch_x86vmx_check_fields_existence(VCPU * vcpu);
#endif							/* !__DEBUG_QEMU__ */

#endif							/* _NESTED_X86VMX_VMCS12_H_ */
