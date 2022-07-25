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

#include "nested-x86vmx-handler.h"

/*
 * Rules:
 * * Exactly one bit should be set in mask 0xf
 * * At most one bit should be set in mask 0x70
 * * FIELD_PROP_GPADDR (0x20) can only be set for 64-bit fields
 * * FIELD_PROP_SWWRONLY (0x80) can only be set when 0x10 or 0x20 is set
 * Notes:
 * * FIELD_PROP_ID_HOST is ignored. nested-x86vmx-vmcs12-guesthost.h is used
 *   instead.
 */
#define FIELD_PROP_GUEST	0x00000001	/* Guest field */
#define FIELD_PROP_HOST		0x00000002	/* Host field */
#define FIELD_PROP_CTRL		0x00000004	/* Control field */
#define FIELD_PROP_RO		0x00000008	/* Read-only field */
#define FIELD_PROP_ID_GUEST	0x00000010	/* VMCS12 value = VMCS02 value = any */
#define FIELD_PROP_GPADDR	0x00000020	/* VMCS12 value = VMCS02 value = gpa */
#define FIELD_PROP_ID_HOST	0x00000040	/* VMCS12 value = VMCS01 value */
#define FIELD_PROP_SWWRONLY	0x00000080	/* Read-only by hardware */

/* Maximum number of active VMCS per CPU */
#define VMX_NESTED_MAX_ACTIVE_VMCS 4

enum vmcs_nested_encoding {
#define DECLARE_FIELD_16(encoding, name, ...) \
	VMCSENC_##name = encoding,
#define DECLARE_FIELD_64(encoding, name, ...) DECLARE_FIELD_16(encoding, name)
#define DECLARE_FIELD_32(encoding, name, ...) DECLARE_FIELD_16(encoding, name)
#define DECLARE_FIELD_NW(encoding, name, ...) DECLARE_FIELD_16(encoding, name)
#include "nested-x86vmx-vmcs12-fields.h"
};

struct nested_vmcs12 {
#define DECLARE_FIELD_16(encoding, name, ...) \
	u16 name;
#define DECLARE_FIELD_64(encoding, name, ...) \
	u64 name;
#define DECLARE_FIELD_32(encoding, name, ...) \
	u32 name;
#define DECLARE_FIELD_NW(encoding, name, ...) \
	ulong_t name;
#include "nested-x86vmx-vmcs12-fields.h"
};

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
	/* Whether this VMCS has launched */
	int launched;
	/* Content of VMCS12, stored in XMHF's format */
	struct nested_vmcs12 vmcs12_value;
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
	 * The type of this member should be ept02_cache_line_t *. However,
	 * currently casting to void * to avoid circular includes in header files.
	 */
	void *guest_ept_cache_line;
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
} vmcs12_info_t;

size_t xmhf_nested_arch_x86vmx_vmcs_field_find(ulong_t encoding);
int xmhf_nested_arch_x86vmx_vmcs_writable(size_t offset);
ulong_t xmhf_nested_arch_x86vmx_vmcs_read(struct nested_vmcs12 *vmcs12,
										  size_t offset, size_t size);
void xmhf_nested_arch_x86vmx_vmcs_write(struct nested_vmcs12 *vmcs12,
										size_t offset, ulong_t value,
										size_t size);
void xmhf_nested_arch_x86vmx_vmcs_dump(VCPU * vcpu,
									   struct nested_vmcs12 *vmcs12,
									   char *prefix);
void xmhf_nested_arch_x86vmx_vmread_all(VCPU * vcpu, char *prefix);
u32 xmhf_nested_arch_x86vmx_vmcs12_to_vmcs02(VCPU * vcpu,
											 vmcs12_info_t * vmcs12_info);
void xmhf_nested_arch_x86vmx_vmcs02_to_vmcs12(VCPU * vcpu,
											  vmcs12_info_t * vmcs12_info);

#endif							/* _NESTED_X86VMX_VMCS12_H_ */
