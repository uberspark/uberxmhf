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

bool xmhf_nested_arch_x86vmx_vmcs_readable(ulong_t encoding)
{
	switch (encoding) {
#define DECLARE_FIELD_16(encoding, name, ...) \
	case encoding: \
		return true;
#define DECLARE_FIELD_64(encoding, name, ...) \
	case encoding: \
		return true; \
	case encoding + 1: \
		return true;
#define DECLARE_FIELD_32(...) DECLARE_FIELD_16(__VA_ARGS__)
#define DECLARE_FIELD_NW(...) DECLARE_FIELD_16(__VA_ARGS__)
#include "nested-x86vmx-vmcs12-fields.h"
	default:
		return false;
	}
}

bool xmhf_nested_arch_x86vmx_vmcs_writable(ulong_t encoding)
{
	switch (encoding) {
#define DECLARE_FIELD_16_RW(encoding, name, ...) \
	case encoding: \
		return true;
#define DECLARE_FIELD_64_RW(encoding, name, ...) \
	case encoding: \
		return true; \
	case encoding + 1: \
		return true;
#define DECLARE_FIELD_32_RW(...) DECLARE_FIELD_16_RW(__VA_ARGS__)
#define DECLARE_FIELD_NW_RW(...) DECLARE_FIELD_16_RW(__VA_ARGS__)
#include "nested-x86vmx-vmcs12-fields.h"
	default:
		return false;
	}
}

/* Used when handling L2 performing VMREAD, return true if successful */
ulong_t xmhf_nested_arch_x86vmx_vmcs_read(struct _vmx_vmcsfields *vmcs12,
										  ulong_t encoding, size_t size)
{
	switch (encoding) {
#define DECLARE_FIELD_16(encoding, name, ...) \
	case encoding: \
		return (ulong_t) vmcs12->name;
#define DECLARE_FIELD_64(encoding, name, ...) \
	case encoding: \
		if (size == sizeof(u64)) { \
			return (ulong_t) vmcs12->name; \
		} else { \
			HALT_ON_ERRORCOND(size == sizeof(u32)); \
			return (ulong_t) *(u32 *)(void *)&vmcs12->name; \
		} \
	case encoding + 1: \
		HALT_ON_ERRORCOND(size == sizeof(u32)); \
		return (ulong_t) ((u32 *)(void *)&vmcs12->name)[1];
#define DECLARE_FIELD_32(...) DECLARE_FIELD_16(__VA_ARGS__)
#define DECLARE_FIELD_NW(...) DECLARE_FIELD_16(__VA_ARGS__)
#include "nested-x86vmx-vmcs12-fields.h"
	default:
		HALT_ON_ERRORCOND(0 && "Unknown guest VMCS field");
	}
}

void xmhf_nested_arch_x86vmx_vmcs_write(struct _vmx_vmcsfields *vmcs12,
										size_t encoding, ulong_t value,
										size_t size)
{
	switch (encoding) {
#define DECLARE_FIELD_16_RO(encoding, name, ...) \
	case encoding: \
		HALT_ON_ERRORCOND(0 && "Write to read-only VMCS field"); \
		break;
#define DECLARE_FIELD_64_RO(encoding, name, ...) \
	case encoding: \
		HALT_ON_ERRORCOND(0 && "Write to read-only VMCS field"); \
		break; \
	case encoding + 1: \
		HALT_ON_ERRORCOND(0 && "Write to read-only VMCS field"); \
		break;
#define DECLARE_FIELD_32_RO(...) DECLARE_FIELD_16_RO(__VA_ARGS__)
#define DECLARE_FIELD_NW_RO(...) DECLARE_FIELD_16_RO(__VA_ARGS__)
#define DECLARE_FIELD_16_RW(encoding, name, ...) \
	case encoding: \
		vmcs12->name = (u16) value; \
		break;
#define DECLARE_FIELD_64_RW(encoding, name, ...) \
	case encoding: \
		if (size == sizeof(u64)) { \
			vmcs12->name = (u64) value; \
		} else { \
			HALT_ON_ERRORCOND(size == sizeof(u32)); \
			*(u32 *)(void *)&vmcs12->name = (u32) value; \
		} \
		break; \
	case encoding + 1: \
		HALT_ON_ERRORCOND(size == sizeof(u32)); \
		((u32 *)(void *)&vmcs12->name)[1] = (u32) value; \
		break;
#define DECLARE_FIELD_32_RW(encoding, name, ...) \
	case encoding: \
		vmcs12->name = (u32) value; \
		break;
#define DECLARE_FIELD_NW_RW(encoding, name, ...) \
	case encoding: \
		vmcs12->name = (ulong_t) value; \
		break;
#include "nested-x86vmx-vmcs12-fields.h"
	default:
		HALT_ON_ERRORCOND(0 && "Unknown guest VMCS field");
	}
}

/* VMREAD all fields in current VMCS and put the result to vmcs12 */
void xmhf_nested_arch_x86vmx_vmcs_read_all(VCPU * vcpu,
										   struct _vmx_vmcsfields *vmcs12)
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
											struct _vmx_vmcsfields *vmcs12)
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
									   struct _vmx_vmcsfields *vmcs12,
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

/* Check whether ia32_pat is legal value of IA32_PAT MSR */
static bool _check_ia32_pat(u64 ia32_pat)
{
	u32 offset;
	for (offset = 0; offset < 64; offset += 8) {
		u8 pa = (u8) (ia32_pat >> offset);
		switch (pa) {
		case 0:				/* fallthrough */
		case 1:				/* fallthrough */
		case 4:				/* fallthrough */
		case 5:				/* fallthrough */
		case 6:				/* fallthrough */
		case 7:
			break;
		default:
			return false;
		}
	}
	return true;
}

/*
 * Check whether ia32_pat is legal value of IA32_EFER MSR.
 * lma indicates whether IA32_EFER.LMA should be set.
 * cr0_pg indicates whether CR0.PG is set.
 */
static bool _check_ia32_efer(u64 ia32_efer, bool lma, bool cr0_pg)
{
	/* Check EFER.LMA and EFER.LME are correct */
	u64 mask = (1ULL << EFER_LMA);
	if (cr0_pg) {
		mask |= (1ULL << EFER_LME);
	}
	if (lma) {
		if ((ia32_efer & mask) != mask) {
			return false;
		}
	} else {
		if ((ia32_efer & mask) != 0) {
			return false;
		}
	}
	/* Check reserved bits */
	if (ia32_efer & ~0x00000d01ULL) {
		return false;
	}
	return true;
}

/*
 * Extract ctls information to ctls from selected fields in VMCS12.
 * Return an error code following VM instruction error number, or 0 when
 * success.
 */
static u32 _vmcs12_get_ctls(VCPU * vcpu, struct _vmx_vmcsfields *vmcs12,
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

typedef struct _vmcs12_to_vmcs02_arg {
	VCPU *vcpu;
	vmcs12_info_t *vmcs12_info;
	struct _vmx_vmcsfields *vmcs12;
	vmx_ctls_t *ctls;
	guestmem_hptw_ctx_pair_t *ctx_pair;
	u64 guest_ia32_pat;
	u64 guest_ia32_efer;
	u32 ia32_pat_index;
	u32 ia32_efer_index;
	msr_entry_t *msr01;
} ARG10;

typedef struct _vmcs02_to_vmcs12_arg {
	VCPU *vcpu;
	vmcs12_info_t *vmcs12_info;
	struct _vmx_vmcsfields *vmcs12;
	vmx_ctls_t *ctls;
	u64 host_ia32_pat;
	u64 host_ia32_efer;
	u32 ia32_pat_index;
	u32 ia32_efer_index;
	msr_entry_t *msr02;
} ARG01;

#define FIELD_CTLS_ARG (arg->ctls)

#define DECLARE_FIELD_16_RW(encoding, name, prop, exist, trans_suf, ...) \
DECLARE_FIELD_16_RO(encoding, name, prop, exist, trans_suf, ...) \
static u32 _vmcs12_to_vmcs02_##name##trans_suf(ARG10 * arg) \
{ \
	if (prop & FIELD_PROP_ID_GUEST) { \
		if (exist) { \
			__vmx_vmwrite16(encoding, arg->vmcs12->name); \
		} \
		return VM_INST_SUCCESS; \
	} else if (prop & (FIELD_PROP_IGNORE | FIELD_PROP_ID_HOST)) { \
		return VM_INST_SUCCESS; \
	} else if (prop & FIELD_PROP_UNSUPP) { \
		HALT_ON_ERRORCOND(!exist); \
		return VM_INST_SUCCESS; \
	} else { \
		HALT_ON_ERRORCOND(0 && "Not implemented"); \
	} \
}

#define DECLARE_FIELD_16_RO(encoding, name, prop, exist, trans_suf, ...) \
static void _vmcs02_to_vmcs12_##name##trans_suf(ARG01 * arg) \
{ \
	if (prop & FIELD_PROP_ID_GUEST) { \
		if (exist) { \
			if (prop & FIELD_PROP_SWWRONLY) { \
				HALT_ON_ERRORCOND(arg->vmcs12->name == \
								  __vmx_vmread16(encoding)); \
			} else { \
				arg->vmcs12->name = __vmx_vmread16(encoding); \
			} \
		} \
	} else if (prop & FIELD_PROP_UNSUPP) { \
		HALT_ON_ERRORCOND(!exist); \
	} else if (!(prop & (FIELD_PROP_IGNORE | FIELD_PROP_ID_HOST))) { \
		HALT_ON_ERRORCOND(0 && "Not implemented"); \
	} \
}

#define DECLARE_FIELD_64_RW(encoding, name, prop, exist, trans_suf, ...) \
DECLARE_FIELD_64_RO(encoding, name, prop, exist, trans_suf, ...) \
static u32 _vmcs12_to_vmcs02_##name##trans_suf(ARG10 * arg) \
{ \
	if (prop & FIELD_PROP_ID_GUEST) { \
		if (exist) { \
			__vmx_vmwrite64(encoding, arg->vmcs12->name); \
		} \
		return VM_INST_SUCCESS; \
	} else if (prop & FIELD_PROP_GPADDR) { \
		if (exist) { \
			gpa_t addr = arg->vmcs12->name; \
			__vmx_vmwrite64(encoding, guestmem_gpa2spa_page(arg->ctx_pair, \
															addr)); \
		} \
		return VM_INST_SUCCESS; \
	} else if (prop & (FIELD_PROP_IGNORE | FIELD_PROP_ID_HOST)) { \
		return VM_INST_SUCCESS; \
	} else if (prop & FIELD_PROP_UNSUPP) { \
		HALT_ON_ERRORCOND(!exist); \
		return VM_INST_SUCCESS; \
	} else { \
		HALT_ON_ERRORCOND(0 && "Not implemented"); \
	} \
}

#define DECLARE_FIELD_64_RO(encoding, name, prop, exist, trans_suf, ...) \
static void _vmcs02_to_vmcs12_##name##trans_suf(ARG01 * arg) \
{ \
	if ((prop & FIELD_PROP_ID_GUEST) || (prop & FIELD_PROP_GPADDR)) { \
		if (exist) { \
			if (prop & FIELD_PROP_SWWRONLY) { \
				/* Note: currently for FIELD_PROP_GPADDR, assuming spa=gpa */ \
				HALT_ON_ERRORCOND(arg->vmcs12->name == \
								  __vmx_vmread64(encoding)); \
			} else { \
				arg->vmcs12->name = __vmx_vmread64(encoding); \
			} \
		} \
	} else if (prop & FIELD_PROP_UNSUPP) { \
		HALT_ON_ERRORCOND(!exist); \
	} else if (!(prop & (FIELD_PROP_IGNORE | FIELD_PROP_ID_HOST))) { \
		HALT_ON_ERRORCOND(0 && "Not implemented"); \
	} \
}

#define DECLARE_FIELD_32_RW(encoding, name, prop, exist, trans_suf, ...) \
DECLARE_FIELD_32_RO(encoding, name, prop, exist, trans_suf, ...) \
static u32 _vmcs12_to_vmcs02_##name##trans_suf(ARG10 * arg) \
{ \
	if (prop & FIELD_PROP_ID_GUEST) { \
		if (exist) { \
			__vmx_vmwrite32(encoding, arg->vmcs12->name); \
		} \
		return VM_INST_SUCCESS; \
	} else if (prop & (FIELD_PROP_IGNORE | FIELD_PROP_ID_HOST)) { \
		return VM_INST_SUCCESS; \
	} else if (prop & FIELD_PROP_UNSUPP) { \
		HALT_ON_ERRORCOND(!exist); \
		return VM_INST_SUCCESS; \
	} else { \
		HALT_ON_ERRORCOND(0 && "Not implemented"); \
	} \
}

#define DECLARE_FIELD_32_RO(encoding, name, prop, exist, trans_suf, ...) \
static void _vmcs02_to_vmcs12_##name##trans_suf(ARG01 * arg) \
{ \
	if (prop & FIELD_PROP_ID_GUEST) { \
		if (exist) { \
			if (prop & FIELD_PROP_SWWRONLY) { \
				HALT_ON_ERRORCOND(arg->vmcs12->name == \
								  __vmx_vmread32(encoding)); \
			} else { \
				arg->vmcs12->name = __vmx_vmread32(encoding); \
			} \
		} \
	} else if (prop & FIELD_PROP_UNSUPP) { \
		HALT_ON_ERRORCOND(!exist); \
	} else if (!(prop & (FIELD_PROP_IGNORE | FIELD_PROP_ID_HOST))) { \
		HALT_ON_ERRORCOND(0 && "Not implemented"); \
	} \
}

#define DECLARE_FIELD_NW_RW(encoding, name, prop, exist, trans_suf, ...) \
DECLARE_FIELD_NW_RO(encoding, name, prop, exist, trans_suf, ...) \
static u32 _vmcs12_to_vmcs02_##name##trans_suf(ARG10 * arg) \
{ \
	if (prop & FIELD_PROP_ID_GUEST) { \
		if (exist) { \
			__vmx_vmwriteNW(encoding, arg->vmcs12->name); \
		} \
		return VM_INST_SUCCESS; \
	} else if (prop & (FIELD_PROP_IGNORE | FIELD_PROP_ID_HOST)) { \
		return VM_INST_SUCCESS; \
	} else if (prop & FIELD_PROP_UNSUPP) { \
		HALT_ON_ERRORCOND(!exist); \
		return VM_INST_SUCCESS; \
	} else { \
		HALT_ON_ERRORCOND(0 && "Not implemented"); \
	} \
}

#define DECLARE_FIELD_NW_RO(encoding, name, prop, exist, trans_suf, ...) \
static void _vmcs02_to_vmcs12_##name##trans_suf(ARG01 * arg) \
{ \
	if (prop & FIELD_PROP_ID_GUEST) { \
		if (exist) { \
			if (prop & FIELD_PROP_SWWRONLY) { \
				HALT_ON_ERRORCOND(arg->vmcs12->name == \
								  __vmx_vmreadNW(encoding)); \
			} else { \
				arg->vmcs12->name = __vmx_vmreadNW(encoding); \
			} \
		} \
	} else if (prop & FIELD_PROP_UNSUPP) { \
		HALT_ON_ERRORCOND(!exist); \
	} else if (!(prop & (FIELD_PROP_IGNORE | FIELD_PROP_ID_HOST))) { \
		HALT_ON_ERRORCOND(0 && "Not implemented"); \
	} \
}

#include "nested-x86vmx-vmcs12-fields.h"

#define DECLARE_FIELDPAIR_16(guest_encoding, host_encoding, name) \
static u32 _vmcs12_to_vmcs02_host_##name(ARG10 * arg) \
{ \
	__vmx_vmwrite16(host_encoding, arg->vcpu->vmcs.host_##name); \
	return VM_INST_SUCCESS; \
	(void) _vmcs12_to_vmcs02_host_##name##_unused; \
} \
\
static void _vmcs02_to_vmcs12_host_##name(ARG01 * arg) \
{ \
	HALT_ON_ERRORCOND(__vmx_vmread16(host_encoding) == \
					  arg->vcpu->vmcs.host_##name); \
	arg->vcpu->vmcs.guest_##name = arg->vmcs12->host_##name; \
	(void) _vmcs02_to_vmcs12_host_##name##_unused; \
}

#define DECLARE_FIELDPAIR_64(guest_encoding, host_encoding, name) \
static u32 _vmcs12_to_vmcs02_host_##name(ARG10 * arg) \
{ \
	__vmx_vmwrite64(host_encoding, arg->vcpu->vmcs.host_##name); \
	return VM_INST_SUCCESS; \
	(void) _vmcs12_to_vmcs02_host_##name##_unused; \
} \
\
static void _vmcs02_to_vmcs12_host_##name(ARG01 * arg) \
{ \
	HALT_ON_ERRORCOND(__vmx_vmread64(host_encoding) == \
					  arg->vcpu->vmcs.host_##name); \
	arg->vcpu->vmcs.guest_##name = arg->vmcs12->host_##name; \
	(void) _vmcs02_to_vmcs12_host_##name##_unused; \
}

#define DECLARE_FIELDPAIR_32(guest_encoding, host_encoding, name) \
static u32 _vmcs12_to_vmcs02_host_##name(ARG10 * arg) \
{ \
	__vmx_vmwrite32(host_encoding, arg->vcpu->vmcs.host_##name); \
	return VM_INST_SUCCESS; \
	(void) _vmcs12_to_vmcs02_host_##name##_unused; \
} \
\
static void _vmcs02_to_vmcs12_host_##name(ARG01 * arg) \
{ \
	HALT_ON_ERRORCOND(__vmx_vmread32(host_encoding) == \
					  arg->vcpu->vmcs.host_##name); \
	arg->vcpu->vmcs.guest_##name = arg->vmcs12->host_##name; \
	(void) _vmcs02_to_vmcs12_host_##name##_unused; \
}

#define DECLARE_FIELDPAIR_NW(guest_encoding, host_encoding, name) \
static u32 _vmcs12_to_vmcs02_host_##name(ARG10 * arg) \
{ \
	__vmx_vmwriteNW(host_encoding, arg->vcpu->vmcs.host_##name); \
	return VM_INST_SUCCESS; \
	(void) _vmcs12_to_vmcs02_host_##name##_unused; \
} \
\
static void _vmcs02_to_vmcs12_host_##name(ARG01 * arg) \
{ \
	HALT_ON_ERRORCOND(__vmx_vmreadNW(host_encoding) == \
					  arg->vcpu->vmcs.host_##name); \
	arg->vcpu->vmcs.guest_##name = arg->vmcs12->host_##name; \
	(void) _vmcs02_to_vmcs12_host_##name##_unused; \
}

#include "nested-x86vmx-vmcs12-guesthost.h"

/*
 * 16-Bit Control Fields
 */

/* Virtual-processor identifier (VPID) */

static u32 _vmcs12_to_vmcs02_control_vpid(ARG10 * arg)
{
	u16 vpid02;
	if (_vmx_hasctl_enable_vpid(arg->ctls)) {
		bool cache_hit;
		u16 vpid12 = arg->vmcs12->control_vpid;
		if (vpid12 == 0) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		vpid02 = xmhf_nested_arch_x86vmx_get_vpid02(arg->vcpu, vpid12,
													&cache_hit);
	} else {
		/*
		 * When VPID is not enabled, VMENTRY and VMEXIT in L1 should result in
		 * flushing linear and combination TLB. We simulate this effect here by
		 * setting VPID of L2 guest to the same as L1 guest (VPID = 1) and
		 * manually executing INVVPID for every VNENTRY and VMEXIT.
		 */
		vpid02 = 1;
		HALT_ON_ERRORCOND(__vmx_invvpid(VMX_INVVPID_SINGLECONTEXT, 1, 0));
	}
	__vmx_vmwrite16(VMCSENC_control_vpid, vpid02);
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_vpid_unused;
}

static void _vmcs02_to_vmcs12_control_vpid(ARG01 * arg)
{
	u16 vpid02;
	if (_vmx_hasctl_enable_vpid(arg->ctls)) {
		bool cache_hit;
		u16 vpid12 = arg->vmcs12->control_vpid;
		HALT_ON_ERRORCOND(vpid12 != 0);
		vpid02 = xmhf_nested_arch_x86vmx_get_vpid02(arg->vcpu, vpid12,
													&cache_hit);
		HALT_ON_ERRORCOND(cache_hit);
	} else {
		/*
		 * When VPID is not enabled, VMENTRY and VMEXIT in L1 should result in
		 * flushing linear and combination TLB. We simulate this effect here by
		 * setting VPID of L2 guest to the same as L1 guest (VPID = 1) and
		 * manually executing INVVPID for every VNENTRY and VMEXIT.
		 */
		vpid02 = 1;
		HALT_ON_ERRORCOND(__vmx_invvpid(VMX_INVVPID_SINGLECONTEXT, 1, 0));
	}
	HALT_ON_ERRORCOND(__vmx_vmread16(VMCSENC_control_vpid) == vpid02);
	(void)_vmcs02_to_vmcs12_control_vpid_unused;
}

/*
 * 16-Bit Guest-State Fields
 */

/*
 * 16-Bit Host-State Fields
 */

/*
 * 64-Bit Control Fields
 */

/* Address of MSR bitmaps */

static u32 _vmcs12_to_vmcs02_control_MSR_Bitmaps_address(ARG10 * arg)
{
	if (_vmx_hasctl_use_msr_bitmaps(arg->ctls)) {
		/* Note: ideally should return VMENTRY error */
		HALT_ON_ERRORCOND(PA_PAGE_ALIGNED_4K
						  (arg->vmcs12->control_MSR_Bitmaps_address));
	}
	/* XMHF never uses MSR bitmaps, so set VMCS02 to invalid value */
	__vmx_vmwrite64(VMCSENC_control_MSR_Bitmaps_address, UINT64_MAX);
	return VM_INST_SUCCESS;
	(void)arg;
	(void)_vmcs12_to_vmcs02_control_MSR_Bitmaps_address_unused;
}

static void _vmcs02_to_vmcs12_control_MSR_Bitmaps_address(ARG01 * arg)
{
	u16 encoding = VMCSENC_control_MSR_Bitmaps_address;
	HALT_ON_ERRORCOND(__vmx_vmread64(encoding) == UINT64_MAX);
	(void)arg;
	(void)_vmcs02_to_vmcs12_control_MSR_Bitmaps_address_unused;
}

/* VM-exit MSR-store address */

static u32 _vmcs12_to_vmcs02_control_VM_exit_MSR_store_address(ARG10 * arg)
{
	/* VMCS02 needs to always process the same MSRs as VMCS01 */
	__vmx_vmwrite64(VMCSENC_control_VM_exit_MSR_store_address,
					hva2spa(arg->vmcs12_info->vmcs02_vmexit_msr_store_area));
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_VM_exit_MSR_store_address_unused;
}

static void _vmcs02_to_vmcs12_control_VM_exit_MSR_store_address(ARG01 * arg)
{
	u16 encoding = VMCSENC_control_VM_exit_MSR_store_address;
	HALT_ON_ERRORCOND(hva2spa(arg->vmcs12_info->vmcs02_vmexit_msr_store_area) ==
					  __vmx_vmread64(encoding));
	(void)_vmcs02_to_vmcs12_control_VM_exit_MSR_store_address_unused;
}

/* VM-exit MSR-load address */

static u32 _vmcs12_to_vmcs02_control_VM_exit_MSR_load_address(ARG10 * arg)
{
	/* VMCS02 needs to always process the same MSRs as VMCS01 */
	__vmx_vmwrite64(VMCSENC_control_VM_exit_MSR_load_address,
					hva2spa(arg->vmcs12_info->vmcs02_vmexit_msr_load_area));
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_VM_exit_MSR_load_address_unused;
}

static void _vmcs02_to_vmcs12_control_VM_exit_MSR_load_address(ARG01 * arg)
{
	u16 encoding = VMCSENC_control_VM_exit_MSR_load_address;
	HALT_ON_ERRORCOND(hva2spa(arg->vmcs12_info->vmcs02_vmexit_msr_load_area) ==
					  __vmx_vmread64(encoding));
	(void)_vmcs02_to_vmcs12_control_VM_exit_MSR_load_address_unused;
}

/* VM-entry MSR-load address */

static u32 _vmcs12_to_vmcs02_control_VM_entry_MSR_load_address(ARG10 * arg)
{
	/* VMCS02 needs to always process the same MSRs as VMCS01 */
	__vmx_vmwrite64(VMCSENC_control_VM_entry_MSR_load_address,
					hva2spa(arg->vmcs12_info->vmcs02_vmentry_msr_load_area));
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_VM_entry_MSR_load_address_unused;
}

static void _vmcs02_to_vmcs12_control_VM_entry_MSR_load_address(ARG01 * arg)
{
	u16 encoding = VMCSENC_control_VM_entry_MSR_load_address;
	HALT_ON_ERRORCOND(hva2spa(arg->vmcs12_info->vmcs02_vmentry_msr_load_area)
					  == __vmx_vmread64(encoding));
	(void)_vmcs02_to_vmcs12_control_VM_entry_MSR_load_address_unused;
}

/*
 * control_Executive_VMCS_pointer: ignored (0 in VMCS02), because we assume
 * XMHF is not in SMM. Also see IA32_VMX_BASIC bit 49.
 */

/* Posted-interrupt descriptor address */

static u32 _vmcs12_to_vmcs02_control_posted_interrupt_desc_address(ARG10 * arg)
{
	if (_vmx_hasctl_process_posted_interrupts(arg->ctls)) {
		gpa_t addr = arg->vmcs12->control_posted_interrupt_desc_address;
		if (addr & (64 - 1)) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		__vmx_vmwrite64(VMCSENC_control_posted_interrupt_desc_address,
						guestmem_gpa2spa_size(arg->ctx_pair, addr, 64));
	}
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_posted_interrupt_desc_address_unused;
}

static void _vmcs02_to_vmcs12_control_posted_interrupt_desc_address(ARG01 * arg)
{
	if (_vmx_hasctl_process_posted_interrupts(arg->ctls)) {
		u16 encoding = VMCSENC_control_posted_interrupt_desc_address;
		/* Note: currently assuming spa=gpa */
		HALT_ON_ERRORCOND(arg->vmcs12->control_posted_interrupt_desc_address ==
						  __vmx_vmread64(encoding));
	}
	(void)_vmcs02_to_vmcs12_control_posted_interrupt_desc_address_unused;
}

/* EPT pointer */

static void _update_pae_pdpte(ARG10 * arg)
{
	/*
	 * Assume guest does not enable EPT. Check whether guest is in PAE. If so,
	 * XMHF needs to re-compute PDPTEs VMCS fields. (Otherwise the nested guest
	 * may triple fault.
	 */
	bool pae = ((arg->vmcs12->guest_CR0 & CR0_PG) &&
				(arg->vmcs12->guest_CR4 & CR4_PAE));
#ifdef __AMD64__
	if (_vmx_hasctl_vmentry_ia_32e_mode_guest(arg->ctls)) {
		pae = false;
	}
#elif !defined(__I386__)
#error "Unsupported Arch"
#endif							/* !defined(__I386__) */
	if (pae) {
		/* Walk EPT and retrieve values for guest_PDPTE* */
		u64 pdptes[4];
		u64 addr = arg->vmcs12->guest_CR3 & ~0x1FUL;
		guestmem_copy_gp2h(arg->ctx_pair, 0, pdptes, addr, sizeof(pdptes));
		__vmx_vmwrite64(VMCSENC_guest_PDPTE0, pdptes[0]);
		__vmx_vmwrite64(VMCSENC_guest_PDPTE1, pdptes[1]);
		__vmx_vmwrite64(VMCSENC_guest_PDPTE2, pdptes[2]);
		__vmx_vmwrite64(VMCSENC_guest_PDPTE3, pdptes[3]);
	}
}

#ifdef __DEBUG_QEMU__
static void _workaround_kvm_216212(ARG10 * arg, ept02_cache_line_t * cache_line)
{
	/*
	 * Workaround a KVM bug: https://bugzilla.kernel.org/show_bug.cgi?id=216212
	 *
	 * Looks like KVM has a problem setting CR0.PG when nested guest's PDPTEs
	 * are not in guest hypervisor's EPT. So we always make sure the EPT entry
	 * for PDPTEs is available. To achieve this effect, simulating a EPT
	 * violation by calling xmhf_nested_arch_x86vmx_handle_ept02_exit() with
	 * guest2_paddr = CR3.
	 */
	extern bool is_in_kvm;
	if (is_in_kvm && arg->vmcs12->guest_CR3 != 0) {
		xmhf_nested_arch_x86vmx_hardcode_ept(arg->vcpu, cache_line,
											 arg->vmcs12->guest_CR3);
	}
}
#endif							/* !__DEBUG_QEMU__ */

static u32 _vmcs12_to_vmcs02_control_EPT_pointer(ARG10 * arg)
{
	/* Note: VMX_SECPROCBASED_ENABLE_EPT is always enabled */
	spa_t ept02;
	HALT_ON_ERRORCOND(_vmx_hasctl_enable_ept(&arg->vcpu->vmx_caps));
	if (_vmx_hasctl_enable_ept(arg->ctls)) {
		/* Construct shadow EPT */
		u64 eptp12 = arg->vmcs12->control_EPT_pointer;
		gpa_t ept12;
		ept02_cache_line_t *cache_line;
		bool cache_hit;
		arg->vmcs12_info->guest_ept_enable = 1;
		if (!xmhf_nested_arch_x86vmx_check_ept_lower_bits(eptp12, &ept12)) {
			return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
		}
		ept02 = xmhf_nested_arch_x86vmx_get_ept02(arg->vcpu, ept12, &cache_hit,
												  &cache_line);
		arg->vmcs12_info->guest_ept_cache_line = cache_line;
		arg->vmcs12_info->guest_ept_root = ept12;
#ifdef __DEBUG_QEMU__
		_workaround_kvm_216212(arg, cache_line);
#endif							/* !__DEBUG_QEMU__ */
	} else {
		/* Guest does not use EPT, just use XMHF's EPT */
		arg->vmcs12_info->guest_ept_enable = 0;
		ept02 = arg->vcpu->vmcs.control_EPT_pointer;
		_update_pae_pdpte(arg);
	}
	__vmx_vmwrite64(VMCSENC_control_EPT_pointer, ept02);
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_EPT_pointer_unused;
}

static void _vmcs02_to_vmcs12_control_EPT_pointer(ARG01 * arg)
{
	spa_t ept02;
	HALT_ON_ERRORCOND(_vmx_hasctl_enable_ept(&arg->vcpu->vmx_caps));
	if (_vmx_hasctl_enable_ept(arg->ctls)) {
		gpa_t ept12 = arg->vmcs12_info->guest_ept_root;
		ept02_cache_line_t *cache_line;
		bool cache_hit;
		ept02 = xmhf_nested_arch_x86vmx_get_ept02(arg->vcpu, ept12, &cache_hit,
												  &cache_line);
		HALT_ON_ERRORCOND(cache_hit);
	} else {
		ept02 = arg->vcpu->vmcs.control_EPT_pointer;
	}
	HALT_ON_ERRORCOND(__vmx_vmread64(VMCSENC_control_EPT_pointer) == ept02);
	/* vmcs12->control_EPT_pointer is ignored here */
	(void)_vmcs02_to_vmcs12_control_EPT_pointer_unused;
}

static void _rewalk_ept01_control_EPT_pointer(ARG10 * arg)
{
	spa_t ept02;
	if (arg->vmcs12_info->guest_ept_enable) {
		ept02_cache_line_t *cache_line;
		bool cache_hit;
		u64 eptp12 = arg->vmcs12->control_EPT_pointer;
		gpa_t ept12;
		HALT_ON_ERRORCOND(xmhf_nested_arch_x86vmx_check_ept_lower_bits
						  (eptp12, &ept12));
		ept02 =
			xmhf_nested_arch_x86vmx_get_ept02(arg->vcpu, ept12, &cache_hit,
											  &cache_line);
		HALT_ON_ERRORCOND(!cache_hit);
		arg->vmcs12_info->guest_ept_cache_line = cache_line;
		__vmx_vmwrite64(VMCSENC_control_EPT_pointer, ept02);
#ifdef __DEBUG_QEMU__
		_workaround_kvm_216212(arg, cache_line);
#endif							/* !__DEBUG_QEMU__ */
	} else {
		ept02 = arg->vcpu->vmcs.control_EPT_pointer;
		_update_pae_pdpte(arg);
	}
	__vmx_vmwrite64(VMCSENC_control_EPT_pointer, ept02);
}

/*
 * 64-Bit Read-Only Data Field
 */

/*
 * 64-Bit Guest-State Fields
 */

/* Guest IA32_PAT */

static u32 _vmcs12_to_vmcs02_guest_IA32_PAT(ARG10 * arg)
{
	if (_vmx_hasctl_vmentry_load_ia32_pat(arg->ctls)) {
		/* XMHF never uses this feature. Instead, uses MSR load / save area */
		arg->guest_ia32_pat = arg->vmcs12->guest_IA32_PAT;
		/* Note: ideally should return VMENTRY error */
		HALT_ON_ERRORCOND(_check_ia32_pat(arg->guest_ia32_pat));
	} else {
		/* When not loading IA32_PAT, IA32_PAT from L1 is used */
		arg->guest_ia32_pat = arg->msr01[arg->ia32_pat_index].data;
	}
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_guest_IA32_PAT_unused;
}

static void _vmcs02_to_vmcs12_guest_IA32_PAT(ARG01 * arg)
{
	if (_vmx_hasctl_vmexit_save_ia32_pat(arg->ctls)) {
		/* XMHF never uses this feature. Instead, uses MSR load / save area */
		arg->vmcs12->guest_IA32_PAT = arg->msr02[arg->ia32_pat_index].data;
	}
	(void)_vmcs02_to_vmcs12_guest_IA32_PAT_unused;
}

/* Guest IA32_EFER */

static u32 _vmcs12_to_vmcs02_guest_IA32_EFER(ARG10 * arg)
{
	if (_vmx_hasctl_vmentry_load_ia32_efer(arg->ctls)) {
		/* XMHF never uses this feature. Instead, uses MSR load / save area */
		arg->guest_ia32_efer = arg->vmcs12->guest_IA32_EFER;
		/* Note: ideally should return VMENTRY error */
		HALT_ON_ERRORCOND(_check_ia32_efer
						  (arg->guest_ia32_efer,
						   _vmx_hasctl_vmentry_ia_32e_mode_guest(arg->ctls),
						   arg->vmcs12->guest_CR0 & CR0_PG));
	} else {
		/*
		 * When not loading IA32_EFER, IA32_EFER is changed as following:
		 * * IA32_EFER.LMA = "IA-32e mode guest"
		 * * If CR0.PG = 1, IA32_EFER.LME = "IA-32e mode guest"
		 */
		u64 val01 = arg->msr01[arg->ia32_efer_index].data;
		u64 mask = (1ULL << EFER_LMA);
		if (arg->vmcs12->guest_CR0 & CR0_PG) {
			mask |= (1ULL << EFER_LME);
		}
		if (_vmx_hasctl_vmentry_ia_32e_mode_guest(arg->ctls)) {
			arg->guest_ia32_efer = val01 | mask;
		} else {
			arg->guest_ia32_efer = val01 & ~mask;
		}
	}
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_guest_IA32_EFER_unused;
}

static void _vmcs02_to_vmcs12_guest_IA32_EFER(ARG01 * arg)
{
	if (_vmx_hasctl_vmexit_save_ia32_efer(arg->ctls)) {
		/* XMHF never uses this feature. Instead, uses MSR load / save area */
		arg->vmcs12->guest_IA32_EFER = arg->msr02[arg->ia32_efer_index].data;
	}
	(void)_vmcs02_to_vmcs12_guest_IA32_EFER_unused;
}

/*
 * 64-Bit Host-State Fields
 */

/* Host IA32_PAT */

static u32 _vmcs12_to_vmcs02_host_IA32_PAT(ARG10 * arg)
{
	if (_vmx_hasctl_vmexit_load_ia32_pat(arg->ctls)) {
		/* XMHF never uses this feature. Instead, uses MSR load / save area */
		/* Note: ideally should return VMENTRY error */
		HALT_ON_ERRORCOND(_check_ia32_pat(arg->vmcs12->host_IA32_PAT));
	}
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_host_IA32_PAT_unused;
}

static void _vmcs02_to_vmcs12_host_IA32_PAT(ARG01 * arg)
{
	if (_vmx_hasctl_vmexit_load_ia32_pat(arg->ctls)) {
		/* XMHF never uses this feature. Instead, uses MSR load / save area */
		arg->host_ia32_pat = arg->vmcs12->host_IA32_PAT;
	} else {
		arg->host_ia32_pat = arg->msr02[arg->ia32_pat_index].data;
	}
	(void)_vmcs02_to_vmcs12_host_IA32_PAT_unused;
}

/* Host IA32_EFER */

static u32 _vmcs12_to_vmcs02_host_IA32_EFER(ARG10 * arg)
{
	if (_vmx_hasctl_vmexit_load_ia32_efer(arg->ctls)) {
		/* XMHF never uses this feature. Instead, uses MSR load / save area */
		/* Note: ideally should return VMENTRY error */
		bool host_long = _vmx_hasctl_vmexit_host_address_space_size(arg->ctls);
		HALT_ON_ERRORCOND(_check_ia32_efer(arg->vmcs12->host_IA32_EFER,
										   host_long, true));
	}
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_host_IA32_EFER_unused;
}

static void _vmcs02_to_vmcs12_host_IA32_EFER(ARG01 * arg)
{
	if (_vmx_hasctl_vmexit_load_ia32_efer(arg->ctls)) {
		/* XMHF never uses this feature. Instead, uses MSR load / save area */
		arg->host_ia32_efer = arg->vmcs12->host_IA32_EFER;
	} else {
		/*
		 * When not loading IA32_EFER, IA32_EFER is changed as following:
		 * * IA32_EFER.LMA = "host address-space size"
		 * * IA32_EFER.LME = "host address-space size"
		 */
		u64 mask = (1ULL << EFER_LMA) | (1ULL << EFER_LME);
		if (_vmx_hasctl_vmexit_host_address_space_size(arg->ctls)) {
			arg->host_ia32_efer = arg->msr02[arg->ia32_efer_index].data | mask;
		} else {
			arg->host_ia32_efer = arg->msr02[arg->ia32_efer_index].data & mask;
		}
	}
	(void)_vmcs02_to_vmcs12_host_IA32_EFER_unused;
}

/* Host IA32_PERF_GLOBAL_CTRL */

static u32 _vmcs12_to_vmcs02_host_IA32_PERF_GLOBAL_CTRL(ARG10 * arg)
{
	if (_vmx_hasctl_vmexit_load_ia32_perf_global_ctrl(arg->ctls)) {
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
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_host_IA32_PERF_GLOBAL_CTRL_unused;
}

static void _vmcs02_to_vmcs12_host_IA32_PERF_GLOBAL_CTRL(ARG01 * arg)
{
	if (_vmx_hasctl_vmexit_load_ia32_perf_global_ctrl(arg->ctls)) {
		u32 eax, ebx, ecx, edx;
		cpuid(0x0, &eax, &ebx, &ecx, &edx);
		if (eax >= 0xA) {
			cpuid(0xA, &eax, &ebx, &ecx, &edx);
			if (eax & 0xffU) {
				/* Check L1 */
				u16 encoding = VMCSENC_host_IA32_PERF_GLOBAL_CTRL;
				HALT_ON_ERRORCOND(__vmx_vmread64(encoding) ==
								  rdmsr64(IA32_PERF_GLOBAL_CTRL));
				/* Update L0 */
				wrmsr64(IA32_PERF_GLOBAL_CTRL,
						__vmx_vmread64(VMCSENC_host_IA32_PERF_GLOBAL_CTRL));
			}
		}
	}
	(void)_vmcs02_to_vmcs12_host_IA32_PERF_GLOBAL_CTRL_unused;
}

/* Host IA32_PKRS */

static u32 _vmcs12_to_vmcs02_host_IA32_PKRS(ARG10 * arg)
{
	if (_vmx_hasctl_vmexit_load_pkrs(arg->ctls)) {
		__vmx_vmwrite64(VMCSENC_host_IA32_PKRS, rdmsr64(IA32_PKRS));
	}
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_host_IA32_PKRS_unused;
}

static void _vmcs02_to_vmcs12_host_IA32_PKRS(ARG01 * arg)
{
	if (_vmx_hasctl_vmexit_load_pkrs(arg->ctls)) {
		/* Check L1 */
		HALT_ON_ERRORCOND(__vmx_vmread64(VMCSENC_host_IA32_PKRS) ==
						  rdmsr64(IA32_PKRS));
		/* Update L0 */
		wrmsr64(IA32_PKRS, __vmx_vmread64(VMCSENC_host_IA32_PKRS));
	}
	(void)_vmcs02_to_vmcs12_host_IA32_PKRS_unused;
}

/*
 * 32-Bit Control Fields
 */

/* Pin-based VM-execution controls */

static u32 _vmcs12_to_vmcs02_control_VMX_pin_based(ARG10 * arg)
{
	/*
	 * Note: this function needs to be called before 
	 * _vmcs12_to_vmcs02_control_VMX_cpu_based().
	 */
	u32 val = arg->vmcs12->control_VMX_pin_based;
	/* Check for relationship between "NMI exiting" and "virtual NMIs" */
	arg->vmcs12_info->guest_nmi_exiting = _vmx_hasctl_nmi_exiting(arg->ctls);
	arg->vmcs12_info->guest_virtual_nmis = _vmx_hasctl_virtual_nmis(arg->ctls);
	if (!arg->vmcs12_info->guest_nmi_exiting &&
		arg->vmcs12_info->guest_virtual_nmis) {
		return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
	}
	/*
	 * Disallow NMI injection if NMI exiting = 0.
	 * This is a limitation of XMHF. The correct behavior is to make NMI
	 * not blocked after injecting NMI. However, this requires non-trivial
	 * XMHF implementation effort. So not implemented, at least for now.
	 */
	if (!arg->vmcs12_info->guest_nmi_exiting) {
		u32 injection = arg->vmcs12->control_VM_entry_interruption_information;
		if (xmhf_nested_arch_x86vmx_is_interruption_nmi(injection)) {
			HALT_ON_ERRORCOND(0 && "Not supported (XMHF limitation)");
		}
	}
	/* Enable NMI exiting because needed by quiesce */
	val |= (1U << VMX_PINBASED_NMI_EXITING);
	val |= (1U << VMX_PINBASED_VIRTUAL_NMIS);
	__vmx_vmwrite32(VMCSENC_control_VMX_pin_based, val);
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_VMX_pin_based_unused;
}

static void _vmcs02_to_vmcs12_control_VMX_pin_based(ARG01 * arg)
{
	u32 val = arg->vmcs12->control_VMX_pin_based;
	/* Enable NMI exiting because needed by quiesce */
	val |= (1U << VMX_PINBASED_NMI_EXITING);
	val |= (1U << VMX_PINBASED_VIRTUAL_NMIS);
	HALT_ON_ERRORCOND(val == __vmx_vmread32(VMCSENC_control_VMX_pin_based));
	(void)_vmcs02_to_vmcs12_control_VMX_pin_based_unused;
}

/* Primary processor-based VM-execution controls */

static u32 _vmcs12_to_vmcs02_control_VMX_cpu_based(ARG10 * arg)
{
	/*
	 * Note: this function needs to be called after
	 * _vmcs12_to_vmcs02_control_VMX_pin_based().
	 */
	u32 val = arg->vmcs12->control_VMX_cpu_based;
	/* Check for relationship between "virtual NMIs" and "NMI-window exiting" */
	arg->vmcs12_info->guest_nmi_window_exiting =
		_vmx_hasctl_nmi_window_exiting(arg->ctls);
	if (!arg->vmcs12_info->guest_virtual_nmis &&
		arg->vmcs12_info->guest_nmi_window_exiting) {
		return VM_INST_ERRNO_VMENTRY_INVALID_CTRL;
	}
	/* XMHF needs to activate secondary controls because of EPT */
	val |= (1U << VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS);
#ifdef __VMX_NESTED_MSR_BITMAP__
	/* XMHF does not use MSR bitmaps, but nested hypervisor may use them. */
	val &= ~(1U << VMX_PROCBASED_USE_MSR_BITMAPS);
#endif							/* __VMX_NESTED_MSR_BITMAP__ */
	__vmx_vmwrite32(VMCSENC_control_VMX_cpu_based, val);
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_VMX_cpu_based_unused;
}

static void _vmcs02_to_vmcs12_control_VMX_cpu_based(ARG01 * arg)
{
	u32 val12 = arg->vmcs12->control_VMX_cpu_based;
	u32 val02 = __vmx_vmread32(VMCSENC_control_VMX_cpu_based);
	/* Secondary controls are always required in VMCS02 for EPT */
	val12 |= (1U << VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS);
#ifdef __VMX_NESTED_MSR_BITMAP__
	/* XMHF does not use MSR bitmaps, but nested hypervisor may use them. */
	val12 &= ~(1U << VMX_PROCBASED_USE_MSR_BITMAPS);
#endif							/* __VMX_NESTED_MSR_BITMAP__ */
	/* NMI window exiting may change due to L0 */
	val12 &= ~(1U << VMX_PROCBASED_NMI_WINDOW_EXITING);
	val02 &= ~(1U << VMX_PROCBASED_NMI_WINDOW_EXITING);
	HALT_ON_ERRORCOND(val12 == val02);
	(void)_vmcs02_to_vmcs12_control_VMX_cpu_based_unused;
}

/* VM-exit controls */

static u32 _vmcs12_to_vmcs02_control_VM_exit_controls(ARG10 * arg)
{
	u32 val = arg->vmcs12->control_VM_exit_controls;
	u32 g64 = VCPU_g64(arg->vcpu);
	/* Check the "IA-32e mode guest" bit of the guest hypervisor */
	if (val & (1U << VMX_VMEXIT_HOST_ADDRESS_SPACE_SIZE)) {
		HALT_ON_ERRORCOND(g64);
	} else {
		HALT_ON_ERRORCOND(!g64);
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
	/* XMHF does not use save / load IA32_PAT / IA32_EFER */
	val &= ~(1U << VMX_VMEXIT_SAVE_IA32_PAT);
	val &= ~(1U << VMX_VMEXIT_LOAD_IA32_PAT);
	val &= ~(1U << VMX_VMEXIT_SAVE_IA32_EFER);
	val &= ~(1U << VMX_VMEXIT_LOAD_IA32_EFER);
	__vmx_vmwrite32(VMCSENC_control_VM_exit_controls, val);
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_VM_exit_controls_unused;
}

static void _vmcs02_to_vmcs12_control_VM_exit_controls(ARG01 * arg)
{
	u32 val = arg->vmcs12->control_VM_exit_controls;
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
	/* XMHF does not use save / load IA32_PAT / IA32_EFER */
	val &= ~(1U << VMX_VMEXIT_SAVE_IA32_PAT);
	val &= ~(1U << VMX_VMEXIT_LOAD_IA32_PAT);
	val &= ~(1U << VMX_VMEXIT_SAVE_IA32_EFER);
	val &= ~(1U << VMX_VMEXIT_LOAD_IA32_EFER);
	HALT_ON_ERRORCOND(val == __vmx_vmread32(encoding));
	(void)_vmcs02_to_vmcs12_control_VM_exit_controls_unused;
}

/* VM-exit MSR-store count */

static u32 _vmcs12_to_vmcs02_control_VM_exit_MSR_store_count(ARG10 * arg)
{
	/* VMCS02 needs to always process the same MSRs as VMCS01 */
	__vmx_vmwrite32(VMCSENC_control_VM_exit_MSR_store_count,
					arg->vcpu->vmcs.control_VM_exit_MSR_store_count);
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_VM_exit_MSR_store_count_unused;
}

static void _vmcs02_to_vmcs12_control_VM_exit_MSR_store_count(ARG01 * arg)
{
	u16 encoding = VMCSENC_control_VM_exit_MSR_store_count;
	HALT_ON_ERRORCOND(arg->vcpu->vmcs.control_VM_exit_MSR_store_count ==
					  __vmx_vmread32(encoding));
	(void)_vmcs02_to_vmcs12_control_VM_exit_MSR_store_count_unused;
}

/* VM-exit MSR-load count */

static u32 _vmcs12_to_vmcs02_control_VM_exit_MSR_load_count(ARG10 * arg)
{
	/* VMCS02 needs to always process the same MSRs as VMCS01 */
	__vmx_vmwrite32(VMCSENC_control_VM_exit_MSR_load_count,
					arg->vcpu->vmcs.control_VM_exit_MSR_load_count);
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_VM_exit_MSR_load_count_unused;
}

static void _vmcs02_to_vmcs12_control_VM_exit_MSR_load_count(ARG01 * arg)
{
	u16 encoding = VMCSENC_control_VM_exit_MSR_load_count;
	HALT_ON_ERRORCOND(arg->vcpu->vmcs.control_VM_exit_MSR_load_count ==
					  __vmx_vmread32(encoding));
	(void)_vmcs02_to_vmcs12_control_VM_exit_MSR_load_count_unused;
}

/* VM-entry controls */

static u32 _vmcs12_to_vmcs02_control_VM_entry_controls(ARG10 * arg)
{
	u32 val = arg->vmcs12->control_VM_entry_controls;
	/* XMHF does not use load IA32_PAT / IA32_EFER */
	val &= ~(1U << VMX_VMENTRY_LOAD_IA32_PAT);
	val &= ~(1U << VMX_VMENTRY_LOAD_IA32_EFER);
	__vmx_vmwrite32(VMCSENC_control_VM_entry_controls, val);
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_VM_entry_controls_unused;
}

static void _vmcs02_to_vmcs12_control_VM_entry_controls(ARG01 * arg)
{
	u32 val02 = __vmx_vmread32(VMCSENC_control_VM_entry_controls);
	u32 val12 = arg->vmcs12->control_VM_entry_controls;
	u32 mask = ~(1U << VMX_VMENTRY_IA_32E_MODE_GUEST);
	/* XMHF does not use load IA32_PAT / IA32_EFER */
	val12 &= ~(1U << VMX_VMENTRY_LOAD_IA32_PAT);
	val12 &= ~(1U << VMX_VMENTRY_LOAD_IA32_EFER);
	/* Check that other bits are not changed */
	HALT_ON_ERRORCOND((val12 & mask) == (val02 & mask));
	/* Copy "IA-32e mode guest" bit from VMCS02 to VMCS12 */
	arg->vmcs12->control_VM_entry_controls &= mask;
	arg->vmcs12->control_VM_entry_controls |= val02 & ~mask;
	(void)_vmcs02_to_vmcs12_control_VM_entry_controls_unused;
}

/* VM-entry MSR-load count */

static u32 _vmcs12_to_vmcs02_control_VM_entry_MSR_load_count(ARG10 * arg)
{
	/* VMCS02 needs to always process the same MSRs as VMCS01 */
	__vmx_vmwrite32(VMCSENC_control_VM_entry_MSR_load_count,
					arg->vcpu->vmcs.control_VM_entry_MSR_load_count);
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_VM_entry_MSR_load_count_unused;
}

static void _vmcs02_to_vmcs12_control_VM_entry_MSR_load_count(ARG01 * arg)
{
	u16 encoding = VMCSENC_control_VM_entry_MSR_load_count;
	HALT_ON_ERRORCOND(arg->vcpu->vmcs.control_VM_entry_MSR_load_count ==
					  __vmx_vmread32(encoding));
	(void)_vmcs02_to_vmcs12_control_VM_entry_MSR_load_count_unused;
}

/* VM-entry interruption-information field */

static u32 _vmcs12_to_vmcs02_control_VM_entry_interruption_information(ARG10 *
																	   arg)
{
	u32 val = arg->vmcs12->control_VM_entry_interruption_information;
	__vmx_vmwrite32(VMCSENC_control_VM_entry_interruption_information, val);
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_VM_entry_interruption_information_unused;
}

static void _vmcs02_to_vmcs12_control_VM_entry_interruption_information(ARG01 *
																		arg)
{
	/*
	 * VMCS02 may be changed during L2 -> L0 -> L2 VMEXITs. So don't copy to
	 * VMCS12. Only clear bit 31 as required by SDM.
	 */
	arg->vmcs12->control_VM_entry_interruption_information &=
		~INTR_INFO_VALID_MASK;
	(void)_vmcs02_to_vmcs12_control_VM_entry_interruption_information_unused;
}

/* VM-entry exception error code */

static u32 _vmcs12_to_vmcs02_control_VM_entry_exception_errorcode(ARG10 * arg)
{
	u32 val = arg->vmcs12->control_VM_entry_exception_errorcode;
	__vmx_vmwrite32(VMCSENC_control_VM_entry_exception_errorcode, val);
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_VM_entry_exception_errorcode_unused;
}

static void _vmcs02_to_vmcs12_control_VM_entry_exception_errorcode(ARG01 * arg)
{
	/*
	 * VMCS02 may be changed during L2 -> L0 -> L2 VMEXITs. So don't copy to
	 * VMCS12.
	 */
	(void)arg;
	(void)_vmcs02_to_vmcs12_control_VM_entry_exception_errorcode_unused;
}

/* VM-entry instruction length */

static u32 _vmcs12_to_vmcs02_control_VM_entry_instruction_length(ARG10 * arg)
{
	u32 val = arg->vmcs12->control_VM_entry_instruction_length;
	__vmx_vmwrite32(VMCSENC_control_VM_entry_instruction_length, val);
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_VM_entry_instruction_length_unused;
}

static void _vmcs02_to_vmcs12_control_VM_entry_instruction_length(ARG01 * arg)
{
	/*
	 * VMCS02 may be changed during L2 -> L0 -> L2 VMEXITs. So don't copy to
	 * VMCS12.
	 */
	(void)arg;
	(void)_vmcs02_to_vmcs12_control_VM_entry_instruction_length_unused;
}

/* Secondary processor-based VM-execution controls */

static u32 _vmcs12_to_vmcs02_control_VMX_seccpu_based(ARG10 * arg)
{
	/* Note: VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS is always enabled */
	u32 val = arg->vmcs12->control_VMX_seccpu_based;
	/* XMHF needs the guest to run in EPT to protect memory */
	val |= (1U << VMX_SECPROCBASED_ENABLE_EPT);
	__vmx_vmwrite32(VMCSENC_control_VMX_seccpu_based, val);
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_control_VMX_seccpu_based_unused;
}

static void _vmcs02_to_vmcs12_control_VMX_seccpu_based(ARG01 * arg)
{
	u32 val = arg->vmcs12->control_VMX_seccpu_based;
	u16 encoding = VMCSENC_control_VMX_seccpu_based;
	/* XMHF needs the guest to run in EPT to protect memory */
	val |= (1U << VMX_SECPROCBASED_ENABLE_EPT);
	HALT_ON_ERRORCOND(val == __vmx_vmread32(encoding));
	(void)_vmcs02_to_vmcs12_control_VMX_seccpu_based_unused;
}

/*
 * 32-Bit Read-Only Data Fields
 */

/*
 * 32-Bit Guest-State Fields
 */

/* Guest interruptibility state */

static u32 _vmcs12_to_vmcs02_guest_interruptibility(ARG10 * arg)
{
	u32 val = arg->vmcs12->guest_interruptibility;
	if (arg->vmcs12_info->guest_nmi_exiting) {
		if (arg->vmcs12_info->guest_virtual_nmis) {
			/* NMI Exiting = 1, virtual NMIs = 1 */
			arg->vmcs12_info->guest_block_nmi = false;
		} else {
			/* NMI Exiting = 1, virtual NMIs = 0 */
			arg->vmcs12_info->guest_block_nmi = val & VMX_GUEST_INTR_BLOCK_NMI;
		}
	} else {
		/* NMI Exiting = 0, virtual NMIs = 0, guest_block_nmi is ignored */
	}
	HALT_ON_ERRORCOND(!arg->vmcs12_info->guest_vmcs_block_nmi_overridden);
	__vmx_vmwrite32(VMCSENC_guest_interruptibility, val);
	return VM_INST_SUCCESS;
	(void)_vmcs12_to_vmcs02_guest_interruptibility_unused;
}

static void _vmcs02_to_vmcs12_guest_interruptibility(ARG01 * arg)
{
	/* Handle "Blocking by NMI" */
	u32 val = __vmx_vmread32(VMCSENC_guest_interruptibility);
	if (arg->vmcs12_info->guest_vmcs_block_nmi_overridden) {
		arg->vmcs12_info->guest_vmcs_block_nmi_overridden = false;
		if (arg->vmcs12_info->guest_vmcs_block_nmi) {
			val |= VMX_GUEST_INTR_BLOCK_NMI;
		} else {
			val &= ~VMX_GUEST_INTR_BLOCK_NMI;
		}
	}
	if (arg->vmcs12_info->guest_nmi_exiting) {
		/* Copy guest NMI blocking to host (VMCS01) */
		if (arg->vmcs12_info->guest_block_nmi) {
			arg->vcpu->vmcs.guest_interruptibility |= VMX_GUEST_INTR_BLOCK_NMI;
		} else {
			arg->vcpu->vmcs.guest_interruptibility &= ~VMX_GUEST_INTR_BLOCK_NMI;
		}
		/* Set guest interruptibility state in VMCS12 */
		if (!arg->vmcs12_info->guest_virtual_nmis) {
			if (arg->vmcs12_info->guest_block_nmi) {
				val |= VMX_GUEST_INTR_BLOCK_NMI;
			} else {
				val &= ~VMX_GUEST_INTR_BLOCK_NMI;
			}
		}
	} else {
		/* Copy guest NMI blocking to host (VMCS01) */
		if (val & VMX_GUEST_INTR_BLOCK_NMI) {
			arg->vcpu->vmcs.guest_interruptibility |= VMX_GUEST_INTR_BLOCK_NMI;
		} else {
			arg->vcpu->vmcs.guest_interruptibility &= ~VMX_GUEST_INTR_BLOCK_NMI;
		}
	}
	arg->vmcs12->guest_interruptibility = val;
	/* There is no blocking by STI or by MOV SS after a VM exit */
	arg->vcpu->vmcs.guest_interruptibility &= ~((1U << 0) | (1U << 1));
	(void)_vmcs02_to_vmcs12_guest_interruptibility_unused;
}

/*
 * 32-Bit Host-State Field
 */

/*
 * Natural-Width Control Fields
 */

/*
 * Natural-Width Read-Only Data Fields
 */

/*
 * Natural-Width Guest-State Fields
 */

/*
 * Natural-Width Host-State Fields
 */

/*
 * Translate VMCS12 (vmcs12) to VMCS02 (already loaded as current VMCS).
 * Return an error code following VM instruction error number, or 0 when
 * success.
 */
u32 xmhf_nested_arch_x86vmx_vmcs12_to_vmcs02(VCPU * vcpu,
											 vmcs12_info_t * vmcs12_info)
{
	struct _vmx_vmcsfields *vmcs12 = &vmcs12_info->vmcs12_value;
	guestmem_hptw_ctx_pair_t ctx_pair;
	msr_entry_t *msr01 = (msr_entry_t *) vcpu->vmx_vaddr_msr_area_guest;
	msr_entry_t *msr02 = vmcs12_info->vmcs02_vmentry_msr_load_area;
	u32 ia32_pat_index;
	u32 ia32_efer_index;
	u32 status = _vmcs12_get_ctls(vcpu, vmcs12, &vmcs12_info->ctls12);
	ARG10 arg = {
		.vcpu = vcpu,
		.vmcs12_info = vmcs12_info,
		.vmcs12 = vmcs12,
		.ctls = &vmcs12_info->ctls12,
		.ctx_pair = &ctx_pair,
		.guest_ia32_pat = 0,
		.guest_ia32_efer = 0,
		.ia32_pat_index = 0,
		.ia32_efer_index = 0,
		.msr01 = msr01,
	};
	if (status != 0) {
		return status;
	}
	guestmem_init(vcpu, &ctx_pair);
	if (!xmhf_partition_arch_x86vmx_get_xmhf_msr(MSR_IA32_PAT, &ia32_pat_index)) {
		HALT_ON_ERRORCOND(0 && "MSR_IA32_PAT not found");
	}
	arg.ia32_pat_index = ia32_pat_index;
	if (!xmhf_partition_arch_x86vmx_get_xmhf_msr(MSR_EFER, &ia32_efer_index)) {
		HALT_ON_ERRORCOND(0 && "MSR_EFER not found");
	}
	arg.ia32_efer_index = ia32_efer_index;
	/* TODO: Check settings of VMX controls and host-state area */

#define DECLARE_FIELD_16_RW(encoding, name, ...) \
	{ \
		u32 status = _vmcs12_to_vmcs02_##name(&arg); \
		if (status != VM_INST_SUCCESS) { \
			return status; \
		} \
	}
#define DECLARE_FIELD_64_RW(...) DECLARE_FIELD_16_RW(__VA_ARGS__)
#define DECLARE_FIELD_32_RW(...) DECLARE_FIELD_16_RW(__VA_ARGS__)
#define DECLARE_FIELD_NW_RW(...) DECLARE_FIELD_16_RW(__VA_ARGS__)
#include "nested-x86vmx-vmcs12-fields.h"

	/* Perform MSR load */
	{
		u32 i;
		gva_t guest_addr = vmcs12->control_VM_entry_MSR_load_address;

		/* Set IA32_PAT and IA32_EFER in VMCS02 guest */
		msr02[ia32_pat_index].data = arg.guest_ia32_pat;
		msr02[ia32_efer_index].data = arg.guest_ia32_efer;

		/* Write the MSRs requested by guest */
		for (i = 0; i < vmcs12->control_VM_entry_MSR_load_count; i++) {
			u32 index;
			msr_entry_t msr12;
			guestmem_copy_gp2h(&ctx_pair, 0, &msr12,
							   guest_addr + sizeof(msr_entry_t) * i,
							   sizeof(msr_entry_t));
			switch (msr12.index) {
			case IA32_SYSENTER_CS_MSR:
				__vmx_vmwrite32(VMCSENC_guest_SYSENTER_CS, (u32) msr12.data);
				break;
			case IA32_SYSENTER_EIP_MSR:
				__vmx_vmwriteNW(VMCSENC_guest_SYSENTER_EIP,
								(ulong_t) msr12.data);
				break;
			case IA32_SYSENTER_ESP_MSR:
				__vmx_vmwriteNW(VMCSENC_guest_SYSENTER_ESP,
								(ulong_t) msr12.data);
				break;
			case IA32_MSR_FS_BASE:	/* fallthrough */
			case IA32_MSR_GS_BASE:
				/* Likely need to fail VMENTRY, but need to double check. */
				HALT_ON_ERRORCOND(0 && "Not allowed, what should I do?");
				break;
			default:
				if ((msr12.index & 0xffffff00U) == 0x00000800U) {
					/* Likely need to fail VMENTRY, but need to double check. */
					HALT_ON_ERRORCOND(0 && "Not allowed, what should I do?");
				} else if (xmhf_partition_arch_x86vmx_get_xmhf_msr(msr12.index,
																   &index)) {
					HALT_ON_ERRORCOND(msr02[index].index == msr12.index);
					msr02[index].data = msr12.data;
				} else {
					if (xmhf_parteventhub_arch_x86vmx_handle_wrmsr
						(vcpu, msr12.index, msr12.data)) {
						/*
						 * Likely need to fail VMENTRY, but need to double
						 * check.
						 */
						HALT_ON_ERRORCOND(0 && "WRMSR fail, what should I do?");
					}
				}
				break;
			}
		}
	}

	return VM_INST_SUCCESS;
}

/*
 * Perform operations in xmhf_nested_arch_x86vmx_vmcs12_to_vmcs02() that depend
 * on walking EPT01. This is intended to be called when XMHF or hypapp decides
 * to flush EPT. As a rule of thumb, functions called by
 * xmhf_nested_arch_x86vmx_vmcs12_to_vmcs02() that uses arg->ctx_pair should
 * also be called by this function.
 */
void xmhf_nested_arch_x86vmx_rewalk_ept01(VCPU * vcpu,
										  vmcs12_info_t * vmcs12_info)
{
	struct _vmx_vmcsfields *vmcs12 = &vmcs12_info->vmcs12_value;
	guestmem_hptw_ctx_pair_t ctx_pair;
	ARG10 arg = {
		.vcpu = vcpu,
		.vmcs12_info = vmcs12_info,
		.vmcs12 = vmcs12,
		.ctls = &vmcs12_info->ctls12,
		.ctx_pair = &ctx_pair,
		/* All fields below are not used */
		.guest_ia32_pat = 0,
		.guest_ia32_efer = 0,
		.ia32_pat_index = 0,
		.ia32_efer_index = 0,
		.msr01 = NULL,
	};
	guestmem_init(vcpu, &ctx_pair);

#define DECLARE_FIELD_64_RW(encoding, name, prop, ...) \
	if (prop & FIELD_PROP_GPADDR) { \
		HALT_ON_ERRORCOND(_vmcs12_to_vmcs02_##name(&arg) == VM_INST_SUCCESS); \
	}
#include "nested-x86vmx-vmcs12-fields.h"

	/* Special handling for EPT02 */
	_rewalk_ept01_control_EPT_pointer(&arg);
}

/*
 * Translate VMCS02 (already loaded as current VMCS) to VMCS12 (vmcs12)
 */
void xmhf_nested_arch_x86vmx_vmcs02_to_vmcs12(VCPU * vcpu,
											  vmcs12_info_t * vmcs12_info)
{
	struct _vmx_vmcsfields *vmcs12 = &vmcs12_info->vmcs12_value;
	guestmem_hptw_ctx_pair_t ctx_pair;
	msr_entry_t *msr01 = (msr_entry_t *) vcpu->vmx_vaddr_msr_area_guest;
	msr_entry_t *msr02 = vmcs12_info->vmcs02_vmentry_msr_load_area;
	u32 ia32_pat_index;
	u32 ia32_efer_index;
	ARG01 arg = {
		.vcpu = vcpu,
		.vmcs12_info = vmcs12_info,
		.vmcs12 = vmcs12,
		.ctls = &vmcs12_info->ctls12,
		.host_ia32_pat = 0,
		.host_ia32_efer = 0,
		.ia32_pat_index = 0,
		.ia32_efer_index = 0,
		.msr02 = msr02,
	};

	guestmem_init(vcpu, &ctx_pair);
	if (!xmhf_partition_arch_x86vmx_get_xmhf_msr(MSR_IA32_PAT, &ia32_pat_index)) {
		HALT_ON_ERRORCOND(0 && "MSR_IA32_PAT not found");
	}
	arg.ia32_pat_index = ia32_pat_index;
	if (!xmhf_partition_arch_x86vmx_get_xmhf_msr(MSR_EFER, &ia32_efer_index)) {
		HALT_ON_ERRORCOND(0 && "MSR_EFER not found");
	}
	arg.ia32_efer_index = ia32_efer_index;

#define DECLARE_FIELD_16(encoding, name, ...) \
	{ \
		_vmcs02_to_vmcs12_##name(&arg); \
	}
#define DECLARE_FIELD_64(...) DECLARE_FIELD_16(__VA_ARGS__)
#define DECLARE_FIELD_32(...) DECLARE_FIELD_16(__VA_ARGS__)
#define DECLARE_FIELD_NW(...) DECLARE_FIELD_16(__VA_ARGS__)
#include "nested-x86vmx-vmcs12-fields.h"

	/* Perform MSR load / store */
	{
		u32 i;
		gva_t guest_addr = vmcs12->control_VM_exit_MSR_store_address;

		/* Read MSRs and write to guest */
		for (i = 0; i < vmcs12->control_VM_exit_MSR_store_count; i++) {
			u32 index;
			msr_entry_t msr12;
			guestmem_copy_gp2h(&ctx_pair, 0, &msr12,
							   guest_addr + sizeof(msr_entry_t) * i,
							   sizeof(msr_entry_t));
			switch (msr12.index) {
			case IA32_SYSENTER_CS_MSR:
				msr12.data = (u64) __vmx_vmread32(VMCSENC_guest_SYSENTER_CS);
				break;
			case IA32_SYSENTER_EIP_MSR:
				msr12.data = (u64) __vmx_vmreadNW(VMCSENC_guest_SYSENTER_EIP);
				break;
			case IA32_SYSENTER_ESP_MSR:
				msr12.data = (u64) __vmx_vmreadNW(VMCSENC_guest_SYSENTER_ESP);
				break;
			case IA32_MSR_FS_BASE:
				msr12.data = (u64) __vmx_vmreadNW(VMCSENC_guest_FS_base);
				break;
			case IA32_MSR_GS_BASE:
				msr12.data = (u64) __vmx_vmreadNW(VMCSENC_guest_GS_base);
				break;
			default:
				if (xmhf_partition_arch_x86vmx_get_xmhf_msr(msr12.index,
															&index)) {
					msr_entry_t *msr02 =
						vmcs12_info->vmcs02_vmexit_msr_store_area;
					HALT_ON_ERRORCOND(msr02[index].index == msr12.index);
					msr12.data = msr02[index].data;
				} else {
					if (xmhf_parteventhub_arch_x86vmx_handle_rdmsr
						(vcpu, msr12.index, &msr12.data)) {
						/*
						 * Likely need to fail VMEXIT, but need to double check.
						 */
						HALT_ON_ERRORCOND(0 && "RDMSR fail, what should I do?");
					}
				}
				break;
			}
			guestmem_copy_h2gp(&ctx_pair, 0,
							   guest_addr + sizeof(msr_entry_t) * i,
							   &msr12, sizeof(msr_entry_t));
		}
	}
	{
		u32 i;
		gva_t guest_addr = vmcs12->control_VM_exit_MSR_load_address;

		/* Set IA32_PAT and IA32_EFER in VMCS01 guest */
		msr01[ia32_pat_index].data = arg.host_ia32_pat;
		msr01[ia32_efer_index].data = arg.host_ia32_efer;

		/* Write MSRs as requested by guest */
		for (i = 0; i < vmcs12->control_VM_exit_MSR_load_count; i++) {
			u32 index;
			msr_entry_t msr12;
			guestmem_copy_gp2h(&ctx_pair, 0, &msr12,
							   guest_addr + sizeof(msr_entry_t) * i,
							   sizeof(msr_entry_t));
			switch (msr12.index) {
			case IA32_SYSENTER_CS_MSR:
				vcpu->vmcs.guest_SYSENTER_CS = (u32) msr12.data;
				break;
			case IA32_SYSENTER_EIP_MSR:
				vcpu->vmcs.guest_SYSENTER_EIP = (ulong_t) msr12.data;
				break;
			case IA32_SYSENTER_ESP_MSR:
				vcpu->vmcs.guest_SYSENTER_ESP = (ulong_t) msr12.data;
				break;
			case IA32_MSR_FS_BASE:	/* fallthrough */
			case IA32_MSR_GS_BASE:
				/* Likely need to fail VMEXIT, but need to double check. */
				HALT_ON_ERRORCOND(0 && "Not allowed, what should I do?");
				break;
			default:
				if ((msr12.index & 0xffffff00U) == 0x00000800U) {
					/* Likely need to fail VMEXIT, but need to double check. */
					HALT_ON_ERRORCOND(0 && "Not allowed, what should I do?");
				} else if (xmhf_partition_arch_x86vmx_get_xmhf_msr(msr12.index,
																   &index)) {
					HALT_ON_ERRORCOND(msr01[index].index == msr12.index);
					msr01[index].data = msr12.data;
				} else {
					if (xmhf_parteventhub_arch_x86vmx_handle_wrmsr
						(vcpu, msr12.index, msr12.data)) {
						/*
						 * Likely need to fail VMEXIT, but need to double check.
						 */
						HALT_ON_ERRORCOND(0 && "WRMSR fail, what should I do?");
					}
				}
				break;
			}
		}
	}

	/* 16-Bit fields: VMCS12 host -> VMCS01 guest */
	{
		/*
		 * SDM volume 3 26.5.2 "Loading Host Segment and Descriptor-Table
		 * Registers": "the selector is cleared to 0000H".
		 */
		vcpu->vmcs.guest_LDTR_selector = 0x0000U;
	}

	/* 64-Bit fields: VMCS12 host -> VMCS01 guest */
	{
		/* The IA32_DEBUGCTL MSR is cleared to 00000000_00000000H */
		vcpu->vmcs.guest_IA32_DEBUGCTL = 0ULL;
	}

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
		if (_vmx_hasctl_vmexit_host_address_space_size(&vmcs12_info->ctls12)) {
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

	/* Natural-Width fields: VMCS12 host -> VMCS01 guest */
	{
		/*
		 * CR4.PAE is set to 1 if the "host address-space size" VM-exit control
		 * is 1. CR4.PCIDE is set to 0 if the “host address-space size” VM-exit
		 * control is 0.
		 */
		if (_vmx_hasctl_vmexit_host_address_space_size(&vmcs12_info->ctls12)) {
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
}

#ifdef __DEBUG_QEMU__
/*
 * Check whether VMCS fields exist as specified in the SDM. Return true if
 * everything is well.
 */
bool xmhf_nested_arch_x86vmx_check_fields_existence(VCPU * vcpu)
{
	bool success = true;
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
