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

/*
 * EMHF base platform component interface, x86 vmx backend
 * VMCS to memory interface
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>

/* Write 16-bit VMCS field, never fails */
void __vmx_vmwrite16(u16 encoding, u16 value) {
	HALT_ON_ERRORCOND((encoding >> 12) == 0UL);
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding, value));
}

/* Write 64-bit VMCS field, never fails */
void __vmx_vmwrite64(u16 encoding, u64 value) {
	HALT_ON_ERRORCOND((encoding >> 12) == 2UL);
	HALT_ON_ERRORCOND((encoding & 0x1) == 0x0);
#ifdef __AMD64__
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding, value));
#elif defined(__I386__)
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding, value));
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding + 1, value >> 32));
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
}

/* Write 32-bit VMCS field, never fails */
void __vmx_vmwrite32(u16 encoding, u32 value) {
	HALT_ON_ERRORCOND((encoding >> 12) == 4UL);
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding, value));
}

/* Write natural width (NW) VMCS field, never fails */
void __vmx_vmwriteNW(u16 encoding, ulong_t value) {
	HALT_ON_ERRORCOND((encoding >> 12) == 6UL);
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding, value));
}

/* Read 16-bit VMCS field, never fails */
u16 __vmx_vmread16(u16 encoding) {
	unsigned long value;
	HALT_ON_ERRORCOND((encoding >> 12) == 0UL);
	HALT_ON_ERRORCOND(__vmx_vmread(encoding, &value));
	HALT_ON_ERRORCOND(value == (unsigned long)(u16)value);
	return value;
}

/* Read 64-bit VMCS field, never fails */
u64 __vmx_vmread64(u16 encoding) {
#ifdef __AMD64__
	unsigned long value;
	HALT_ON_ERRORCOND((encoding >> 12) == 2UL);
	HALT_ON_ERRORCOND(__vmx_vmread(encoding, &value));
	return value;
#elif defined(__I386__)
	union {
		struct {
			unsigned long low, high;
		};
		u64 full;
	} ans;
	_Static_assert(sizeof(u32) == sizeof(unsigned long), "incorrect size");
	HALT_ON_ERRORCOND((encoding >> 12) == 2UL);
	HALT_ON_ERRORCOND((encoding & 0x1) == 0x0);
	HALT_ON_ERRORCOND(__vmx_vmread(encoding, &ans.low));
	HALT_ON_ERRORCOND(__vmx_vmread(encoding + 1, &ans.high));
	return ans.full;
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
}

/* Read 32-bit VMCS field, never fails */
u32 __vmx_vmread32(u16 encoding) {
	unsigned long value;
	HALT_ON_ERRORCOND((encoding >> 12) == 4UL);
	HALT_ON_ERRORCOND(__vmx_vmread(encoding, &value));
	HALT_ON_ERRORCOND(value == (unsigned long)(u32)value);
	return value;
}

/* Read natural width (NW) VMCS field, never fails */
ulong_t __vmx_vmreadNW(u16 encoding) {
	unsigned long value;
	HALT_ON_ERRORCOND((encoding >> 12) == 6UL);
	HALT_ON_ERRORCOND(__vmx_vmread(encoding, &value));
	HALT_ON_ERRORCOND(value == (unsigned long)(ulong_t)value);
	return value;
}

//---putVMCS--------------------------------------------------------------------
// routine takes vcpu vmcsfields and stores it in the CPU VMCS
void xmhf_baseplatform_arch_x86vmx_putVMCS(VCPU *vcpu){
#define FIELD_CTLS_ARG (&vcpu->vmx_caps)
#define DECLARE_FIELD_16_RW(encoding, name, exist, ...) \
    if (exist) { \
        __vmx_vmwrite16(encoding, vcpu->vmcs.name); \
    }
#define DECLARE_FIELD_64_RW(encoding, name, exist, ...) \
    if (exist) { \
        __vmx_vmwrite64(encoding, vcpu->vmcs.name); \
    }
#define DECLARE_FIELD_32_RW(encoding, name, exist, ...) \
    if (exist) { \
        __vmx_vmwrite32(encoding, vcpu->vmcs.name); \
    }
#define DECLARE_FIELD_NW_RW(encoding, name, exist, ...) \
    if (exist) { \
        __vmx_vmwriteNW(encoding, vcpu->vmcs.name); \
    }
#include <arch/x86/_vmx_vmcs_fields.h>
}

//---getVMCS--------------------------------------------------------------------
// routine takes CPU VMCS and stores it in vcpu vmcsfields
void xmhf_baseplatform_arch_x86vmx_getVMCS(VCPU *vcpu){
#define FIELD_CTLS_ARG (&vcpu->vmx_caps)
#define DECLARE_FIELD_16(encoding, name, exist, ...) \
    if (exist) { \
        vcpu->vmcs.name = __vmx_vmread16(encoding); \
    }
#define DECLARE_FIELD_64(encoding, name, exist, ...) \
    if (exist) { \
        vcpu->vmcs.name = __vmx_vmread64(encoding); \
    }
#define DECLARE_FIELD_32(encoding, name, exist, ...) \
    if (exist) { \
        vcpu->vmcs.name = __vmx_vmread32(encoding); \
    }
#define DECLARE_FIELD_NW(encoding, name, exist, ...) \
    if (exist) { \
        vcpu->vmcs.name = __vmx_vmreadNW(encoding); \
    }
#include <arch/x86/_vmx_vmcs_fields.h>
}

//--debug: dump_vcpu dumps vcpu contents (including VMCS)-----------------------
void xmhf_baseplatform_arch_x86vmx_dump_vcpu(VCPU *vcpu){
    u32 i = 0;

#define DUMP_VCPU_PRINT_INT16(x) \
    { _Static_assert(sizeof(x) == sizeof(u16), "incorrect size"); } \
    printf("CPU(0x%02x): " #x "=0x%04x\n", (u32) vcpu->id, (x));
#define DUMP_VCPU_PRINT_INT32(x) \
    { _Static_assert(sizeof(x) == sizeof(u32), "incorrect size"); } \
    printf("CPU(0x%02x): " #x "=0x%08x\n", vcpu->id, (x));
#define DUMP_VCPU_PRINT_INT64(x) \
    { _Static_assert(sizeof(x) == sizeof(u64), "incorrect size"); } \
    printf("CPU(0x%02x): " #x "=0x%016lx\n", vcpu->id, (x));
#define DUMP_VCPU_PRINT_INT64_INDEX(x, i) \
    { _Static_assert(sizeof((x)[i]) == sizeof(u64), "incorrect size"); } \
    printf("CPU(0x%02x): " #x "[%x]=0x%016lx\n", vcpu->id, (i), (x)[i]);
#ifdef __AMD64__
#define DUMP_VCPU_PRINT_INTNW(x) DUMP_VCPU_PRINT_INT64(x)
#elif defined(__I386__)
#define DUMP_VCPU_PRINT_INTNW(x) DUMP_VCPU_PRINT_INT32(x)
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */

#ifdef __AMD64__
    DUMP_VCPU_PRINT_INT64(vcpu->rsp);
#elif defined(__I386__)
    DUMP_VCPU_PRINT_INT32(vcpu->esp);
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
    DUMP_VCPU_PRINT_INTNW(vcpu->sipi_page_vaddr);
    DUMP_VCPU_PRINT_INT32(vcpu->id);
    DUMP_VCPU_PRINT_INT32(vcpu->idx);
    DUMP_VCPU_PRINT_INT32(vcpu->sipivector);
    DUMP_VCPU_PRINT_INT32(vcpu->sipireceived);
    DUMP_VCPU_PRINT_INT32(vcpu->cpu_vendor);
    DUMP_VCPU_PRINT_INT32(vcpu->isbsp);
    DUMP_VCPU_PRINT_INT32(vcpu->quiesced);
    DUMP_VCPU_PRINT_INTNW(vcpu->hsave_vaddr_ptr);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcb_vaddr_ptr);
    DUMP_VCPU_PRINT_INTNW(vcpu->npt_vaddr_ptr);
    DUMP_VCPU_PRINT_INTNW(vcpu->npt_vaddr_pdts);
    DUMP_VCPU_PRINT_INT32(vcpu->npt_asid);
    DUMP_VCPU_PRINT_INTNW(vcpu->npt_vaddr_pts);
    DUMP_VCPU_PRINT_INTNW(vcpu->svm_vaddr_iobitmap);
    for (i = 0; i < IA32_VMX_MSRCOUNT; i++) {
        DUMP_VCPU_PRINT_INT64_INDEX(vcpu->vmx_msrs, i);
    }
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_pinbased_ctls);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_procbased_ctls);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_exit_ctls);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_entry_ctls);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmx_vmxonregion_vaddr);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmx_vmcs_vaddr);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmx_vaddr_iobitmap);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmx_vaddr_msr_area_host);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmx_vaddr_msr_area_guest);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmx_vaddr_msrbitmaps);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmx_vaddr_ept_pml4_table);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmx_vaddr_ept_pdp_table);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmx_vaddr_ept_pd_tables);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmx_vaddr_ept_p_tables);
    DUMP_VCPU_PRINT_INT32(vcpu->vmx_ept_defaulttype);
    DUMP_VCPU_PRINT_INT32(vcpu->vmx_ept_mtrr_enable);
    DUMP_VCPU_PRINT_INT32(vcpu->vmx_ept_fixmtrr_enable);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_ept_paddrmask);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_guestmtrrmsrs.def_type);
    for (i = 0; i < NUM_FIXED_MTRRS; i++) {
        DUMP_VCPU_PRINT_INT64_INDEX(vcpu->vmx_guestmtrrmsrs.fix_mtrrs, i);
    }
    DUMP_VCPU_PRINT_INT32(vcpu->vmx_guestmtrrmsrs.var_count);
    // Skip: vcpu->vmx_guestmtrrmsrs.var_mtrrs
    DUMP_VCPU_PRINT_INT32(vcpu->vmx_guest_unrestricted);
#define DECLARE_FIELD_16(encoding, name, ...) \
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.name);
#define DECLARE_FIELD_64(encoding, name, ...) \
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.name);
#define DECLARE_FIELD_32(encoding, name, ...) \
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.name);
#define DECLARE_FIELD_NW(encoding, name, ...) \
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.name);
#include <arch/x86/_vmx_vmcs_fields.h>

#undef DUMP_VCPU_PRINT_INT16
#undef DUMP_VCPU_PRINT_INT32
#undef DUMP_VCPU_PRINT_INT64
#undef DUMP_VCPU_PRINT_INT64_INDEX
#undef DUMP_VCPU_PRINT_INTNW

}
