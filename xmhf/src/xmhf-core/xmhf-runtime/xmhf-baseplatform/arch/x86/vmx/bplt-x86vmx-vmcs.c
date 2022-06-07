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
void __vmx_vmwrite16(unsigned long encoding, u16 value) {
	HALT_ON_ERRORCOND((encoding >> 12) == 0UL);
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding, value));
}

/* Write 64-bit VMCS field, never fails */
void __vmx_vmwrite64(unsigned long encoding, u64 value) {
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
void __vmx_vmwrite32(unsigned long encoding, u32 value) {
	HALT_ON_ERRORCOND((encoding >> 12) == 4UL);
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding, value));
}

/* Write natural width (NW) VMCS field, never fails */
void __vmx_vmwriteNW(unsigned long encoding, ulong_t value) {
	HALT_ON_ERRORCOND((encoding >> 12) == 6UL);
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding, value));
}

/* Read 16-bit VMCS field, never fails */
u16 __vmx_vmread16(unsigned long encoding) {
	unsigned long value;
	HALT_ON_ERRORCOND((encoding >> 12) == 0UL);
	HALT_ON_ERRORCOND(__vmx_vmread(encoding, &value));
	HALT_ON_ERRORCOND(value == (unsigned long)(u16)value);
	return value;
}

/* Read 64-bit VMCS field, never fails */
u64 __vmx_vmread64(unsigned long encoding) {
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
u32 __vmx_vmread32(unsigned long encoding) {
	unsigned long value;
	HALT_ON_ERRORCOND((encoding >> 12) == 4UL);
	HALT_ON_ERRORCOND(__vmx_vmread(encoding, &value));
	HALT_ON_ERRORCOND(value == (unsigned long)(u32)value);
	return value;
}

/* Read natural width (NW) VMCS field, never fails */
ulong_t __vmx_vmreadNW(unsigned long encoding) {
	unsigned long value;
	HALT_ON_ERRORCOND((encoding >> 12) == 6UL);
	HALT_ON_ERRORCOND(__vmx_vmread(encoding, &value));
	HALT_ON_ERRORCOND(value == (unsigned long)(ulong_t)value);
	return value;
}

static void xmhf_baseplatform_arch_x86vmx_write_field(u32 encoding, void *addr,
                                                      u32 size) {
    switch ((encoding >> 13) & 0x3) {
    case 0: {
        /* 16-bit */
        HALT_ON_ERRORCOND(size == sizeof(u16));
        __vmx_vmwrite16(encoding, *(u16 *)addr);
        break;
    }
    case 1: {
        /* 64-bit */
        HALT_ON_ERRORCOND(size == sizeof(u64));
        __vmx_vmwrite64(encoding, *(u64 *)addr);
        break;
    }
    case 2: {
        /* 32-bit */
        HALT_ON_ERRORCOND(size == sizeof(u32));
        __vmx_vmwrite32(encoding, *(u32 *)addr);
        break;
    }
    case 3: {
        /* natural width */
        HALT_ON_ERRORCOND(size == sizeof(ulong_t));
        __vmx_vmwriteNW(encoding, *(ulong_t *)addr);
        break;
    }
    default:
        HALT();
    }
}

//---putVMCS--------------------------------------------------------------------
// routine takes vcpu vmcsfields and stores it in the CPU VMCS
void xmhf_baseplatform_arch_x86vmx_putVMCS(VCPU *vcpu){
    unsigned int i;
    for(i=0; i < g_vmx_vmcsrwfields_encodings_count; i++){
      u32 encoding = g_vmx_vmcsrwfields_encodings[i].encoding;
      u32 offset = g_vmx_vmcsrwfields_encodings[i].fieldoffset;
      void *field = (void *)((hva_t)&vcpu->vmcs + offset);
      u32 size = g_vmx_vmcsrwfields_encodings[i].membersize;
      xmhf_baseplatform_arch_x86vmx_write_field(encoding, field, size);
    }
}

static void xmhf_baseplatform_arch_x86vmx_read_field(u32 encoding, void *addr,
                                                    u32 size) {
    switch ((encoding >> 13) & 0x3) {
    case 0: {
        /* 16-bit */
        HALT_ON_ERRORCOND(size == sizeof(u16));
        *(u16 *)addr = __vmx_vmread16(encoding);
        break;
    }
    case 1: {
        /* 64-bit */
        HALT_ON_ERRORCOND(size == sizeof(u64));
        *(u64 *)addr = __vmx_vmread64(encoding);
        break;
    }
    case 2: {
        /* 32-bit */
        HALT_ON_ERRORCOND(size == sizeof(u32));
        *(u32 *)addr = __vmx_vmread32(encoding);
        break;
    }
    case 3: {
        /* natural width */
        HALT_ON_ERRORCOND(size == sizeof(ulong_t));
        *(ulong_t *)addr = __vmx_vmreadNW(encoding);
        break;
    }
    default:
        HALT();
    }
}

//---getVMCS--------------------------------------------------------------------
// routine takes CPU VMCS and stores it in vcpu vmcsfields
void xmhf_baseplatform_arch_x86vmx_getVMCS(VCPU *vcpu){
    unsigned int i;
    for(i=0; i < g_vmx_vmcsrwfields_encodings_count; i++){
        u32 encoding = g_vmx_vmcsrwfields_encodings[i].encoding;
        u32 offset = g_vmx_vmcsrwfields_encodings[i].fieldoffset;
        void *field = (void *)((hva_t)&vcpu->vmcs + offset);
        u32 size = g_vmx_vmcsrwfields_encodings[i].membersize;
        xmhf_baseplatform_arch_x86vmx_read_field(encoding, field, size);
    }
    for(i=0; i < g_vmx_vmcsrofields_encodings_count; i++){
        u32 encoding = g_vmx_vmcsrofields_encodings[i].encoding;
        u32 offset = g_vmx_vmcsrofields_encodings[i].fieldoffset;
        void *field = (void *)((hva_t)&vcpu->vmcs + offset);
        u32 size = g_vmx_vmcsrofields_encodings[i].membersize;
        xmhf_baseplatform_arch_x86vmx_read_field(encoding, field, size);
    }
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
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.control_vpid);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_VMX_pin_based);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_VMX_cpu_based);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_VMX_seccpu_based);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_exception_bitmap);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_pagefault_errorcode_mask);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_pagefault_errorcode_match);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_CR3_target_count);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_VM_exit_controls);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_VM_exit_MSR_store_count);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_VM_exit_MSR_load_count);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_VM_entry_controls);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_VM_entry_MSR_load_count);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_VM_entry_interruption_information);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_VM_entry_exception_errorcode);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_VM_entry_instruction_length);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.control_Task_PRivilege_Threshold);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.control_CR0_mask);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.control_CR4_mask);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.control_CR0_shadow);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.control_CR4_shadow);
#ifndef __DEBUG_QEMU__
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.control_CR3_target0);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.control_CR3_target1);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.control_CR3_target2);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.control_CR3_target3);
#endif /* !__DEBUG_QEMU__ */
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_IO_BitmapA_address);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_IO_BitmapB_address);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_MSR_Bitmaps_address);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_VM_exit_MSR_store_address);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_VM_exit_MSR_load_address);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_VM_entry_MSR_load_address);
#ifndef __DEBUG_QEMU__
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_Executive_VMCS_pointer);
#endif /* !__DEBUG_QEMU__ */
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_TSC_offset);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_virtual_APIC_page_address);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_EPT_pointer);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.host_CR0);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.host_CR3);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.host_CR4);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.host_FS_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.host_GS_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.host_TR_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.host_GDTR_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.host_IDTR_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.host_SYSENTER_ESP);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.host_SYSENTER_EIP);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.host_RSP);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.host_RIP);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.host_SYSENTER_CS);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.host_ES_selector);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.host_CS_selector);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.host_SS_selector);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.host_DS_selector);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.host_FS_selector);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.host_GS_selector);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.host_TR_selector);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_CR0);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_CR3);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_CR4);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_ES_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_CS_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_SS_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_DS_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_FS_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_GS_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_LDTR_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_TR_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_GDTR_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_IDTR_base);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_DR7);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_RSP);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_RIP);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_RFLAGS);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_pending_debug_x);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_SYSENTER_ESP);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.guest_SYSENTER_EIP);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_ES_limit);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_CS_limit);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_SS_limit);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_DS_limit);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_FS_limit);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_GS_limit);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_LDTR_limit);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_TR_limit);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_GDTR_limit);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_IDTR_limit);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_ES_access_rights);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_CS_access_rights);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_SS_access_rights);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_DS_access_rights);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_FS_access_rights);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_GS_access_rights);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_LDTR_access_rights);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_TR_access_rights);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_interruptibility);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_activity_state);
#ifndef __DEBUG_QEMU__
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_SMBASE);
#endif /* !__DEBUG_QEMU__ */
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_SYSENTER_CS);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.guest_ES_selector);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.guest_CS_selector);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.guest_SS_selector);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.guest_DS_selector);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.guest_FS_selector);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.guest_GS_selector);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.guest_LDTR_selector);
    DUMP_VCPU_PRINT_INT16(vcpu->vmcs.guest_TR_selector);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_VMCS_link_pointer);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_IA32_DEBUGCTL);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_paddr);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_PDPTE0);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_PDPTE1);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_PDPTE2);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_PDPTE3);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.info_vminstr_error);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.info_vmexit_reason);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.info_vmexit_interrupt_information);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.info_vmexit_interrupt_error_code);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.info_IDT_vectoring_information);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.info_IDT_vectoring_error_code);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.info_vmexit_instruction_length);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.info_vmx_instruction_information);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.info_exit_qualification);
#ifndef __DEBUG_QEMU__
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.info_IO_RCX);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.info_IO_RSI);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.info_IO_RDI);
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.info_IO_RIP);
#endif /* !__DEBUG_QEMU__ */
    DUMP_VCPU_PRINT_INTNW(vcpu->vmcs.info_guest_linear_address);
#ifdef __NESTED_VIRTUALIZATION__
    DUMP_VCPU_PRINT_INT32(vcpu->vmx_nested_is_vmx_operation);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_nested_vmxon_pointer);
    DUMP_VCPU_PRINT_INT32(vcpu->vmx_nested_is_vmx_root_operation);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_nested_current_vmcs_pointer);
    for (i = 0; i < IA32_VMX_MSRCOUNT; i++) {
        DUMP_VCPU_PRINT_INT64_INDEX(vcpu->vmx_nested_msrs, i);
    }
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_nested_pinbased_ctls);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_nested_procbased_ctls);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_nested_exit_ctls);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_nested_entry_ctls);

#endif /* !__NESTED_VIRTUALIZATION__ */

#undef DUMP_VCPU_PRINT_INT16
#undef DUMP_VCPU_PRINT_INT32
#undef DUMP_VCPU_PRINT_INT64
#undef DUMP_VCPU_PRINT_INT64_INDEX
#undef DUMP_VCPU_PRINT_INTNW

}
