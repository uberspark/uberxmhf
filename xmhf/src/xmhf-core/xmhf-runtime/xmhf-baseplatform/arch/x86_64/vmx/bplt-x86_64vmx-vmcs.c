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

//---putVMCS--------------------------------------------------------------------
// routine takes vcpu vmcsfields and stores it in the CPU VMCS 
void xmhf_baseplatform_arch_x86_64vmx_putVMCS(VCPU *vcpu){
    unsigned int i;
    for(i=0; i < g_vmx_vmcsrwfields_encodings_count; i++){
      unsigned long *field = (unsigned long *)((hva_t)&vcpu->vmcs + (u32)g_vmx_vmcsrwfields_encodings[i].fieldoffset);
      unsigned long fieldvalue = *field;
      //printf("\nvmwrite: enc=0x%08x, value=0x%08x", vmcsrwfields_encodings[i].encoding, fieldvalue);
      if(!__vmx_vmwrite(g_vmx_vmcsrwfields_encodings[i].encoding, fieldvalue)){
        printf("\nCPU(0x%02x): VMWRITE failed. HALT!", vcpu->id);
        HALT();
      }
    }
}

void xmhf_baseplatform_arch_x86_64vmx_read_field(u32 encoding, void *addr,
                                                 u32 size) {
    u64 value;
    HALT_ON_ERRORCOND(__vmx_vmread(encoding, &value));
    /* Read 64-bit fields using 1 VMREAD instruction (different from x86) */
    switch ((encoding >> 13) & 0x3) {
    case 0: /* 16-bit */
        /* fallthrough */
    case 2: /* 32-bit */
        HALT_ON_ERRORCOND(size == 4);
        *(u32 *)addr = (u32)value;
        break;
    case 1: /* 64-bit */
        /* Disallow high access */
        HALT_ON_ERRORCOND((encoding & 0x1) == 0x0);
        /* fallthrough */
    case 3: /* natural width */
        HALT_ON_ERRORCOND(size == 8);
        *(u64 *)addr = value;
        break;
    default:
        HALT();
    }
}

//---getVMCS--------------------------------------------------------------------
// routine takes CPU VMCS and stores it in vcpu vmcsfields  
void xmhf_baseplatform_arch_x86_64vmx_getVMCS(VCPU *vcpu){
    unsigned int i;
    for(i=0; i < g_vmx_vmcsrwfields_encodings_count; i++){
        u32 encoding = g_vmx_vmcsrwfields_encodings[i].encoding;
        u32 offset = g_vmx_vmcsrwfields_encodings[i].fieldoffset;
        void *field = (void *)((hva_t)&vcpu->vmcs + offset);
        u32 size = g_vmx_vmcsrwfields_encodings[i].membersize;
        xmhf_baseplatform_arch_x86_64vmx_read_field(encoding, field, size);
    }
    for(i=0; i < g_vmx_vmcsrofields_encodings_count; i++){
        u32 encoding = g_vmx_vmcsrofields_encodings[i].encoding;
        u32 offset = g_vmx_vmcsrofields_encodings[i].fieldoffset;
        void *field = (void *)((hva_t)&vcpu->vmcs + offset);
        u32 size = g_vmx_vmcsrofields_encodings[i].membersize;
        xmhf_baseplatform_arch_x86_64vmx_read_field(encoding, field, size);
    }
}

//--debug: dumpVMCS dumps VMCS contents-----------------------------------------
void xmhf_baseplatform_arch_x86_64vmx_dumpVMCS(VCPU *vcpu){
  		printf("\nGuest State follows:");
		printf("\nguest_CS_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_CS_selector);
		printf("\nguest_DS_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_DS_selector);
		printf("\nguest_ES_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_ES_selector);
		printf("\nguest_FS_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_FS_selector);
		printf("\nguest_GS_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_GS_selector);
		printf("\nguest_SS_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_SS_selector);
		printf("\nguest_TR_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_TR_selector);
		printf("\nguest_LDTR_selector=0x%04x", (unsigned short)vcpu->vmcs.guest_LDTR_selector);
		printf("\nguest_CS_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_CS_access_rights);
		printf("\nguest_DS_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_DS_access_rights);
		printf("\nguest_ES_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_ES_access_rights);
		printf("\nguest_FS_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_FS_access_rights);
		printf("\nguest_GS_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_GS_access_rights);
		printf("\nguest_SS_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_SS_access_rights);
		printf("\nguest_TR_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_TR_access_rights);
		printf("\nguest_LDTR_access_rights=0x%08lx", 
			(unsigned long)vcpu->vmcs.guest_LDTR_access_rights);

		printf("\nguest_CS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)vcpu->vmcs.guest_CS_base, (unsigned short)vcpu->vmcs.guest_CS_limit);
		printf("\nguest_DS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)vcpu->vmcs.guest_DS_base, (unsigned short)vcpu->vmcs.guest_DS_limit);
		printf("\nguest_ES_base/limit=0x%08lx/0x%04x", 
			(unsigned long)vcpu->vmcs.guest_ES_base, (unsigned short)vcpu->vmcs.guest_ES_limit);
		printf("\nguest_FS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)vcpu->vmcs.guest_FS_base, (unsigned short)vcpu->vmcs.guest_FS_limit);
		printf("\nguest_GS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)vcpu->vmcs.guest_GS_base, (unsigned short)vcpu->vmcs.guest_GS_limit);
		printf("\nguest_SS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)vcpu->vmcs.guest_SS_base, (unsigned short)vcpu->vmcs.guest_SS_limit);
		printf("\nguest_GDTR_base/limit=0x%08lx/0x%04x",
			(unsigned long)vcpu->vmcs.guest_GDTR_base, (unsigned short)vcpu->vmcs.guest_GDTR_limit);		
		printf("\nguest_IDTR_base/limit=0x%08lx/0x%04x",
			(unsigned long)vcpu->vmcs.guest_IDTR_base, (unsigned short)vcpu->vmcs.guest_IDTR_limit);		
		printf("\nguest_TR_base/limit=0x%08lx/0x%04x",
			(unsigned long)vcpu->vmcs.guest_TR_base, (unsigned short)vcpu->vmcs.guest_TR_limit);		
		printf("\nguest_LDTR_base/limit=0x%08lx/0x%04x",
			(unsigned long)vcpu->vmcs.guest_LDTR_base, (unsigned short)vcpu->vmcs.guest_LDTR_limit);		

		printf("\nguest_CR0=0x%08lx, guest_CR4=0x%08lx, guest_CR3=0x%08lx",
			(unsigned long)vcpu->vmcs.guest_CR0, (unsigned long)vcpu->vmcs.guest_CR4,
			(unsigned long)vcpu->vmcs.guest_CR3);
		printf("\nguest_RSP=0x%08lx", (unsigned long)vcpu->vmcs.guest_RSP);
		printf("\nguest_RIP=0x%08lx", (unsigned long)vcpu->vmcs.guest_RIP);
		printf("\nguest_RFLAGS=0x%08lx", (unsigned long)vcpu->vmcs.guest_RFLAGS);
}

void xmhf_baseplatform_arch_x86_64vmx_dump_vcpu(VCPU *vcpu){

#define DUMP_VCPU_PRINT_INT16(x) \
    printf("\nCPU(0x%02x): " #x "=0x%08x", vcpu->id, (x));
#define DUMP_VCPU_PRINT_INT32(x) \
    printf("\nCPU(0x%02x): " #x "=0x%08x", vcpu->id, (x));
#define DUMP_VCPU_PRINT_INT64(x) \
    printf("\nCPU(0x%02x): " #x "=0x%016lx", vcpu->id, (x));
#define DUMP_VCPU_PRINT_INT64_INDEX(x, i) \
    printf("\nCPU(0x%02x): " #x "[%x]=0x%016lx", vcpu->id, (i), (x)[i]);

    DUMP_VCPU_PRINT_INT64(vcpu->rsp);
    DUMP_VCPU_PRINT_INT64(vcpu->sipi_page_vaddr);
    DUMP_VCPU_PRINT_INT32(vcpu->id);
    DUMP_VCPU_PRINT_INT32(vcpu->idx);
    DUMP_VCPU_PRINT_INT32(vcpu->sipivector);
    DUMP_VCPU_PRINT_INT32(vcpu->sipireceived);
    DUMP_VCPU_PRINT_INT32(vcpu->cpu_vendor);
    DUMP_VCPU_PRINT_INT32(vcpu->isbsp);
    DUMP_VCPU_PRINT_INT32(vcpu->quiesced);
    DUMP_VCPU_PRINT_INT64(vcpu->hsave_vaddr_ptr);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcb_vaddr_ptr);
    DUMP_VCPU_PRINT_INT64(vcpu->npt_vaddr_ptr);
    DUMP_VCPU_PRINT_INT64(vcpu->npt_vaddr_pdts);
    DUMP_VCPU_PRINT_INT64(vcpu->npt_asid);
    DUMP_VCPU_PRINT_INT64(vcpu->npt_vaddr_pts);
    DUMP_VCPU_PRINT_INT64(vcpu->svm_vaddr_iobitmap);
    for (u32 i = 0; i < IA32_VMX_MSRCOUNT; i++) {
        DUMP_VCPU_PRINT_INT64_INDEX(vcpu->vmx_msrs, i);
    }
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_msr_efer);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_msr_efcr);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_vmxonregion_vaddr);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_vmcs_vaddr);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_vaddr_iobitmap);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_vaddr_msr_area_host);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_vaddr_msr_area_guest);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_vaddr_msrbitmaps);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_vaddr_ept_pml4_table);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_vaddr_ept_pdp_table);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_vaddr_ept_pd_tables);
    DUMP_VCPU_PRINT_INT64(vcpu->vmx_vaddr_ept_p_tables);
    // Skip: vmx_ept_memorytypes
    // Skip: vmx_guestmtrrmsrs
    DUMP_VCPU_PRINT_INT32(vcpu->vmx_guest_currentstate);
    DUMP_VCPU_PRINT_INT32(vcpu->vmx_guest_nextstate);
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
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_CR0_mask);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_CR4_mask);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_CR0_shadow);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_CR4_shadow);
#ifndef __DEBUG_QEMU__
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_CR3_target0);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_CR3_target1);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_CR3_target2);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.control_CR3_target3);
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
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.host_CR0);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.host_CR3);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.host_CR4);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.host_FS_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.host_GS_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.host_TR_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.host_GDTR_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.host_IDTR_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.host_SYSENTER_ESP);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.host_SYSENTER_EIP);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.host_RSP);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.host_RIP);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.host_SYSENTER_CS);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.host_ES_selector);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.host_CS_selector);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.host_SS_selector);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.host_DS_selector);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.host_FS_selector);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.host_GS_selector);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.host_TR_selector);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_CR0);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_CR3);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_CR4);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_ES_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_CS_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_SS_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_DS_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_FS_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_GS_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_LDTR_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_TR_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_GDTR_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_IDTR_base);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_DR7);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_RSP);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_RIP);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_RFLAGS);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_pending_debug_x);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_SYSENTER_ESP);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.guest_SYSENTER_EIP);
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
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_ES_selector);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_CS_selector);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_SS_selector);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_DS_selector);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_FS_selector);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_GS_selector);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_LDTR_selector);
    DUMP_VCPU_PRINT_INT32(vcpu->vmcs.guest_TR_selector);
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
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.info_exit_qualification);
#ifndef __DEBUG_QEMU__
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.info_IO_RCX);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.info_IO_RSI);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.info_IO_RDI);
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.info_IO_RIP);
#endif /* !__DEBUG_QEMU__ */
    DUMP_VCPU_PRINT_INT64(vcpu->vmcs.info_guest_linear_address);

#undef DUMP_VCPU_PRINT_INT16
#undef DUMP_VCPU_PRINT_INT32
#undef DUMP_VCPU_PRINT_INT64
#undef DUMP_VCPU_PRINT_INT64_INDEX

}
