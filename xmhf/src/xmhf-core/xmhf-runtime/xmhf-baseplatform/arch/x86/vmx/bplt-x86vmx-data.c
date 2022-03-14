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
 * EMHF base platform component interface, x86 vmx backend data
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>

#define DECLARE_FIELD(encoding, member) \
    {                                                           \
        encoding,                                               \
        offsetof(struct _vmx_vmcsfields, member),               \
        sizeof((struct _vmx_vmcsfields){}.member)               \
    },

//VMX VMCS read-only field encodings
struct _vmx_vmcsrofields_encodings g_vmx_vmcsrofields_encodings[] __attribute__(( section(".data") )) = {
    DECLARE_FIELD(0x4400, info_vminstr_error) 
    DECLARE_FIELD(0x4402, info_vmexit_reason)
    DECLARE_FIELD(0x4404, info_vmexit_interrupt_information)
    DECLARE_FIELD(0x4406, info_vmexit_interrupt_error_code)
    DECLARE_FIELD(0x4408, info_IDT_vectoring_information)
    DECLARE_FIELD(0x440A, info_IDT_vectoring_error_code)
    DECLARE_FIELD(0x440C, info_vmexit_instruction_length)
    DECLARE_FIELD(0x440E, info_vmx_instruction_information)
    DECLARE_FIELD(0x6400, info_exit_qualification)
#ifndef __DEBUG_QEMU__
    DECLARE_FIELD(0x6402, info_IO_RCX)
    DECLARE_FIELD(0x6404, info_IO_RSI)
    DECLARE_FIELD(0x6406, info_IO_RDI)
    DECLARE_FIELD(0x6408, info_IO_RIP)
#endif /* !__DEBUG_QEMU__ */
#if defined(__NESTED_PAGING__)
    DECLARE_FIELD(0x2400, guest_paddr_full)
    DECLARE_FIELD(0x2401, guest_paddr_high)
#endif
    DECLARE_FIELD(0x640A, info_guest_linear_address)
};

//count of VMX VMCS read-only fields
unsigned int g_vmx_vmcsrofields_encodings_count __attribute__(( section(".data") )) = sizeof( g_vmx_vmcsrofields_encodings ) / sizeof( struct _vmx_vmcsrofields_encodings );

//VMX VMCS read-write field encodings
struct _vmx_vmcsrwfields_encodings g_vmx_vmcsrwfields_encodings[] __attribute__(( section(".data") )) = {
    // Control fields
    #if defined(__NESTED_PAGING__)
    //16-bit control field
    DECLARE_FIELD(0x0000, control_vpid)
    #endif
    // Natural 32-bit Control fields
    DECLARE_FIELD(0x4000, control_VMX_pin_based)
    DECLARE_FIELD(0x4002, control_VMX_cpu_based)
    DECLARE_FIELD(0x401E, control_VMX_seccpu_based)
    DECLARE_FIELD(0x4004, control_exception_bitmap)
    DECLARE_FIELD(0x4006, control_pagefault_errorcode_mask)
    DECLARE_FIELD(0x4008, control_pagefault_errorcode_match)
    DECLARE_FIELD(0x400A, control_CR3_target_count)
    DECLARE_FIELD(0x400C, control_VM_exit_controls)
    DECLARE_FIELD(0x400E, control_VM_exit_MSR_store_count)
    DECLARE_FIELD(0x4010, control_VM_exit_MSR_load_count)
    DECLARE_FIELD(0x4012, control_VM_entry_controls)
    DECLARE_FIELD(0x4014, control_VM_entry_MSR_load_count)
    DECLARE_FIELD(0x4016, control_VM_entry_interruption_information)
    DECLARE_FIELD(0x4018, control_VM_entry_exception_errorcode)
    DECLARE_FIELD(0x401A, control_VM_entry_instruction_length)
    DECLARE_FIELD(0x401C, control_Task_PRivilege_Threshold)
    // Natural 64-bit Control fields
    DECLARE_FIELD(0x6000, control_CR0_mask)
    DECLARE_FIELD(0x6002, control_CR4_mask) 
    DECLARE_FIELD(0x6004, control_CR0_shadow)
    DECLARE_FIELD(0x6006, control_CR4_shadow)
#ifndef __DEBUG_QEMU__
    DECLARE_FIELD(0x6008, control_CR3_target0)
    DECLARE_FIELD(0x600A, control_CR3_target1)
    DECLARE_FIELD(0x600C, control_CR3_target2)
    DECLARE_FIELD(0x600E, control_CR3_target3)
#endif /* !__DEBUG_QEMU__ */
    // Full 64-bit Control fields
    DECLARE_FIELD(0x2000, control_IO_BitmapA_address_full)
    DECLARE_FIELD(0x2001, control_IO_BitmapA_address_high)
    DECLARE_FIELD(0x2002, control_IO_BitmapB_address_full)
    DECLARE_FIELD(0x2003, control_IO_BitmapB_address_high)
    DECLARE_FIELD(0x2004, control_MSR_Bitmaps_address_full)
    DECLARE_FIELD(0x2005, control_MSR_Bitmaps_address_high) 
    DECLARE_FIELD(0x2006, control_VM_exit_MSR_store_address_full)
    DECLARE_FIELD(0x2007, control_VM_exit_MSR_store_address_high)
    DECLARE_FIELD(0x2008, control_VM_exit_MSR_load_address_full)
    DECLARE_FIELD(0x2009, control_VM_exit_MSR_load_address_high)
    DECLARE_FIELD(0x200A, control_VM_entry_MSR_load_address_full)
    DECLARE_FIELD(0x200B, control_VM_entry_MSR_load_address_high)
#ifndef __DEBUG_QEMU__
    DECLARE_FIELD(0x200C, control_Executive_VMCS_pointer_full)
    DECLARE_FIELD(0x200D, control_Executive_VMCS_pointer_high)
#endif /* !__DEBUG_QEMU__ */
    DECLARE_FIELD(0x2010, control_TSC_offset_full)
    DECLARE_FIELD(0x2011, control_TSC_offset_high)
    //DECLARE_FIELD(0x2012, control_virtual_APIC_page_address_full)
    //DECLARE_FIELD(0x2013, control_virtual_APIC_page_address_high)
    #if defined(__NESTED_PAGING__)
    DECLARE_FIELD(0x201A, control_EPT_pointer_full)
    DECLARE_FIELD(0x201B, control_EPT_pointer_high)
    #endif
    // Host-State fields
    // Natural 64-bit Host-State fields
    DECLARE_FIELD(0x6C00, host_CR0)
    DECLARE_FIELD(0x6C02, host_CR3)
    DECLARE_FIELD(0x6C04, host_CR4)
    DECLARE_FIELD(0x6C06, host_FS_base)
    DECLARE_FIELD(0x6C08, host_GS_base)
    DECLARE_FIELD(0x6C0A, host_TR_base)
    DECLARE_FIELD(0x6C0C, host_GDTR_base)
    DECLARE_FIELD(0x6C0E, host_IDTR_base)
    DECLARE_FIELD(0x6C10, host_SYSENTER_ESP)
    DECLARE_FIELD(0x6C12, host_SYSENTER_EIP)
    DECLARE_FIELD(0x6C14, host_RSP)
    DECLARE_FIELD(0x6C16, host_RIP)
    // Natural 32-bit Host-State fields
    DECLARE_FIELD(0x4C00, host_SYSENTER_CS)
    // Natural 16-bit Host-State fields
    DECLARE_FIELD(0x0C00, host_ES_selector)
    DECLARE_FIELD(0x0C02, host_CS_selector)
    DECLARE_FIELD(0x0C04, host_SS_selector)
    DECLARE_FIELD(0x0C06, host_DS_selector)
    DECLARE_FIELD(0x0C08, host_FS_selector)
    DECLARE_FIELD(0x0C0A, host_GS_selector)
    DECLARE_FIELD(0x0C0C, host_TR_selector)
    // Guest-State fields
    // Natural 64-bit Guest-State fields
    DECLARE_FIELD(0x6800, guest_CR0)
    DECLARE_FIELD(0x6802, guest_CR3)
    DECLARE_FIELD(0x6804, guest_CR4)
    DECLARE_FIELD(0x6806, guest_ES_base)
    DECLARE_FIELD(0x6808, guest_CS_base)
    DECLARE_FIELD(0x680A, guest_SS_base)
    DECLARE_FIELD(0x680C, guest_DS_base)
    DECLARE_FIELD(0x680E, guest_FS_base)
    DECLARE_FIELD(0x6810, guest_GS_base)
    DECLARE_FIELD(0x6812, guest_LDTR_base)
    DECLARE_FIELD(0x6814, guest_TR_base)
    DECLARE_FIELD(0x6816, guest_GDTR_base)
    DECLARE_FIELD(0x6818, guest_IDTR_base)
    DECLARE_FIELD(0x681A, guest_DR7)
    DECLARE_FIELD(0x681C, guest_RSP)
    DECLARE_FIELD(0x681E, guest_RIP)
    DECLARE_FIELD(0x6820, guest_RFLAGS)
    DECLARE_FIELD(0x6822, guest_pending_debug_x)
    DECLARE_FIELD(0x6824, guest_SYSENTER_ESP)
    DECLARE_FIELD(0x6826, guest_SYSENTER_EIP)
    #if defined(__NESTED_PAGING__)
    DECLARE_FIELD(0x280A, guest_PDPTE0_full)
    DECLARE_FIELD(0x280B, guest_PDPTE0_high)
    DECLARE_FIELD(0x280C, guest_PDPTE1_full)
    DECLARE_FIELD(0x280D, guest_PDPTE1_high)
    DECLARE_FIELD(0x280E, guest_PDPTE2_full)
    DECLARE_FIELD(0x280F, guest_PDPTE2_high)
    DECLARE_FIELD(0x2810, guest_PDPTE3_full)
    DECLARE_FIELD(0x2811, guest_PDPTE3_high)
    #endif
    // Natural 32-bit Guest-State fields
    DECLARE_FIELD(0x4800, guest_ES_limit)
    DECLARE_FIELD(0x4802, guest_CS_limit)
    DECLARE_FIELD(0x4804, guest_SS_limit)
    DECLARE_FIELD(0x4806, guest_DS_limit)
    DECLARE_FIELD(0x4808, guest_FS_limit)
    DECLARE_FIELD(0x480A, guest_GS_limit)
    DECLARE_FIELD(0x480C, guest_LDTR_limit)
    DECLARE_FIELD(0x480E, guest_TR_limit)
    DECLARE_FIELD(0x4810, guest_GDTR_limit)
    DECLARE_FIELD(0x4812, guest_IDTR_limit)
    DECLARE_FIELD(0x4814, guest_ES_access_rights)
    DECLARE_FIELD(0x4816, guest_CS_access_rights)
    DECLARE_FIELD(0x4818, guest_SS_access_rights)
    DECLARE_FIELD(0x481A, guest_DS_access_rights)
    DECLARE_FIELD(0x481C, guest_FS_access_rights)
    DECLARE_FIELD(0x481E, guest_GS_access_rights)
    DECLARE_FIELD(0x4820, guest_LDTR_access_rights)
    DECLARE_FIELD(0x4822, guest_TR_access_rights)
    DECLARE_FIELD(0x4824, guest_interruptibility)
    DECLARE_FIELD(0x4826, guest_activity_state)
#ifndef __DEBUG_QEMU__
    DECLARE_FIELD(0x4828, guest_SMBASE)
#endif /* !__DEBUG_QEMU__ */
    DECLARE_FIELD(0x482A, guest_SYSENTER_CS)
    // Natural 16-bit Guest-State fields
    DECLARE_FIELD(0x0800, guest_ES_selector)
    DECLARE_FIELD(0x0802, guest_CS_selector)
    DECLARE_FIELD(0x0804, guest_SS_selector)
    DECLARE_FIELD(0x0806, guest_DS_selector)
    DECLARE_FIELD(0x0808, guest_FS_selector)
    DECLARE_FIELD(0x080A, guest_GS_selector)
    DECLARE_FIELD(0x080C, guest_LDTR_selector)
    DECLARE_FIELD(0x080E, guest_TR_selector)
    // Full 64-bit Guest-State fields
    DECLARE_FIELD(0x2800, guest_VMCS_link_pointer_full)
    DECLARE_FIELD(0x2801, guest_VMCS_link_pointer_high)
    DECLARE_FIELD(0x2802, guest_IA32_DEBUGCTL_full)
    DECLARE_FIELD(0x2803, guest_IA32_DEBUGCTL_high)
};

//count of VMX VMCS read-write fields
unsigned int g_vmx_vmcsrwfields_encodings_count __attribute__(( section(".data") )) = sizeof( g_vmx_vmcsrwfields_encodings ) / sizeof( struct _vmx_vmcsrwfields_encodings );

//VMX VMXON buffers
u8 g_vmx_vmxon_buffers[PAGE_SIZE_4K * MAX_VCPU_ENTRIES] __attribute__(( section(".palign_data") ));

//VMX VMCS buffers
u8 g_vmx_vmcs_buffers[PAGE_SIZE_4K * MAX_VCPU_ENTRIES] __attribute__(( section(".palign_data") ));
		
//VMX IO bitmap buffer (one buffer for the entire platform)
u8 g_vmx_iobitmap_buffer[2 * PAGE_SIZE_4K] __attribute__(( section(".palign_data") ));
		
//VMX guest and host MSR save area buffers
u8 g_vmx_msr_area_host_buffers[2 * PAGE_SIZE_4K * MAX_VCPU_ENTRIES] __attribute__(( section(".palign_data") ));
u8 g_vmx_msr_area_guest_buffers[2 * PAGE_SIZE_4K * MAX_VCPU_ENTRIES] __attribute__(( section(".palign_data") ));

//VMX MSR bitmap buffers
u8 g_vmx_msrbitmap_buffers[PAGE_SIZE_4K * MAX_VCPU_ENTRIES] __attribute__(( section(".palign_data") ));
