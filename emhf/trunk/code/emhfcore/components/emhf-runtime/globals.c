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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

//globals.c
//author: amit vasudevan (amitvasudevan@acm.org)
//global declarations and definitions for the runtime

#include <emhf.h> 


#if defined (__TEST_CPU_QUIESCE__)
	//queisce test global variables
	//quiesce cpu counter and corresponding lock
	u32 g_quiesce_cpu_counter __attribute__(( section(".data") )) =0;
	u32 g_lock_quiesce_cpu_counter __attribute__(( section(".data") )) =1;
#endif


//variable that is used to de-link the INT 15 handler, if 1 then signifies that
//we have processed E820 requests and its safe to de-link
//parteventhub
//u32 g_svm_ine820handler __attribute__(( section(".data") )) = 0;


//SVM VM_HSAVE buffers 
//baseplatform x86svm
u8 g_svm_hsave_buffers[2 * PAGE_SIZE_4K * MAX_VCPU_ENTRIES]__attribute__(( section(".palign_data") ));

//SVM VMCB buffers
//baseplatform x86svm
u8 g_svm_vmcb_buffers[2 * PAGE_SIZE_4K * MAX_VCPU_ENTRIES]__attribute__(( section(".palign_data") )); 

//SVM IO bitmap buffer
//baseplatform x86svm
u8 g_svm_iopm[SIZEOF_IOPM_BITMAP]__attribute__(( section(".palign_data") )); 

//SVM MSR bitmap buffer
//baseplatform x86svm
u8 g_svm_msrpm[SIZEOF_MSRPM_BITMAP]__attribute__(( section(".palign_data") ));

//VMX VMCS read-only field encodings
//baseplatform x86vmx
struct _vmx_vmcsrofields_encodings g_vmx_vmcsrofields_encodings[] __attribute__(( section(".data") )) = {
	{ 0x4400, offsetof(struct _vmx_vmcsfields, info_vminstr_error) }, 
	{ 0x4402, offsetof(struct _vmx_vmcsfields, info_vmexit_reason) },
	{ 0x4404, offsetof(struct _vmx_vmcsfields, info_vmexit_interrupt_information) },
	{ 0x4406, offsetof(struct _vmx_vmcsfields, info_vmexit_interrupt_error_code) },
	{ 0x4408, offsetof(struct _vmx_vmcsfields, info_IDT_vectoring_information) },
	{ 0x440A, offsetof(struct _vmx_vmcsfields, info_IDT_vectoring_error_code) },
	{ 0x440C, offsetof(struct _vmx_vmcsfields, info_vmexit_instruction_length) },
	{ 0x440E, offsetof(struct _vmx_vmcsfields, info_vmx_instruction_information) },
	{ 0x6400, offsetof(struct _vmx_vmcsfields, info_exit_qualification) },
	{ 0x6402, offsetof(struct _vmx_vmcsfields, info_IO_RCX) },
	{ 0x6404, offsetof(struct _vmx_vmcsfields, info_IO_RSI) },
	{ 0x6406, offsetof(struct _vmx_vmcsfields, info_IO_RDI) },
	{ 0x6408, offsetof(struct _vmx_vmcsfields, info_IO_RIP) },
#if defined(__NESTED_PAGING__)
	{ 0x2400, offsetof(struct _vmx_vmcsfields, guest_paddr_full) },
	{ 0x2401, offsetof(struct _vmx_vmcsfields, guest_paddr_high) },
#endif
	{ 0x640A, offsetof(struct _vmx_vmcsfields, info_guest_linear_address) } 
};

//count of VMX VMCS read-only fields
//baseplatform x86vmx
unsigned int g_vmx_vmcsrofields_encodings_count __attribute__(( section(".data") )) = sizeof( g_vmx_vmcsrofields_encodings ) / sizeof( struct _vmx_vmcsrofields_encodings );

//VMX VMCS read-write field encodings
//baseplatform x86vmx
struct _vmx_vmcsrwfields_encodings g_vmx_vmcsrwfields_encodings[] __attribute__(( section(".data") )) = {
	// Control fields
	#if defined(__NESTED_PAGING__)
  //16-bit control field
  { 0x0000, offsetof(struct _vmx_vmcsfields, control_vpid) },
	#endif
	// Natural 32-bit Control fields
	{ 0x4000, offsetof(struct _vmx_vmcsfields, control_VMX_pin_based) },
	{ 0x4002, offsetof(struct _vmx_vmcsfields, control_VMX_cpu_based) },
	{ 0x401E, offsetof(struct _vmx_vmcsfields, control_VMX_seccpu_based) },
	{ 0x4004, offsetof(struct _vmx_vmcsfields, control_exception_bitmap) },
	{ 0x4006, offsetof(struct _vmx_vmcsfields, control_pagefault_errorcode_mask) },
	{ 0x4008, offsetof(struct _vmx_vmcsfields, control_pagefault_errorcode_match) },
	{ 0x400A, offsetof(struct _vmx_vmcsfields, control_CR3_target_count) },
	{ 0x400C, offsetof(struct _vmx_vmcsfields, control_VM_exit_controls) },
	{ 0x400E, offsetof(struct _vmx_vmcsfields, control_VM_exit_MSR_store_count) },
	{ 0x4010, offsetof(struct _vmx_vmcsfields, control_VM_exit_MSR_load_count) },
	{ 0x4012, offsetof(struct _vmx_vmcsfields, control_VM_entry_controls) },
	{ 0x4014, offsetof(struct _vmx_vmcsfields, control_VM_entry_MSR_load_count) },
	{ 0x4016, offsetof(struct _vmx_vmcsfields, control_VM_entry_interruption_information) },
	{ 0x4018, offsetof(struct _vmx_vmcsfields, control_VM_entry_exception_errorcode) },
	{ 0x401A, offsetof(struct _vmx_vmcsfields, control_VM_entry_instruction_length) },
	{ 0x401C, offsetof(struct _vmx_vmcsfields, control_Task_PRivilege_Threshold) },
	// Natural 64-bit Control fields
	{ 0x6000, offsetof(struct _vmx_vmcsfields, control_CR0_mask) },
	{ 0x6002, offsetof(struct _vmx_vmcsfields, control_CR4_mask) }, 
	{ 0x6004, offsetof(struct _vmx_vmcsfields, control_CR0_shadow) },
	{ 0x6006, offsetof(struct _vmx_vmcsfields, control_CR4_shadow) },
	{ 0x6008, offsetof(struct _vmx_vmcsfields, control_CR3_target0) },
	{ 0x600A, offsetof(struct _vmx_vmcsfields, control_CR3_target1) },
	{ 0x600C, offsetof(struct _vmx_vmcsfields, control_CR3_target2) },
	{ 0x600E, offsetof(struct _vmx_vmcsfields, control_CR3_target3) },
	// Full 64-bit Control fields
	{ 0x2000, offsetof(struct _vmx_vmcsfields, control_IO_BitmapA_address_full) },
	{ 0x2001, offsetof(struct _vmx_vmcsfields, control_IO_BitmapA_address_high) },
	{ 0x2002, offsetof(struct _vmx_vmcsfields, control_IO_BitmapB_address_full) },
	{ 0x2003, offsetof(struct _vmx_vmcsfields, control_IO_BitmapB_address_high) },
	{ 0x2004, offsetof(struct _vmx_vmcsfields, control_MSR_Bitmaps_address_full) },
	{ 0x2005, offsetof(struct _vmx_vmcsfields, control_MSR_Bitmaps_address_high) }, 
	{ 0x2006, offsetof(struct _vmx_vmcsfields, control_VM_exit_MSR_store_address_full) },
	{ 0x2007, offsetof(struct _vmx_vmcsfields, control_VM_exit_MSR_store_address_high) },
	{ 0x2008, offsetof(struct _vmx_vmcsfields, control_VM_exit_MSR_load_address_full) },
	{ 0x2009, offsetof(struct _vmx_vmcsfields, control_VM_exit_MSR_load_address_high) },
	{ 0x200A, offsetof(struct _vmx_vmcsfields, control_VM_entry_MSR_load_address_full) },
	{ 0x200B, offsetof(struct _vmx_vmcsfields, control_VM_entry_MSR_load_address_high) },
	{ 0x200C, offsetof(struct _vmx_vmcsfields, control_Executive_VMCS_pointer_full) },
	{ 0x200D, offsetof(struct _vmx_vmcsfields, control_Executive_VMCS_pointer_high) },
	{ 0x2010, offsetof(struct _vmx_vmcsfields, control_TSC_offset_full) },
	{ 0x2011, offsetof(struct _vmx_vmcsfields, control_TSC_offset_high) },
	//{ 0x2012, offsetof(struct _vmx_vmcsfields, control_virtual_APIC_page_address_full) }, 
	//{ 0x2013, offsetof(struct _vmx_vmcsfields, control_virtual_APIC_page_address_high) },
	#if defined(__NESTED_PAGING__)
	{ 0x201A, offsetof(struct _vmx_vmcsfields, control_EPT_pointer_full) },
	{ 0x201B, offsetof(struct _vmx_vmcsfields, control_EPT_pointer_high) },
	#endif
	// Host-State fields
	// Natural 64-bit Host-State fields
	{ 0x6C00, offsetof(struct _vmx_vmcsfields, host_CR0) },
	{ 0x6C02, offsetof(struct _vmx_vmcsfields, host_CR3) },
	{ 0x6C04, offsetof(struct _vmx_vmcsfields, host_CR4) },
	{ 0x6C06, offsetof(struct _vmx_vmcsfields, host_FS_base) },
	{ 0x6C08, offsetof(struct _vmx_vmcsfields, host_GS_base) },
	{ 0x6C0A, offsetof(struct _vmx_vmcsfields, host_TR_base) },
	{ 0x6C0C, offsetof(struct _vmx_vmcsfields, host_GDTR_base) },
	{ 0x6C0E, offsetof(struct _vmx_vmcsfields, host_IDTR_base) },
	{ 0x6C10, offsetof(struct _vmx_vmcsfields, host_SYSENTER_ESP) },
	{ 0x6C12, offsetof(struct _vmx_vmcsfields, host_SYSENTER_EIP) },
	{ 0x6C14, offsetof(struct _vmx_vmcsfields, host_RSP) },
	{ 0x6C16, offsetof(struct _vmx_vmcsfields, host_RIP) },
	// Natural 32-bit Host-State fields
	{ 0x4C00, offsetof(struct _vmx_vmcsfields, host_SYSENTER_CS) },
	// Natural 16-bit Host-State fields
	{ 0x0C00, offsetof(struct _vmx_vmcsfields, host_ES_selector) },
	{ 0x0C02, offsetof(struct _vmx_vmcsfields, host_CS_selector) },
	{ 0x0C04, offsetof(struct _vmx_vmcsfields, host_SS_selector) },
	{ 0x0C06, offsetof(struct _vmx_vmcsfields, host_DS_selector) },
	{ 0x0C08, offsetof(struct _vmx_vmcsfields, host_FS_selector) },
	{ 0x0C0A, offsetof(struct _vmx_vmcsfields, host_GS_selector) },
	{ 0x0C0C, offsetof(struct _vmx_vmcsfields, host_TR_selector) },
	// Guest-State fields
	// Natural 64-bit Guest-State fields
	{ 0x6800, offsetof(struct _vmx_vmcsfields, guest_CR0) },
	{ 0x6802, offsetof(struct _vmx_vmcsfields, guest_CR3) },
	{ 0x6804, offsetof(struct _vmx_vmcsfields, guest_CR4) },
	{ 0x6806, offsetof(struct _vmx_vmcsfields, guest_ES_base) },
	{ 0x6808, offsetof(struct _vmx_vmcsfields, guest_CS_base) },
	{ 0x680A, offsetof(struct _vmx_vmcsfields, guest_SS_base) },
	{ 0x680C, offsetof(struct _vmx_vmcsfields, guest_DS_base) },
	{ 0x680E, offsetof(struct _vmx_vmcsfields, guest_FS_base) },
	{ 0x6810, offsetof(struct _vmx_vmcsfields, guest_GS_base) },
	{ 0x6812, offsetof(struct _vmx_vmcsfields, guest_LDTR_base) },
	{ 0x6814, offsetof(struct _vmx_vmcsfields, guest_TR_base) },
	{ 0x6816, offsetof(struct _vmx_vmcsfields, guest_GDTR_base) },
	{ 0x6818, offsetof(struct _vmx_vmcsfields, guest_IDTR_base) },
	{ 0x681A, offsetof(struct _vmx_vmcsfields, guest_DR7) },
	{ 0x681C, offsetof(struct _vmx_vmcsfields, guest_RSP) },
	{ 0x681E, offsetof(struct _vmx_vmcsfields, guest_RIP) },
	{ 0x6820, offsetof(struct _vmx_vmcsfields, guest_RFLAGS) },
	{ 0x6822, offsetof(struct _vmx_vmcsfields, guest_pending_debug_x) },
	{ 0x6824, offsetof(struct _vmx_vmcsfields, guest_SYSENTER_ESP) },
	{ 0x6826, offsetof(struct _vmx_vmcsfields, guest_SYSENTER_EIP) },
	#if defined(__NESTED_PAGING__)
	{ 0x280A, offsetof(struct _vmx_vmcsfields, guest_PDPTE0_full) },
	{ 0x280B, offsetof(struct _vmx_vmcsfields, guest_PDPTE0_high) },
	{ 0x280C, offsetof(struct _vmx_vmcsfields, guest_PDPTE1_full) },
	{ 0x280D, offsetof(struct _vmx_vmcsfields, guest_PDPTE1_high) },
	{ 0x280E, offsetof(struct _vmx_vmcsfields, guest_PDPTE2_full) },
	{ 0x280F, offsetof(struct _vmx_vmcsfields, guest_PDPTE2_high) },
	{ 0x2810, offsetof(struct _vmx_vmcsfields, guest_PDPTE3_full) },
	{ 0x2811, offsetof(struct _vmx_vmcsfields, guest_PDPTE3_high) },
	#endif
	// Natural 32-bit Guest-State fields
	{ 0x4800, offsetof(struct _vmx_vmcsfields, guest_ES_limit) },
	{ 0x4802, offsetof(struct _vmx_vmcsfields, guest_CS_limit) },
	{ 0x4804, offsetof(struct _vmx_vmcsfields, guest_SS_limit) },
	{ 0x4806, offsetof(struct _vmx_vmcsfields, guest_DS_limit) },
	{ 0x4808, offsetof(struct _vmx_vmcsfields, guest_FS_limit) },
	{ 0x480A, offsetof(struct _vmx_vmcsfields, guest_GS_limit) },
	{ 0x480C, offsetof(struct _vmx_vmcsfields, guest_LDTR_limit) },
	{ 0x480E, offsetof(struct _vmx_vmcsfields, guest_TR_limit) },
	{ 0x4810, offsetof(struct _vmx_vmcsfields, guest_GDTR_limit) },
	{ 0x4812, offsetof(struct _vmx_vmcsfields, guest_IDTR_limit) },
	{ 0x4814, offsetof(struct _vmx_vmcsfields, guest_ES_access_rights) },
	{ 0x4816, offsetof(struct _vmx_vmcsfields, guest_CS_access_rights) },
	{ 0x4818, offsetof(struct _vmx_vmcsfields, guest_SS_access_rights) },
	{ 0x481A, offsetof(struct _vmx_vmcsfields, guest_DS_access_rights) },
	{ 0x481C, offsetof(struct _vmx_vmcsfields, guest_FS_access_rights) },
	{ 0x481E, offsetof(struct _vmx_vmcsfields, guest_GS_access_rights) },
	{ 0x4820, offsetof(struct _vmx_vmcsfields, guest_LDTR_access_rights) },
	{ 0x4822, offsetof(struct _vmx_vmcsfields, guest_TR_access_rights) },
	{ 0x4824, offsetof(struct _vmx_vmcsfields, guest_interruptibility) },
	{ 0x4826, offsetof(struct _vmx_vmcsfields, guest_activity_state) },
	{ 0x4828, offsetof(struct _vmx_vmcsfields, guest_SMBASE) },
	{ 0x482A, offsetof(struct _vmx_vmcsfields, guest_SYSENTER_CS) },
	// Natural 16-bit Guest-State fields
	{ 0x0800, offsetof(struct _vmx_vmcsfields, guest_ES_selector) },
	{ 0x0802, offsetof(struct _vmx_vmcsfields, guest_CS_selector) },
	{ 0x0804, offsetof(struct _vmx_vmcsfields, guest_SS_selector) },
	{ 0x0806, offsetof(struct _vmx_vmcsfields, guest_DS_selector) },
	{ 0x0808, offsetof(struct _vmx_vmcsfields, guest_FS_selector) },
	{ 0x080A, offsetof(struct _vmx_vmcsfields, guest_GS_selector) },
	{ 0x080C, offsetof(struct _vmx_vmcsfields, guest_LDTR_selector) },
	{ 0x080E, offsetof(struct _vmx_vmcsfields, guest_TR_selector) },
	// Full 64-bit Guest-State fields
	{ 0x2800, offsetof(struct _vmx_vmcsfields, guest_VMCS_link_pointer_full) },
	{ 0x2801, offsetof(struct _vmx_vmcsfields, guest_VMCS_link_pointer_high) },
	{ 0x2802, offsetof(struct _vmx_vmcsfields, guest_IA32_DEBUGCTL_full) },
	{ 0x2803, offsetof(struct _vmx_vmcsfields, guest_IA32_DEBUGCTL_high) } 
};

//count of VMX VMCS read-write fields
//baseplatform x86vmx
unsigned int g_vmx_vmcsrwfields_encodings_count __attribute__(( section(".data") )) = sizeof( g_vmx_vmcsrwfields_encodings ) / sizeof( struct _vmx_vmcsrwfields_encodings );

//VMX VMXON buffers
//baseplatform x86vmx
u8 g_vmx_vmxon_buffers[PAGE_SIZE_4K * MAX_VCPU_ENTRIES] __attribute__(( section(".palign_data") ));

//VMX VMCS buffers
//baseplatform x86vmx
u8 g_vmx_vmcs_buffers[PAGE_SIZE_4K * MAX_VCPU_ENTRIES] __attribute__(( section(".palign_data") ));
		
//VMX IO bitmap buffers
//baseplatform x86vmx
u8 g_vmx_iobitmap_buffers[2 * PAGE_SIZE_4K * MAX_VCPU_ENTRIES] __attribute__(( section(".palign_data") ));
		
//VMX guest and host MSR save area buffers
//baseplatform x86vmx
u8 g_vmx_msr_area_host_buffers[2 * PAGE_SIZE_4K * MAX_VCPU_ENTRIES] __attribute__(( section(".palign_data") ));
u8 g_vmx_msr_area_guest_buffers[2 * PAGE_SIZE_4K * MAX_VCPU_ENTRIES] __attribute__(( section(".palign_data") ));

//VMX MSR bitmap buffers
//baseplatform x86vmx
u8 g_vmx_msrbitmap_buffers[PAGE_SIZE_4K * MAX_VCPU_ENTRIES] __attribute__(( section(".palign_data") ));

