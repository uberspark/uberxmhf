#ifndef __MACHINE_H_
#define __MACHINE_H_

typedef struct	{
 int  encoding; void *setting; } __attribute__((packed)) VMCS_DEF;

#if defined(__CONF_HARDWARE_PAGING__)
extern unsigned short control_vpid;
#endif
// Natural 32-bit Control fields
extern unsigned int  control_VMX_pin_based;
extern unsigned int  control_VMX_cpu_based;
#if defined(__CONF_HARDWARE_PAGING__)
extern unsigned int control_VMX_seccpu_based;
#endif
extern unsigned int  control_exception_bitmap;
extern unsigned int  control_pagefault_errorcode_mask; 
extern unsigned int  control_pagefault_errorcode_match; 
extern unsigned int  control_CR3_target_count;
extern unsigned int  control_VM_exit_controls;
extern unsigned int  control_VM_exit_MSR_store_count;
extern unsigned int  control_VM_exit_MSR_load_count;
extern unsigned int  control_VM_entry_controls;
extern unsigned int  control_VM_entry_MSR_load_count;
extern unsigned int  control_VM_entry_interruption_information;
extern unsigned int  control_VM_entry_exception_errorcode;
extern unsigned int  control_VM_entry_instruction_length;
extern unsigned int  control_Task_PRivilege_Threshold;
// Natural 64-bit Control fields
extern unsigned long long  control_CR0_mask;
extern unsigned long long  control_CR4_mask;
extern unsigned long long  control_CR0_shadow;
extern unsigned long long  control_CR4_shadow;
extern unsigned long long  control_CR3_target0;
extern unsigned long long  control_CR3_target1;
extern unsigned long long  control_CR3_target2;
extern unsigned long long  control_CR3_target3;
// Full 64-bit Control fields
extern unsigned int  control_IO_BitmapA_address_full;
extern unsigned int  control_IO_BitmapA_address_high;
extern unsigned int  control_IO_BitmapB_address_full;
extern unsigned int  control_IO_BitmapB_address_high;
extern unsigned int  control_MSR_Bitmaps_address_full;
extern unsigned int  control_MSR_Bitmaps_address_high;
extern unsigned int  control_VM_exit_MSR_store_address_full;
extern unsigned int  control_VM_exit_MSR_store_address_high;
extern unsigned int  control_VM_exit_MSR_load_address_full;
extern unsigned int  control_VM_exit_MSR_load_address_high;
extern unsigned int  control_VM_entry_MSR_load_address_full;
extern unsigned int  control_VM_entry_MSR_load_address_high;
extern unsigned int  control_Executive_VMCS_pointer_full;
extern unsigned int  control_Executive_VMCS_pointer_high;
extern unsigned int  control_TSC_offset_full;
extern unsigned int  control_TSC_offset_high;
extern unsigned int  control_virtual_APIC_page_address_full;
extern unsigned int  control_virtual_APIC_page_address_high;
#if defined(__CONF_HARDWARE_PAGING__)
extern unsigned int 	control_EPT_pointer_full;
extern unsigned int 	control_EPT_pointer_high;
#endif

// Natural 64-bit Host-State fields
extern unsigned long long  host_CR0;
extern unsigned long long  host_CR3;
extern unsigned long long  host_CR4;
extern unsigned long long  host_FS_base;
extern unsigned long long  host_GS_base;
extern unsigned long long  host_TR_base;
extern unsigned long long  host_GDTR_base;
extern unsigned long long  host_IDTR_base;
extern unsigned long long  host_SYSENTER_ESP;
extern unsigned long long  host_SYSENTER_EIP;
extern unsigned long long  host_RSP;
extern unsigned long long  host_RIP;
// Natural 32-bit Host-State fields
extern unsigned int  host_SYSENTER_CS;
// Natural 16-bit Host-State fields
extern unsigned short  host_ES_selector;
extern unsigned short  host_CS_selector;
extern unsigned short  host_SS_selector;
extern unsigned short  host_DS_selector;
extern unsigned short  host_FS_selector;
extern unsigned short  host_GS_selector;
extern unsigned short  host_TR_selector;

// Natural 64-bit Guest-State fields
extern unsigned long long  guest_CR0;
extern unsigned long long  guest_CR3;
extern unsigned long long  guest_CR4;
extern unsigned long long  guest_ES_base;
extern unsigned long long  guest_CS_base; 
extern unsigned long long  guest_SS_base;
extern unsigned long long  guest_DS_base;
extern unsigned long long  guest_FS_base;
extern unsigned long long  guest_GS_base;
extern unsigned long long  guest_LDTR_base;
extern unsigned long long  guest_TR_base;
extern unsigned long long  guest_GDTR_base;
extern unsigned long long  guest_IDTR_base;
extern unsigned long long  guest_DR7;
extern unsigned long long  guest_RSP; 
extern unsigned long long  guest_RIP; 
extern unsigned long long  guest_RFLAGS; 
extern unsigned long long  guest_pending_debug_x;
extern unsigned long long  guest_SYSENTER_ESP;
extern unsigned long long  guest_SYSENTER_EIP;
// Natural 32-bit Guest-State fields
extern unsigned int  guest_ES_limit;
extern unsigned int  guest_CS_limit;
extern unsigned int  guest_SS_limit;
extern unsigned int  guest_DS_limit;
extern unsigned int  guest_FS_limit;
extern unsigned int  guest_GS_limit;
extern unsigned int  guest_LDTR_limit; 
extern unsigned int  guest_TR_limit;
extern unsigned int  guest_GDTR_limit;
extern unsigned int  guest_IDTR_limit;
extern unsigned int  guest_ES_access_rights; 
extern unsigned int  guest_CS_access_rights;
extern unsigned int  guest_SS_access_rights;
extern unsigned int  guest_DS_access_rights;
extern unsigned int  guest_FS_access_rights;
extern unsigned int  guest_GS_access_rights;
extern unsigned int  guest_LDTR_access_rights;
extern unsigned int  guest_TR_access_rights;
extern unsigned int  guest_interruptibility; 
extern unsigned int  guest_activity_state; 
extern unsigned int  guest_SMBASE;	// <-- Added 23 December 2006
extern unsigned int  guest_SYSENTER_CS; 
// Natural 16-bit Guest-State fields
extern unsigned short  guest_ES_selector;
extern unsigned short  guest_CS_selector;
extern unsigned short  guest_SS_selector;
extern unsigned short  guest_DS_selector;
extern unsigned short  guest_FS_selector;
extern unsigned short  guest_GS_selector;
extern unsigned short  guest_LDTR_selector;
extern unsigned short  guest_TR_selector;
// Full 64-bit Guest-State fields
extern unsigned int  guest_VMCS_link_pointer_full;
extern unsigned int  guest_VMCS_link_pointer_high;
extern unsigned int  guest_IA32_DEBUGCTL_full;
extern unsigned int  guest_IA32_DEBUGCTL_high;
#if defined(__CONF_HARDWARE_PAGING__)
extern unsigned int  guest_PDPTE0_full;
extern unsigned int  guest_PDPTE0_high;
extern unsigned int  guest_PDPTE1_full;
extern unsigned int  guest_PDPTE1_high;
extern unsigned int  guest_PDPTE2_full;
extern unsigned int  guest_PDPTE2_high;
extern unsigned int  guest_PDPTE3_full;
extern unsigned int  guest_PDPTE3_high;
#endif

extern u32	guest_CR2;

//------------------
// Read-Only Fields
//------------------
extern unsigned int  info_vminstr_error;
extern unsigned int  info_vmexit_reason;
extern unsigned int  info_vmexit_interrupt_information;
extern unsigned int  info_vmexit_interrupt_error_code;
extern unsigned int  info_IDT_vectoring_information;
extern unsigned int  info_IDT_vectoring_error_code;
extern unsigned int  info_vmexit_instruction_length;
extern unsigned int  info_vmx_instruction_information;
extern unsigned long long  info_exit_qualification;
extern unsigned long long  info_IO_RCX;
extern unsigned long long  info_IO_RSI;
extern unsigned long long  info_IO_RDI;
extern unsigned long long  info_IO_RIP;
extern unsigned long long  info_guest_linear_address;



#endif //__MACHINE_H_