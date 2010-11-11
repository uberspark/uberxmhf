//------------------------------------------------------------------------------
// globaldata.c
// this file contains ALL the global variables that are referenced throughout
// the runtime code
// the idea to bunch them all up in a seperate module/section is largely
// for ease of verification and measurement
// author: amit vasudevan (amitvasudevan@acm.org)

#include <target.h>

//the loader parameter block, this currently resides in a seperate section
//and is defined in runtimesup.S
//TODO: move it here and eliminate this extern
extern u32 _xtlpb[];
PXTLPB	lpb=(PXTLPB)_xtlpb;

//the hypervisor GDT, IDT and TSS, currently residing in runtimesup.S
//TODO: move it here and eliminate this extern
extern u32 x_gdt_start[], x_idt_start[], __runtimetss[];


//master-id table used for CPU LAPIC ID -> CPU VCPU structure mapping
u8 __midtable[SIZE_STRUCT_MIDTAB * MAX_MIDTAB_ENTRIES] __attribute__ (( section(".data") )) ;
MIDTAB *midtable = (MIDTAB *)__midtable;
//number of entries in the master-id table = number of physical cores in the system
u32 midtable_numentries;
//revised E820 memory-map buffer with the physical memory region corresponding
//to our hypervisor binary image marked reserved (0x2)
u8 __grube820buffer[SIZE_STRUCT_GRUBE820 * MAX_E820_ENTRIES] __attribute__ (( section(".data") )) ;
GRUBE820 *grube820list = (GRUBE820 *)__grube820buffer;
//buffer to hold entries of type PCPU (LAPIC id, version, base address and
//BSP flag) for every core in the system
u8 __mp_cpuinfo[SIZE_STRUCT_PCPU * MAX_PCPU_ENTRIES]__attribute__ (( section(".data") )) ;	
PCPU *pcpus= (PCPU *)__mp_cpuinfo;
//application parameter block, this is a read-only parameter block for
//emhf apps
APP_PARAM_BLOCK appParamBlock;
//runtime buffer for holding optional module contents
u8 bufferOptionalModule[SIZE_MAX_OPTIONAL_MODULE];
//runtime 3-level paging structures (PDPT and PDT)
//note: we don't have PTs as we use 2M pages for runtime paging
u8 runtime_3level_pdpt[PAGE_SIZE_4K] __attribute__ (( section(".vtdata") )) ;
u8 runtime_3level_pdt[PAE_PTRS_PER_PDPT * PAGE_SIZE_4K] __attribute__ (( section(".vtdata") ));

//critical MSRs that need to be saved/restored across guest VM switches
const u32 vmx_msr_area_msrs[] = {
	MSR_EFER, 
	MSR_K6_STAR,
};
//count of critical MSRs that need to be saved/restored across VM switches
const unsigned int vmx_msr_area_msrs_count = (sizeof(vmx_msr_area_msrs)/sizeof(vmx_msr_area_msrs[0]));

//VMX VMCS read-only field encodings
struct _vmcsrofields_encodings vmcsrofields_encodings[] = {
	{ 0x4400, offsetof(struct vmcsfields, info_vminstr_error) }, 
	{ 0x4402, offsetof(struct vmcsfields, info_vmexit_reason) },
	{ 0x4404, offsetof(struct vmcsfields, info_vmexit_interrupt_information) },
	{ 0x4406, offsetof(struct vmcsfields, info_vmexit_interrupt_error_code) },
	{ 0x4408, offsetof(struct vmcsfields, info_IDT_vectoring_information) },
	{ 0x440A, offsetof(struct vmcsfields, info_IDT_vectoring_error_code) },
	{ 0x440C, offsetof(struct vmcsfields, info_vmexit_instruction_length) },
	{ 0x440E, offsetof(struct vmcsfields, info_vmx_instruction_information) },
	{ 0x6400, offsetof(struct vmcsfields, info_exit_qualification) },
	{ 0x6402, offsetof(struct vmcsfields, info_IO_RCX) },
	{ 0x6404, offsetof(struct vmcsfields, info_IO_RSI) },
	{ 0x6406, offsetof(struct vmcsfields, info_IO_RDI) },
	{ 0x6408, offsetof(struct vmcsfields, info_IO_RIP) },
#if defined(__NESTED_PAGING__)
	{ 0x2400, offsetof(struct vmcsfields, guest_paddr_full) },
	{ 0x2401, offsetof(struct vmcsfields, guest_paddr_high) },
#endif
	{ 0x640A, offsetof(struct vmcsfields, info_guest_linear_address) } 
};
//count of VMX VMCS read-only fields
const unsigned int vmcsrofields_encodings_count = sizeof( vmcsrofields_encodings ) / sizeof( struct _vmcsrofields_encodings );

//VMX VMCS read-write field encodings
struct _vmcsrwfields_encodings vmcsrwfields_encodings[] = {
	// Control fields
	#if defined(__NESTED_PAGING__)
  //16-bit control field
  { 0x0000, offsetof(struct vmcsfields, control_vpid) },
	#endif
	// Natural 32-bit Control fields
	{ 0x4000, offsetof(struct vmcsfields, control_VMX_pin_based) },
	{ 0x4002, offsetof(struct vmcsfields, control_VMX_cpu_based) },
	{ 0x401E, offsetof(struct vmcsfields, control_VMX_seccpu_based) },
	{ 0x4004, offsetof(struct vmcsfields, control_exception_bitmap) },
	{ 0x4006, offsetof(struct vmcsfields, control_pagefault_errorcode_mask) },
	{ 0x4008, offsetof(struct vmcsfields, control_pagefault_errorcode_match) },
	{ 0x400A, offsetof(struct vmcsfields, control_CR3_target_count) },
	{ 0x400C, offsetof(struct vmcsfields, control_VM_exit_controls) },
	{ 0x400E, offsetof(struct vmcsfields, control_VM_exit_MSR_store_count) },
	{ 0x4010, offsetof(struct vmcsfields, control_VM_exit_MSR_load_count) },
	{ 0x4012, offsetof(struct vmcsfields, control_VM_entry_controls) },
	{ 0x4014, offsetof(struct vmcsfields, control_VM_entry_MSR_load_count) },
	{ 0x4016, offsetof(struct vmcsfields, control_VM_entry_interruption_information) },
	{ 0x4018, offsetof(struct vmcsfields, control_VM_entry_exception_errorcode) },
	{ 0x401A, offsetof(struct vmcsfields, control_VM_entry_instruction_length) },
	{ 0x401C, offsetof(struct vmcsfields, control_Task_PRivilege_Threshold) },
	// Natural 64-bit Control fields
	{ 0x6000, offsetof(struct vmcsfields, control_CR0_mask) },
	{ 0x6002, offsetof(struct vmcsfields, control_CR4_mask) }, 
	{ 0x6004, offsetof(struct vmcsfields, control_CR0_shadow) },
	{ 0x6006, offsetof(struct vmcsfields, control_CR4_shadow) },
	{ 0x6008, offsetof(struct vmcsfields, control_CR3_target0) },
	{ 0x600A, offsetof(struct vmcsfields, control_CR3_target1) },
	{ 0x600C, offsetof(struct vmcsfields, control_CR3_target2) },
	{ 0x600E, offsetof(struct vmcsfields, control_CR3_target3) },
	// Full 64-bit Control fields
	{ 0x2000, offsetof(struct vmcsfields, control_IO_BitmapA_address_full) },
	{ 0x2001, offsetof(struct vmcsfields, control_IO_BitmapA_address_high) },
	{ 0x2002, offsetof(struct vmcsfields, control_IO_BitmapB_address_full) },
	{ 0x2003, offsetof(struct vmcsfields, control_IO_BitmapB_address_high) },
	{ 0x2004, offsetof(struct vmcsfields, control_MSR_Bitmaps_address_full) },
	{ 0x2005, offsetof(struct vmcsfields, control_MSR_Bitmaps_address_high) }, 
	{ 0x2006, offsetof(struct vmcsfields, control_VM_exit_MSR_store_address_full) },
	{ 0x2007, offsetof(struct vmcsfields, control_VM_exit_MSR_store_address_high) },
	{ 0x2008, offsetof(struct vmcsfields, control_VM_exit_MSR_load_address_full) },
	{ 0x2009, offsetof(struct vmcsfields, control_VM_exit_MSR_load_address_high) },
	{ 0x200A, offsetof(struct vmcsfields, control_VM_entry_MSR_load_address_full) },
	{ 0x200B, offsetof(struct vmcsfields, control_VM_entry_MSR_load_address_high) },
	{ 0x200C, offsetof(struct vmcsfields, control_Executive_VMCS_pointer_full) },
	{ 0x200D, offsetof(struct vmcsfields, control_Executive_VMCS_pointer_high) },
	{ 0x2010, offsetof(struct vmcsfields, control_TSC_offset_full) },
	{ 0x2011, offsetof(struct vmcsfields, control_TSC_offset_high) },
	//{ 0x2012, offsetof(struct vmcsfields, control_virtual_APIC_page_address_full) }, 
	//{ 0x2013, offsetof(struct vmcsfields, control_virtual_APIC_page_address_high) },
	#if defined(__NESTED_PAGING__)
	{ 0x201A, offsetof(struct vmcsfields, control_EPT_pointer_full) },
	{ 0x201B, offsetof(struct vmcsfields, control_EPT_pointer_high) },
	#endif
	// Host-State fields
	// Natural 64-bit Host-State fields
	{ 0x6C00, offsetof(struct vmcsfields, host_CR0) },
	{ 0x6C02, offsetof(struct vmcsfields, host_CR3) },
	{ 0x6C04, offsetof(struct vmcsfields, host_CR4) },
	{ 0x6C06, offsetof(struct vmcsfields, host_FS_base) },
	{ 0x6C08, offsetof(struct vmcsfields, host_GS_base) },
	{ 0x6C0A, offsetof(struct vmcsfields, host_TR_base) },
	{ 0x6C0C, offsetof(struct vmcsfields, host_GDTR_base) },
	{ 0x6C0E, offsetof(struct vmcsfields, host_IDTR_base) },
	{ 0x6C10, offsetof(struct vmcsfields, host_SYSENTER_ESP) },
	{ 0x6C12, offsetof(struct vmcsfields, host_SYSENTER_EIP) },
	{ 0x6C14, offsetof(struct vmcsfields, host_RSP) },
	{ 0x6C16, offsetof(struct vmcsfields, host_RIP) },
	// Natural 32-bit Host-State fields
	{ 0x4C00, offsetof(struct vmcsfields, host_SYSENTER_CS) },
	// Natural 16-bit Host-State fields
	{ 0x0C00, offsetof(struct vmcsfields, host_ES_selector) },
	{ 0x0C02, offsetof(struct vmcsfields, host_CS_selector) },
	{ 0x0C04, offsetof(struct vmcsfields, host_SS_selector) },
	{ 0x0C06, offsetof(struct vmcsfields, host_DS_selector) },
	{ 0x0C08, offsetof(struct vmcsfields, host_FS_selector) },
	{ 0x0C0A, offsetof(struct vmcsfields, host_GS_selector) },
	{ 0x0C0C, offsetof(struct vmcsfields, host_TR_selector) },
	// Guest-State fields
	// Natural 64-bit Guest-State fields
	{ 0x6800, offsetof(struct vmcsfields, guest_CR0) },
	{ 0x6802, offsetof(struct vmcsfields, guest_CR3) },
	{ 0x6804, offsetof(struct vmcsfields, guest_CR4) },
	{ 0x6806, offsetof(struct vmcsfields, guest_ES_base) },
	{ 0x6808, offsetof(struct vmcsfields, guest_CS_base) },
	{ 0x680A, offsetof(struct vmcsfields, guest_SS_base) },
	{ 0x680C, offsetof(struct vmcsfields, guest_DS_base) },
	{ 0x680E, offsetof(struct vmcsfields, guest_FS_base) },
	{ 0x6810, offsetof(struct vmcsfields, guest_GS_base) },
	{ 0x6812, offsetof(struct vmcsfields, guest_LDTR_base) },
	{ 0x6814, offsetof(struct vmcsfields, guest_TR_base) },
	{ 0x6816, offsetof(struct vmcsfields, guest_GDTR_base) },
	{ 0x6818, offsetof(struct vmcsfields, guest_IDTR_base) },
	{ 0x681A, offsetof(struct vmcsfields, guest_DR7) },
	{ 0x681C, offsetof(struct vmcsfields, guest_RSP) },
	{ 0x681E, offsetof(struct vmcsfields, guest_RIP) },
	{ 0x6820, offsetof(struct vmcsfields, guest_RFLAGS) },
	{ 0x6822, offsetof(struct vmcsfields, guest_pending_debug_x) },
	{ 0x6824, offsetof(struct vmcsfields, guest_SYSENTER_ESP) },
	{ 0x6826, offsetof(struct vmcsfields, guest_SYSENTER_EIP) },
	#if defined(__NESTED_PAGING__)
	{ 0x280A, offsetof(struct vmcsfields, guest_PDPTE0_full) },
	{ 0x280B, offsetof(struct vmcsfields, guest_PDPTE0_high) },
	{ 0x280C, offsetof(struct vmcsfields, guest_PDPTE1_full) },
	{ 0x280D, offsetof(struct vmcsfields, guest_PDPTE1_high) },
	{ 0x280E, offsetof(struct vmcsfields, guest_PDPTE2_full) },
	{ 0x280F, offsetof(struct vmcsfields, guest_PDPTE2_high) },
	{ 0x2810, offsetof(struct vmcsfields, guest_PDPTE3_full) },
	{ 0x2811, offsetof(struct vmcsfields, guest_PDPTE3_high) },
	#endif
	// Natural 32-bit Guest-State fields
	{ 0x4800, offsetof(struct vmcsfields, guest_ES_limit) },
	{ 0x4802, offsetof(struct vmcsfields, guest_CS_limit) },
	{ 0x4804, offsetof(struct vmcsfields, guest_SS_limit) },
	{ 0x4806, offsetof(struct vmcsfields, guest_DS_limit) },
	{ 0x4808, offsetof(struct vmcsfields, guest_FS_limit) },
	{ 0x480A, offsetof(struct vmcsfields, guest_GS_limit) },
	{ 0x480C, offsetof(struct vmcsfields, guest_LDTR_limit) },
	{ 0x480E, offsetof(struct vmcsfields, guest_TR_limit) },
	{ 0x4810, offsetof(struct vmcsfields, guest_GDTR_limit) },
	{ 0x4812, offsetof(struct vmcsfields, guest_IDTR_limit) },
	{ 0x4814, offsetof(struct vmcsfields, guest_ES_access_rights) },
	{ 0x4816, offsetof(struct vmcsfields, guest_CS_access_rights) },
	{ 0x4818, offsetof(struct vmcsfields, guest_SS_access_rights) },
	{ 0x481A, offsetof(struct vmcsfields, guest_DS_access_rights) },
	{ 0x481C, offsetof(struct vmcsfields, guest_FS_access_rights) },
	{ 0x481E, offsetof(struct vmcsfields, guest_GS_access_rights) },
	{ 0x4820, offsetof(struct vmcsfields, guest_LDTR_access_rights) },
	{ 0x4822, offsetof(struct vmcsfields, guest_TR_access_rights) },
	{ 0x4824, offsetof(struct vmcsfields, guest_interruptibility) },
	{ 0x4826, offsetof(struct vmcsfields, guest_activity_state) },
	{ 0x4828, offsetof(struct vmcsfields, guest_SMBASE) },
	{ 0x482A, offsetof(struct vmcsfields, guest_SYSENTER_CS) },
	// Natural 16-bit Guest-State fields
	{ 0x0800, offsetof(struct vmcsfields, guest_ES_selector) },
	{ 0x0802, offsetof(struct vmcsfields, guest_CS_selector) },
	{ 0x0804, offsetof(struct vmcsfields, guest_SS_selector) },
	{ 0x0806, offsetof(struct vmcsfields, guest_DS_selector) },
	{ 0x0808, offsetof(struct vmcsfields, guest_FS_selector) },
	{ 0x080A, offsetof(struct vmcsfields, guest_GS_selector) },
	{ 0x080C, offsetof(struct vmcsfields, guest_LDTR_selector) },
	{ 0x080E, offsetof(struct vmcsfields, guest_TR_selector) },
	// Full 64-bit Guest-State fields
	{ 0x2800, offsetof(struct vmcsfields, guest_VMCS_link_pointer_full) },
	{ 0x2801, offsetof(struct vmcsfields, guest_VMCS_link_pointer_high) },
	{ 0x2802, offsetof(struct vmcsfields, guest_IA32_DEBUGCTL_full) },
	{ 0x2803, offsetof(struct vmcsfields, guest_IA32_DEBUGCTL_high) } 
};

//count of VMX VMCS read-write fields
const unsigned int vmcsrwfields_encodings_count = sizeof( vmcsrwfields_encodings ) / sizeof( struct _vmcsrwfields_encodings );

//virtual LAPIC page to trap LAPIC accesses for MP guests
u8 memregion_virtual_LAPIC[PAGE_SIZE_4K] __attribute__(( section(".vtdata" ) ));


//variable which is incremented by 1 for all cores which had a successful
//appmain initialization
u32 appmain_success_counter=0;
//lock for the above
u32 lock_appmain_success_counter=1;


//---core-quiescing variables
//the quiesce counter, all CPUs except for the one requesting the
//quiesce will increment this when they get their quiesce signal
u32 quiesce_counter=0;
u32 lock_quiesce_counter=1; //spinlock to access the above

//resume counter to rally all CPUs after resumption from quiesce
u32 quiesce_resume_counter=0;
u32 lock_quiesce_resume_counter=1; //spinlock to access the above

//the quiesce variable and its lock
u32 quiesce=0;      //if 1, then we have a quiesce in process
u32 lock_quiesce=1; 

//resume signal
u32 quiesce_resume_signal=0; //signal becomes 1 to resume after quiescing
u32 lock_quiesce_resume_signal=1; //spinlock to access the above



//------------------------------------------------------------------------------
//data that needs to exist per-core and needs to be initialized within
//the VCPU structure for that core

//VCPU structures for individial cores
u8 memregion_vcpubuffers[MAX_PCPU_ENTRIES * SIZE_STRUCT_VCPU] __attribute__ (( section(".data") )) ;

//runtime stacks for individual cores
u8 memregion_cpustacks[MAX_PCPU_ENTRIES * RUNTIME_STACK_SIZE] __attribute__ (( section(".stack") )) ;

//VMX VMXON buffers for each core
u8 memregion_vmx_vmxon_buffers[MAX_PCPU_ENTRIES * PAGE_SIZE_4K] __attribute__ (( section(".vtdata") )) ;

//VMX VMCS buffers for each core
u8 memregion_vmx_vmcs_buffers[MAX_PCPU_ENTRIES * PAGE_SIZE_4K] __attribute__ (( section(".vtdata") )) ;

//VMX IO Bitmap area
u8 memregion_vmx_iobitmap[MAX_PCPU_ENTRIES * (2*PAGE_SIZE_4K)] __attribute__(( section(".vtdata" ) ));

//VMX host-MSR save area
u8 memregion_vmx_msr_area_host[MAX_PCPU_ENTRIES * (2*PAGE_SIZE_4K)] __attribute__(( section(".vtdata" ) ));

//VMX guest-MSR save area
u8 memregion_vmx_msr_area_guest[MAX_PCPU_ENTRIES * (2*PAGE_SIZE_4K)] __attribute__(( section(".vtdata" ) ));

//VMX MSR bitmap area
	//the MSR bitmap is split into 4 regions each 1K in size (total = 4K)
	//0-1K = read-bitmap for 8K MSRs from 0000-1FFFh
	//1-2K = read-bitmap for 8K MSRs from 0xC0000000-0xC0001FFFh
	//2-3K = write-bitmap for 8K MSRs from 0000-1FFFh
	//3-4K = write-bitmap for 8K MSRs from 0xC0000000-0xC0001FFFh
	//if a bit in the bitmap is '1' then it triggers a VMEXIT for RDMSR/WRMSR
u8 memregion_vmx_msrbitmaps[MAX_PCPU_ENTRIES * PAGE_SIZE_4K] __attribute__(( section(".vtdata" ) ));

//VMX EPT PML4 table 
u8 memregion_vmx_ept_pml4_table[MAX_PCPU_ENTRIES * PAGE_SIZE_4K] __attribute__(( section(".vtdata" ) ));

//VMX EPT PDPT table
u8 memregion_vmx_ept_pdp_table[MAX_PCPU_ENTRIES * PAGE_SIZE_4K] __attribute__(( section(".vtdata" ) ));

//VMX EPT PDT tables
u8 memregion_vmx_ept_pd_tables[MAX_PCPU_ENTRIES * (PAGE_SIZE_4K*4)] __attribute__(( section(".vtdata" ) ));	

//VMX EPT P tables
u8 memregion_vmx_ept_p_tables[MAX_PCPU_ENTRIES * (PAGE_SIZE_4K*2048)] __attribute__(( section(".vtdata" ) )); //4GB	

//v86monitor page directory
u8 memregion_v86m_pagedir[MAX_PCPU_ENTRIES * PAGE_SIZE_4K] __attribute__(( section(".vtdata" ) ));

//v86monitor page tables, together they address 4G but really only 1MB is
//what we need for guest real-mode code
u8 memregion_v86m_pagetables[MAX_PCPU_ENTRIES * (1024 * PAGE_SIZE_4K)] __attribute__(( section(".vtdata" ) ));

//v86monitor IDT
u8 memregion_v86m_idt[MAX_PCPU_ENTRIES * PAGE_SIZE_4K] __attribute__(( section(".vtdata" ) ));

//v86monitor GDT
u8 memregion_v86m_gdt[MAX_PCPU_ENTRIES * PAGE_SIZE_4K] __attribute__(( section(".vtdata" ) ));

//v86monitor LDT 
u8 memregion_v86m_ldt[MAX_PCPU_ENTRIES * PAGE_SIZE_4K] __attribute__(( section(".vtdata" ) ));

//v86monitor TSS
u8 memregion_v86m_tss[MAX_PCPU_ENTRIES * (4 * PAGE_SIZE_4K)] __attribute__(( section(".vtdata" ) ));

//v86monitor ring-0 stack, we run guest real-mode code in v8086 mode
//this requires the v86monitor to run at ring-0
u8 memregion_v86m_ring0stack[MAX_PCPU_ENTRIES * (4 * PAGE_SIZE_4K)] __attribute__(( section(".vtdata" ) ));

//limbo GDT needed when guest switches from real to protected-mode limbo
u8 memregion_limbo_gdt [MAX_PCPU_ENTRIES * LIMBO_GDT_SIZE] __attribute__(( section(".vtdata" ) ));

//limbo TSS needed when guest switches from real to protected-mode limbo
u8 memregion_limbo_tss [MAX_PCPU_ENTRIES * LIMBO_TSS_SIZE] __attribute__(( section(".vtdata" ) ));


