//------------------------------------------------------------------------------
// islayer_ug.c
// isolation layer code specific to  
// VMX impl. with unrestricted guest caps.
// author: amit vasudevan (amitvasudevan@acm.org) 

#include <target.h>


//---globals referenced by this module------------------------------------------
extern u32 x_gdt_start[], x_idt_start[], __runtimetss[];
extern void __islayer_callback(void);
extern const u32 vmx_msr_area_msrs[];
extern const unsigned int vmx_msr_area_msrs_count;
extern u32 * vmx_decode_reg(u32 gpr, VCPU *vcpu, struct regs *r);

//--initunrestrictedguestVMCS: initializes VMCS for unrestricted guest ---------
void initunrestrictedguestVMCS(VCPU *vcpu){
		u32 lodword, hidword;

			//clear VMCS
			memset((void *)&vcpu->vmcs, 0, sizeof(struct vmcsfields));
			
			//setup host state
			vcpu->vmcs.host_CR0 = read_cr0();
			vcpu->vmcs.host_CR4 = read_cr4();
			vcpu->vmcs.host_CR3 = read_cr3();
			vcpu->vmcs.host_CS_selector = read_segreg_cs();
			vcpu->vmcs.host_DS_selector = read_segreg_ds();
			vcpu->vmcs.host_ES_selector = read_segreg_es();
			vcpu->vmcs.host_FS_selector = read_segreg_fs();
			vcpu->vmcs.host_GS_selector = read_segreg_gs();
			vcpu->vmcs.host_SS_selector = read_segreg_ss();
			vcpu->vmcs.host_TR_selector = read_tr_sel();
			vcpu->vmcs.host_GDTR_base = (u64)(u32)x_gdt_start;
			vcpu->vmcs.host_IDTR_base = (u64)(u32)x_idt_start;
			vcpu->vmcs.host_TR_base = (u64)(u32)__runtimetss;
			vcpu->vmcs.host_RIP = (u64)(u32)__islayer_callback;
			vcpu->vmcs.host_RSP = (u64)vcpu->esp;
			rdmsr(IA32_SYSENTER_CS_MSR, &lodword, &hidword);
      vcpu->vmcs.host_SYSENTER_CS = lodword;
      rdmsr(IA32_SYSENTER_ESP_MSR, &lodword, &hidword);
      vcpu->vmcs.host_SYSENTER_ESP = (u64) (((u64)hidword << 32) | (u64)lodword);
      rdmsr(IA32_SYSENTER_EIP_MSR, &lodword, &hidword);
      vcpu->vmcs.host_SYSENTER_EIP = (u64) (((u64)hidword << 32) | (u64)lodword);
      rdmsr(IA32_MSR_FS_BASE, &lodword, &hidword);
      vcpu->vmcs.host_FS_base = (u64) (((u64)hidword << 32) | (u64)lodword);
      rdmsr(IA32_MSR_GS_BASE, &lodword, &hidword);
      vcpu->vmcs.host_GS_base = (u64) (((u64)hidword << 32) | (u64)lodword);

      //setup default VMX controls
 			vcpu->vmcs.control_VMX_pin_based = vcpu->vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR];
      vcpu->vmcs.control_VMX_cpu_based = vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR];
			vcpu->vmcs.control_VM_exit_controls = vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR];
 			vcpu->vmcs.control_VM_entry_controls = vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR];
      
 			//IO bitmap support
			vcpu->vmcs.control_IO_BitmapA_address_full = (u32)__hva2spa__((u32)vcpu->vmx_vaddr_iobitmap);
			vcpu->vmcs.control_IO_BitmapA_address_high = 0;
			vcpu->vmcs.control_IO_BitmapB_address_full = (u32)__hva2spa__( ((u32)vcpu->vmx_vaddr_iobitmap + PAGE_SIZE_4K) );
			vcpu->vmcs.control_IO_BitmapB_address_high = 0;
			vcpu->vmcs.control_VMX_cpu_based |= (1 << 25); //enable use IO Bitmaps

 			//MSR bitmap support
			memset( (void *)vcpu->vmx_vaddr_msrbitmaps, 0xFFFFFFFFUL, PAGE_SIZE_4K); //trap all MSR accesses
			vcpu->vmcs.control_MSR_Bitmaps_address_full = (u32)__hva2spa__((u32)vcpu->vmx_vaddr_msrbitmaps);	 							
			vcpu->vmcs.control_MSR_Bitmaps_address_high = 0;
			vcpu->vmcs.control_VMX_cpu_based |= (1 << 28); //enable use MSR Bitmaps 


#if 1
			//Critical MSR load/store
			{
					u32 i;
  				msr_entry_t *hmsr = (msr_entry_t *)vcpu->vmx_vaddr_msr_area_host;
					msr_entry_t *gmsr = (msr_entry_t *)vcpu->vmx_vaddr_msr_area_guest;

					//store initial values of the MSRs
					for(i=0; i < vmx_msr_area_msrs_count; i++){
						u32 msr, eax, edx;
	          msr = vmx_msr_area_msrs[i];						
						rdmsr(msr, &eax, &edx);
						hmsr[i].index = gmsr[i].index = msr;
						hmsr[i].data = gmsr[i].data = ((u64)edx << 32) | (u64)eax;
					}
					
					//host MSR load on exit, we store it ourselves before entry
					vcpu->vmcs.control_VM_exit_MSR_load_address_full=(u32)__hva2spa__((u32)vcpu->vmx_vaddr_msr_area_host);
					vcpu->vmcs.control_VM_exit_MSR_load_address_high=0;
					vcpu->vmcs.control_VM_exit_MSR_load_count= vmx_msr_area_msrs_count;
					
					//guest MSR load on entry, store on exit
					vcpu->vmcs.control_VM_entry_MSR_load_address_full=(u32)__hva2spa__((u32)vcpu->vmx_vaddr_msr_area_guest);
					vcpu->vmcs.control_VM_entry_MSR_load_address_high=0;
					vcpu->vmcs.control_VM_entry_MSR_load_count=vmx_msr_area_msrs_count;
				  vcpu->vmcs.control_VM_exit_MSR_store_address_full=(u32)__hva2spa__((u32)vcpu->vmx_vaddr_msr_area_guest);
					vcpu->vmcs.control_VM_exit_MSR_store_address_high=0;
					vcpu->vmcs.control_VM_exit_MSR_store_count=vmx_msr_area_msrs_count;
			}
#endif


			vcpu->vmcs.control_pagefault_errorcode_mask  = 0x00000000;	//dont be concerned with 
			vcpu->vmcs.control_pagefault_errorcode_match = 0x00000000; //guest page-faults
			vcpu->vmcs.control_exception_bitmap = 0;
			vcpu->vmcs.control_CR3_target_count = 0;
      
      //setup guest state
      	//CR0, real-mode, PE and PG bits cleared
     		vcpu->vmcs.guest_CR0 = vcpu->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR];
     		vcpu->vmcs.guest_CR0 &= ~(CR0_PE);
     		vcpu->vmcs.guest_CR0 &= ~(CR0_PG);
     		//CR4, required bits set (usually VMX enabled bit)
   			vcpu->vmcs.guest_CR4 = vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR];
				//CR3 set to 0, does not matter
				vcpu->vmcs.guest_CR3 = 0;
				//IDTR
				vcpu->vmcs.guest_IDTR_base = 0;
				vcpu->vmcs.guest_IDTR_limit = 0x3ff;	//16-bit IVT
				//GDTR
				vcpu->vmcs.guest_GDTR_base = 0;
				vcpu->vmcs.guest_GDTR_limit = 0;	//no GDT
				//LDTR, unusable
				vcpu->vmcs.guest_LDTR_base = 0;
				vcpu->vmcs.guest_LDTR_limit = 0;
				vcpu->vmcs.guest_LDTR_selector = 0;
				vcpu->vmcs.guest_LDTR_access_rights = 0x10000;
				//TR, should be usable for VMX to work, but not used by guest
				vcpu->vmcs.guest_TR_base = 0;
				vcpu->vmcs.guest_TR_limit = 0;
				vcpu->vmcs.guest_TR_selector = 0;
				vcpu->vmcs.guest_TR_access_rights = 0x83; //present, 16-bit busy TSS
				//RSP
				vcpu->vmcs.guest_RSP = 0x0;
				//RIP
				vcpu->vmcs.guest_RIP = 0x7c00;
				vcpu->vmcs.guest_CS_selector = 0;
				vcpu->vmcs.guest_CS_base = 0;
				vcpu->vmcs.guest_CS_limit = 0xFFFF;	//64K
				vcpu->vmcs.guest_CS_access_rights = 0x93; //present, system, read-write accessed
				
				//RFLAGS
				vcpu->vmcs.guest_RFLAGS = 0; 
				vcpu->vmcs.guest_RFLAGS &= ~((1<<3)|(1<<5)|(1<<15));	// reserved 0-bits
				vcpu->vmcs.guest_RFLAGS |= (1<<1);				// reserved 1-bits
				vcpu->vmcs.guest_RFLAGS |= (1<<9);				// IF = enable 
				vcpu->vmcs.guest_RFLAGS &= ~(1<<14);			// Nested Task = disable
				//CS, DS, ES, FS, GS and SS segments
				vcpu->vmcs.guest_DS_selector = 0;
				vcpu->vmcs.guest_DS_base = 0;
				vcpu->vmcs.guest_DS_limit = 0xFFFF;	//64K
				vcpu->vmcs.guest_DS_access_rights = 0x93; //present, system, read-write accessed
				vcpu->vmcs.guest_ES_selector = 0;
				vcpu->vmcs.guest_ES_base = 0;
				vcpu->vmcs.guest_ES_limit = 0xFFFF;	//64K
				vcpu->vmcs.guest_ES_access_rights = 0x93; //present, system, read-write accessed
				vcpu->vmcs.guest_FS_selector = 0;
				vcpu->vmcs.guest_FS_base = 0;
				vcpu->vmcs.guest_FS_limit = 0xFFFF;	//64K
				vcpu->vmcs.guest_FS_access_rights = 0x93; //present, system, read-write accessed
				vcpu->vmcs.guest_GS_selector = 0;
				vcpu->vmcs.guest_GS_base = 0;
				vcpu->vmcs.guest_GS_limit = 0xFFFF;	//64K
				vcpu->vmcs.guest_GS_access_rights = 0x93; //present, system, read-write accessed
				vcpu->vmcs.guest_SS_selector = 0x0;
				vcpu->vmcs.guest_SS_base = 0x0;
				vcpu->vmcs.guest_SS_limit = 0xFFFF;	//64K
				vcpu->vmcs.guest_SS_access_rights = 0x93; //present, system, read-write accessed

			//activate secondary processor controls
      vcpu->vmcs.control_VMX_seccpu_based = vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR];
			vcpu->vmcs.control_VMX_cpu_based |= (1 << 31); //activate secondary processor controls

#if defined (__NESTED_PAGING__)
      //setup EPT
      vmx_gathermemorytypes(vcpu);
      vmx_setupEPT(vcpu);
			vcpu->vmcs.control_VMX_seccpu_based |= (1 << 1); //enable EPT
			vcpu->vmcs.control_VMX_seccpu_based |= (1 << 5); //enable VPID
 			vcpu->vmcs.control_vpid = 1; //VPID=0 is reserved for hypervisor
 			vcpu->vmcs.control_EPT_pointer_high = 0;
 			vcpu->vmcs.control_EPT_pointer_full = __hva2spa__((u32)vcpu->vmx_vaddr_ept_pml4_table) | 0x1E; //page walk of 4 and WB memory
			vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 15); //disable CR3 load exiting
			vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 16); //disable CR3 store exiting
#endif

			//setup unrestricted guest
			vcpu->vmcs.control_VMX_seccpu_based |= (1 << 7); //enable unrestricted guest
			
			//setup VMCS link pointer
		  vcpu->vmcs.guest_VMCS_link_pointer_full = (u32)0xFFFFFFFFUL;
			vcpu->vmcs.guest_VMCS_link_pointer_high = (u32)0xFFFFFFFFUL;
	
			//setup NMI intercept for core-quiescing
			vcpu->vmcs.control_VMX_pin_based |= (1 << 3);	//intercept NMIs
	
			
			//trap access to CR4 fixed bits (this includes the VMXE bit)
			vcpu->vmcs.control_CR4_mask = vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR];  
			vcpu->vmcs.control_CR4_shadow = CR4_VMXE; //let guest know we have VMX enabled

	
			//flush guest TLB to start with
			__vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);

}


//---CR4 access handler---------------------------------------------------------
void handle_intercept_cr4access_ug(VCPU *vcpu, struct regs *r, u32 gpr, u32 tofrom){
	ASSERT(tofrom == VMX_CRX_ACCESS_TO);

  printf("\nCPU(0x%02x): CS:EIP=0x%04x:0x%08x MOV CR4, xx", vcpu->id,
    (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);
  
	printf("\nMOV TO CR4 (flush TLB?), current=0x%08x, proposed=0x%08x",
			(u32)vcpu->vmcs.guest_CR4, *((u32 *)vmx_decode_reg(gpr, vcpu, r)) );

  #if defined (__NESTED_PAGING__)
  //we need to flush EPT mappings as we emulated CR4 load above
  __vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);
  #endif

}
