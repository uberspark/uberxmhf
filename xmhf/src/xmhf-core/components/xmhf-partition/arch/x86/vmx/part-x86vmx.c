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
 * EMHF partition component interface (x86 VMX backend)
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>

//---globals referenced by this module------------------------------------------
//TODO: need to remove these direct references
extern u32 x_gdt_start[], x_idt_start[]; //runtimesup.S


//critical MSRs that need to be saved/restored across guest VM switches
static const u32 vmx_msr_area_msrs[] = {
	MSR_EFER, 
	MSR_IA32_PAT,
	MSR_K6_STAR,
};
//count of critical MSRs that need to be saved/restored across VM switches
static const unsigned int vmx_msr_area_msrs_count = (sizeof(vmx_msr_area_msrs)/sizeof(vmx_msr_area_msrs[0]));


//---initVT: initializes CPU VT-------------------------------------------------
static void _vmx_initVT(VCPU *vcpu){
	//step-0: to enable VMX on a core, we require it to have a TR loaded,
	//so load it for this core
	//__vmx_loadTR();
	{
	  u32 gdtstart = (u32)&x_gdt_start;
	  u16 trselector = 	__TRSEL;
	  asm volatile("movl %0, %%edi\r\n"
		"xorl %%eax, %%eax\r\n"
		"movw %1, %%ax\r\n"
		"addl %%eax, %%edi\r\n"		//%edi is pointer to TSS descriptor in GDT
		"addl $0x4, %%edi\r\n"		//%edi points to top 32-bits of 64-bit TSS desc.
		"lock andl $0xFFFF00FF, (%%edi)\r\n"
		"lock orl  $0x00008900, (%%edi)\r\n"
		"ltr %%ax\r\n"				//load TR
	     : 
	     : "m"(gdtstart), "m"(trselector)
	     : "edi", "eax"
	  );
	}
	


  //step-1: check if intel CPU
  {
    char cpu_oemid[12];
	  asm(	"xor	%%eax, %%eax \n"
				  "cpuid \n"		
				  "mov	%%ebx, %0 \n"
				  "mov	%%edx, %1 \n"
				  "mov	%%ecx, %2 \n"
			     :: "m"(cpu_oemid[0]), "m"(cpu_oemid[4]), "m"(cpu_oemid[8]): "eax", "ebx", "ecx", "edx" );

   	if ( strncmp( cpu_oemid, "GenuineIntel", 12 ) ){
   	  printf("\nCPU(0x%02x) is not an Intel CPU. Halting!", vcpu->id);
   	  HALT();
   	}
  }
  
  //step-2: check VT support
  {
  	u32	cpu_features;
    asm("mov	$1, %%eax \n"
				"cpuid \n"
				"mov	%%ecx, %0	\n"
				::"m"(cpu_features): "eax", "ebx", "ecx", "edx" );
		if ( ( cpu_features & (1<<5) ) == 0 ){
			printf("CPU(0x%02x) does not support VT. Halting!", vcpu->id);
      HALT();
		}
  }

  //step-3: save contents of VMX MSRs as well as MSR EFER and EFCR 
  //into vcpu
  {
    u32 i;
    u32 eax, edx;
    for(i=0; i < IA32_VMX_MSRCOUNT; i++){
        rdmsr( (IA32_VMX_BASIC_MSR + i), &eax, &edx);
        vcpu->vmx_msrs[i] = (u64)edx << 32 | (u64) eax;        
    }
  
    rdmsr(MSR_EFER, &eax, &edx);
    vcpu->vmx_msr_efer = (u64)edx << 32 | (u64) eax;
    rdmsr(MSR_EFCR, &eax, &edx);
    vcpu->vmx_msr_efcr = (u64)edx << 32 | (u64) eax;
  
    //[debug: dump contents of MSRs]
    for(i=0; i < IA32_VMX_MSRCOUNT; i++)
       printf("\nCPU(0x%02x): VMX MSR 0x%08x = 0x%08x%08x", vcpu->id, IA32_VMX_BASIC_MSR+i, 
          (u32)((u64)vcpu->vmx_msrs[i] >> 32), (u32)vcpu->vmx_msrs[i]);
    
		//check if VMX supports unrestricted guest, if so we don't need the
		//v86 monitor and the associated state transition handling
		if( (u32)((u64)vcpu->vmx_msrs[IA32_VMX_MSRCOUNT-1] >> 32) & 0x80 )
			vcpu->vmx_guest_unrestricted = 1;
		else
			vcpu->vmx_guest_unrestricted = 0;
				
		#if defined(__DISABLE_UG__)
		//for now disable unrestricted bit, as we still need to intercept
		//E820 mem-map access and VMX doesnt provide software INT intercept :(
		vcpu->guest_unrestricted=0;
		#endif				
				
		if(vcpu->vmx_guest_unrestricted)
			printf("\nCPU(0x%02x): UNRESTRICTED-GUEST supported.", vcpu->id);
		
		printf("\nCPU(0x%02x): MSR_EFER=0x%08x%08x", vcpu->id, (u32)((u64)vcpu->vmx_msr_efer >> 32), 
          (u32)vcpu->vmx_msr_efer);
    printf("\nCPU(0x%02x): MSR_EFCR=0x%08x%08x", vcpu->id, (u32)((u64)vcpu->vmx_msr_efcr >> 32), 
          (u32)vcpu->vmx_msr_efcr);
  
  }

  //step-4: enable VMX by setting CR4
	asm(	" mov  %%cr4, %%eax	\n"\
		" bts  $13, %%eax	\n"\
		" mov  %%eax, %%cr4	" ::: "eax" );
  printf("\nCPU(0x%02x): enabled VMX", vcpu->id);

	  //step-5:enter VMX root operation using VMXON
	  {
	  	u32 retval=0;
	  	u64 vmxonregion_paddr = hva2spa((void*)vcpu->vmx_vmxonregion_vaddr);
	    //set VMCS rev id
	  	*((u32 *)vcpu->vmx_vmxonregion_vaddr) = (u32)vcpu->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];
	    
	   	asm( "vmxon %1 \n"
				 "jbe vmfail \n"
				 "movl $0x1, %%eax \n" 
				 "movl %%eax, %0 \n"
				 "jmp vmsuccess \n"
				 "vmfail: \n"
				 "movl $0x0, %%eax \n"
				 "movl %%eax, %0 \n"
				 "vmsuccess: \n" 
	       : "=m" (retval)
	       : "m"(vmxonregion_paddr) 
	       : "eax");
		
	    if(!retval){
	      printf("\nCPU(0x%02x): Fatal, unable to enter VMX root operation", vcpu->id);
	      HALT();
	    }  
	  
	    printf("\nCPU(0x%02x): Entered VMX root operation", vcpu->id);
	  }
	
}

//---vmx int 15 hook enabling function------------------------------------------
static void	_vmx_int15_initializehook(VCPU *vcpu){
	//we should only be called from the BSP
	ASSERT(vcpu->isbsp);
	
	{
		u8 *bdamemory = (u8 *)0x4AC;				//use BDA reserved memory at 0040:00AC
		
		u16 *ivt_int15 = (u16 *)(0x54);			//32-bit CS:IP for IVT INT 15 handler
		
		//printf("\nCPU(0x%02x): original BDA dump: %02x %02x %02x %02x %02x %02x %02x %02x", vcpu->id,
		//	bdamemory[0], bdamemory[1], bdamemory[2], bdamemory[3], bdamemory[4],
		//		bdamemory[5], bdamemory[6], bdamemory[7]);
		
		printf("\nCPU(0x%02x): original INT 15h handler at 0x%04x:0x%04x", vcpu->id,
			ivt_int15[1], ivt_int15[0]);

		//we need 8 bytes (4 for the VMCALL followed by IRET and 4 for he original 
		//IVT INT 15h handler address, zero them to start off
		memset(bdamemory, 0x0, 8);		

		//printf("\nCPU(0x%02x): BDA dump after clear: %02x %02x %02x %02x %02x %02x %02x %02x", vcpu->id,
		//	bdamemory[0], bdamemory[1], bdamemory[2], bdamemory[3], bdamemory[4],
		//		bdamemory[5], bdamemory[6], bdamemory[7]);

		//implant VMCALL followed by IRET at 0040:04AC
		bdamemory[0]= 0x0f;	//VMCALL						
		bdamemory[1]= 0x01;
		bdamemory[2]= 0xc1;																	
		bdamemory[3]= 0xcf;	//IRET
		
		//store original INT 15h handler CS:IP following VMCALL and IRET
		*((u16 *)(&bdamemory[4])) = ivt_int15[0];	//original INT 15h IP
		*((u16 *)(&bdamemory[6])) = ivt_int15[1];	//original INT 15h CS

		//printf("\nCPU(0x%02x): BDA dump after hook implant: %02x %02x %02x %02x %02x %02x %02x %02x", vcpu->id,
		//	bdamemory[0], bdamemory[1], bdamemory[2], bdamemory[3], bdamemory[4],
		//		bdamemory[5], bdamemory[6], bdamemory[7]);

		//point IVT INT15 handler to the VMCALL instruction
		ivt_int15[0]=0x00AC;
		ivt_int15[1]=0x0040;					
	}
}


//--initunrestrictedguestVMCS: initializes VMCS for unrestricted guest ---------
void vmx_initunrestrictedguestVMCS(VCPU *vcpu){
	u32 lodword, hidword;

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
	vcpu->vmcs.host_IDTR_base = (u64)(u32)emhf_xcphandler_get_idt_start();
	vcpu->vmcs.host_TR_base = (u64)(u32)g_runtime_TSS;
	vcpu->vmcs.host_RIP = (u64)(u32)emhf_parteventhub_arch_x86vmx_entry;
	//store vcpu at TOS
	vcpu->esp = vcpu->esp - sizeof(u32);
	*(u32 *)vcpu->esp = (u32)vcpu;
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
	vcpu->vmcs.control_IO_BitmapA_address_full = (u32)hva2spa((void*)vcpu->vmx_vaddr_iobitmap);
	vcpu->vmcs.control_IO_BitmapA_address_high = 0;
	vcpu->vmcs.control_IO_BitmapB_address_full = (u32)hva2spa( ((void*)vcpu->vmx_vaddr_iobitmap + PAGE_SIZE_4K) );
	vcpu->vmcs.control_IO_BitmapB_address_high = 0;
	vcpu->vmcs.control_VMX_cpu_based |= (1 << 25); //enable use IO Bitmaps

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
		vcpu->vmcs.control_VM_exit_MSR_load_address_full=(u32)hva2spa((void*)vcpu->vmx_vaddr_msr_area_host);
		vcpu->vmcs.control_VM_exit_MSR_load_address_high=0;
		vcpu->vmcs.control_VM_exit_MSR_load_count= vmx_msr_area_msrs_count;

		//guest MSR load on entry, store on exit
		vcpu->vmcs.control_VM_entry_MSR_load_address_full=(u32)hva2spa((void*)vcpu->vmx_vaddr_msr_area_guest);
		vcpu->vmcs.control_VM_entry_MSR_load_address_high=0;
		vcpu->vmcs.control_VM_entry_MSR_load_count=vmx_msr_area_msrs_count;
		vcpu->vmcs.control_VM_exit_MSR_store_address_full=(u32)hva2spa((void*)vcpu->vmx_vaddr_msr_area_guest);
		vcpu->vmcs.control_VM_exit_MSR_store_address_high=0;
		vcpu->vmcs.control_VM_exit_MSR_store_count=vmx_msr_area_msrs_count;
	}


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
	if(vcpu->isbsp){
		printf("\nBSP(0x%02x): copying boot-module to boot guest", vcpu->id);
		memcpy((void *)__GUESTOSBOOTMODULE_BASE, (void *)rpb->XtGuestOSBootModuleBase, rpb->XtGuestOSBootModuleSize);
			vcpu->vmcs.guest_CS_selector = 0;
			vcpu->vmcs.guest_CS_base = 0;
		vcpu->vmcs.guest_RIP = 0x7c00ULL;
	}else{
		vcpu->vmcs.guest_CS_selector = (vcpu->sipivector * PAGE_SIZE_4K) >> 4;
		vcpu->vmcs.guest_CS_base = (vcpu->sipivector * PAGE_SIZE_4K);
		vcpu->vmcs.guest_RIP = 0x0ULL;
	}

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

	//setup unrestricted guest
	vcpu->vmcs.control_VMX_seccpu_based |= (1 << 7); //enable unrestricted guest

	//setup VMCS link pointer
	vcpu->vmcs.guest_VMCS_link_pointer_full = (u32)0xFFFFFFFFUL;
	vcpu->vmcs.guest_VMCS_link_pointer_high = (u32)0xFFFFFFFFUL;
	
	//setup NMI intercept for core-quiescing
	vcpu->vmcs.control_VMX_pin_based |= (1 << 3);	//intercept NMIs
	
	//trap access to CR0 fixed 1-bits
	vcpu->vmcs.control_CR0_mask = vcpu->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR];
	vcpu->vmcs.control_CR0_mask &= ~(CR0_PE);
	vcpu->vmcs.control_CR0_mask &= ~(CR0_PG);
	vcpu->vmcs.control_CR0_mask |= CR0_CD;
	vcpu->vmcs.control_CR0_mask |= CR0_NW;
	vcpu->vmcs.control_CR0_shadow = vcpu->vmcs.guest_CR0;
			
	//trap access to CR4 fixed bits (this includes the VMXE bit)
	vcpu->vmcs.control_CR4_mask = vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR];  
	vcpu->vmcs.control_CR4_shadow = CR4_VMXE; //let guest know we have VMX enabled

	//flush guest TLB to start with
	emhf_memprot_arch_x86vmx_flushmappings(vcpu);
}


//---initVMCS - intialize VMCS for guest boot-----------------------------------
static void _vmx_initVMCS(VCPU *vcpu){
  if(vcpu->vmx_guest_unrestricted){
  	vmx_initunrestrictedguestVMCS(vcpu);
  }else{
		printf("\nHALT: Fatal, v86 monitor based real-mode exec. unsupported!");
		HALT();
	}
}


//---start a HVM----------------------------------------------------------------
static void _vmx_start_hvm(VCPU *vcpu, u32 vmcs_phys_addr){
  //clear VMCS
  if(!__vmx_vmclear((u64)vmcs_phys_addr)){
    printf("\nCPU(0x%02x): VMCLEAR failed, HALT!", vcpu->id);
    HALT();
  }
  printf("\nCPU(0x%02x): VMCLEAR success.", vcpu->id);
  
  
  //set VMCS revision id
 	*((u32 *)vcpu->vmx_vmcs_vaddr) = (u32)vcpu->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

  //load VMPTR
  if(!__vmx_vmptrld((u64)vmcs_phys_addr)){
    printf("\nCPU(0x%02x): VMPTRLD failed, HALT!", vcpu->id);
    HALT();
  }
  printf("\nCPU(0x%02x): VMPTRLD success.", vcpu->id);
  
  //put VMCS to CPU
  emhf_baseplatform_arch_x86vmx_putVMCS(vcpu);
  printf("\nCPU(0x%02x): VMWRITEs success.", vcpu->id);
  ASSERT( vcpu->vmcs.guest_VMCS_link_pointer_full == 0xFFFFFFFFUL );

  {
    u32 errorcode;
    errorcode=__vmx_start_hvm();
    ASSERT(errorcode != 2);	//this means the VMLAUNCH implementation violated the specs.
    //get CPU VMCS into VCPU structure
    emhf_baseplatform_arch_x86vmx_getVMCS(vcpu);
    
    switch(errorcode){
			case 0:	//no error code, VMCS pointer is invalid
			    printf("\nCPU(0x%02x): VMLAUNCH error; VMCS pointer invalid?. HALT!", vcpu->id);
				break;
			case 1:{//error code available, so dump it
				u32 code=5;
				__vmx_vmread(0x4400, &code);
			    printf("\nCPU(0x%02x): VMLAUNCH error; code=0x%x. HALT!", vcpu->id, code);
			    emhf_baseplatform_arch_x86vmx_dumpVMCS(vcpu);
				break;
			}
	}
    HALT();
  }

  HALT();
}




//initialize partition monitor for a given CPU
void emhf_partition_arch_x86vmx_initializemonitor(VCPU *vcpu){

  //initialize VT
  _vmx_initVT(vcpu);

  //clear VMCS
  memset((void *)&vcpu->vmcs, 0, sizeof(struct _vmx_vmcsfields));

	//INT 15h E820 hook enablement for VMX unrestricted guest mode
	//note: this only happens for the BSP
	if(vcpu->isbsp){
		printf("\nCPU(0x%02x, BSP): initializing INT 15 hook for UG mode...", vcpu->id);
		_vmx_int15_initializehook(vcpu);
	}

}



//setup guest OS state for the partition
void emhf_partition_arch_x86vmx_setupguestOSstate(VCPU *vcpu){
		//initialize VMCS
		_vmx_initVMCS(vcpu);
	
	
}

//start executing the partition and guest OS
void emhf_partition_arch_x86vmx_start(VCPU *vcpu){
    printf("\nCPU(0x%02x): Starting HVM using CS:EIP=0x%04x:0x%08x...", vcpu->id,
			(u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);
    _vmx_start_hvm(vcpu, hva2spa((void*)vcpu->vmx_vmcs_vaddr));
	//we never get here, if we do, we just return and our caller is responsible
	//for halting the core as something really bad happened!
}

//set legacy I/O protection for the partition
void emhf_partition_arch_x86vmx_legacyIO_setprot(VCPU *vcpu, u32 port, u32 size, u32 prottype){
	u8 *bit_vector = (u8 *)vcpu->vmx_vaddr_iobitmap;
	u32 byte_offset, bit_offset;
	u32 i;

	for(i=0; i < size; i++){
		byte_offset = (port+i) / 8;
		bit_offset = (port+i) % 8;
		if(prottype & PART_LEGACYIO_NOACCESS){
			bit_vector[byte_offset] |= (1 << bit_offset);	
		}else{
			prottype = PART_LEGACYIO_READWRITE;
			bit_vector[byte_offset] &= ~((1 << bit_offset));	
		}
	}
}
