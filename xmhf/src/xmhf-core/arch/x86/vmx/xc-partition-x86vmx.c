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
 * XMHF partition component (x86 VMX backend)
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf-core.h>
#include <xc-x86.h>
#include <xc-x86vmx.h>

//---globals referenced by this module------------------------------------------
//TODO: need to remove these direct references
extern u32 x_idt_start[]; //runtimesup.S


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
	u64 vmcs_phys_addr = hva2spa((void*)vcpu->vmx_vmcs_vaddr);
	
	//step-0: to enable VMX on a core, we require it to have a TR loaded,
	//so load it for this core
	//__vmx_loadTR();
	{
	  u32 gdtstart = (u32)xmhf_baseplatform_arch_x86_getgdtbase();
	  u16 trselector = 	__TRSEL;
	  #ifndef __XMHF_VERIFICATION__
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
	  #endif
	}
	


  //step-1: check if intel CPU
  //{
  //  char cpu_oemid[12];
//	  #ifndef __XMHF_VERIFICATION__
//	  asm(	"xor	%%eax, %%eax \n"
//				  "cpuid \n"		
//				  "mov	%%ebx, %0 \n"
//				  "mov	%%edx, %1 \n"
//				  "mov	%%ecx, %2 \n"
//			     :: "m"(cpu_oemid[0]), "m"(cpu_oemid[4]), "m"(cpu_oemid[8]): "eax", "ebx", "ecx", "edx" );
//
//   	if ( strncmp( cpu_oemid, "GenuineIntel", 12 ) ){
//   	  printf("\nCPU(0x%02x) is not an Intel CPU. Halting!", vcpu->id);
//   	  HALT();
//   	}
//   	#endif
//  }

	{
			u32 cpu_vendor=get_cpu_vendor_or_die();
			if(cpu_vendor != CPU_VENDOR_INTEL){
				printf("\nCPU(0x%02x) is not an Intel CPU. Halting!", vcpu->id);
		        HALT();
			}

	}

  
  //step-2: check VT support
  {
  	u32	cpu_features;
    #ifndef __XMHF_VERIFICATION__
    asm("mov	$1, %%eax \n"
				"cpuid \n"
				"mov	%%ecx, %0	\n"
				::"m"(cpu_features): "eax", "ebx", "ecx", "edx" );
		if ( ( cpu_features & (1<<5) ) == 0 ){
			printf("CPU(0x%02x) does not support VT. Halting!", vcpu->id);
      HALT();
		}
	#endif
  }

  //step-3: save contents of VMX MSRs as well as MSR EFER and EFCR 
  //into vcpu
  {
    u32 i;
    u32 eax, edx;
    #ifndef __XMHF_VERIFICATION__
    for(i=0; i < IA32_VMX_MSRCOUNT; i++){
	#else
	for(i=0; i < 1; i++){
	#endif
        #ifndef __XMHF_VERIFICATION__
        rdmsr( (IA32_VMX_BASIC_MSR + i), &eax, &edx);
        #endif
        vcpu->vmx_msrs[i] = (u64)edx << 32 | (u64) eax;        
    }

    #ifndef __XMHF_VERIFICATION__
	rdmsr(MSR_EFER, &eax, &edx);
    #endif
    vcpu->vmx_msr_efer = (u64)edx << 32 | (u64) eax;
    #ifndef __XMHF_VERIFICATION__
    rdmsr(MSR_EFCR, &eax, &edx);
	#endif
    vcpu->vmx_msr_efcr = (u64)edx << 32 | (u64) eax;
  
    //[debug: dump contents of MSRs]
    //for(i=0; i < IA32_VMX_MSRCOUNT; i++)
    //  printf("\nCPU(0x%02x): VMX MSR 0x%08x = 0x%08x%08x", vcpu->id, IA32_VMX_BASIC_MSR+i, 
    //      (u32)((u64)vcpu->vmx_msrs[i] >> 32), (u32)vcpu->vmx_msrs[i]);
    
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
	#ifndef __XMHF_VERIFICATION__
	asm(	" mov  %%cr4, %%eax	\n"\
		" bts  $13, %%eax	\n"\
		" mov  %%eax, %%cr4	" ::: "eax" );
	#endif
  printf("\nCPU(0x%02x): enabled VMX", vcpu->id);

	  //step-5:enter VMX root operation using VMXON
	  {
	  	u32 retval=0;
	  	u64 vmxonregion_paddr = hva2spa((void*)vcpu->vmx_vmxonregion_vaddr);
	    //set VMCS rev id
	  	#ifndef __XMHF_VERIFICATION__
	  	*((u32 *)vcpu->vmx_vmxonregion_vaddr) = (u32)vcpu->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];
	    #endif
	    
	    #ifndef __XMHF_VERIFICATION__
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
		#endif
		
	    if(!retval){
	      printf("\nCPU(0x%02x): Fatal, unable to enter VMX root operation", vcpu->id);
	      HALT();
	    }  
	  
	    printf("\nCPU(0x%02x): Entered VMX root operation", vcpu->id);
	  }


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

	
}

//---vmx int 15 hook enabling function------------------------------------------
static void	_vmx_int15_initializehook(VCPU *vcpu){
	//we should only be called from the BSP
	HALT_ON_ERRORCOND(vcpu->isbsp);

	#ifndef __XMHF_VERIFICATION__
	{
		u8 *bdamemory = (u8 *)0x4AC;				//use BDA reserved memory at 0040:00AC
		
		u16 *ivt_int15 = (u16 *)(0x54);			//32-bit CS:IP for IVT INT 15 handler
		
		printf("\nCPU(0x%02x): original INT 15h handler at 0x%04x:0x%04x", vcpu->id,
			ivt_int15[1], ivt_int15[0]);

		//we need 8 bytes (4 for the VMCALL followed by IRET and 4 for he original 
		//IVT INT 15h handler address, zero them to start off
		memset(bdamemory, 0x0, 8);		

		//implant VMCALL followed by IRET at 0040:04AC
		bdamemory[0]= 0x0f;	//VMCALL						
		bdamemory[1]= 0x01;
		bdamemory[2]= 0xc1;																	
		bdamemory[3]= 0xcf;	//IRET
		
		//store original INT 15h handler CS:IP following VMCALL and IRET
		*((u16 *)(&bdamemory[4])) = ivt_int15[0];	//original INT 15h IP
		*((u16 *)(&bdamemory[6])) = ivt_int15[1];	//original INT 15h CS


		//point IVT INT15 handler to the VMCALL instruction
		ivt_int15[0]=0x00AC;
		ivt_int15[1]=0x0040;					
	}
	#endif //__XMHF_VERIFICATION__
}


//--initunrestrictedguestVMCS: initializes VMCS for unrestricted guest ---------
void vmx_initunrestrictedguestVMCS(VCPU *vcpu){
	u32 lodword, hidword;

	//setup host state
	//vcpu->vmcs.host_CR0 = read_cr0();
	//vcpu->vmcs.host_CR4 = read_cr4();
	//vcpu->vmcs.host_CR3 = read_cr3();
	//vcpu->vmcs.host_CS_selector = read_segreg_cs();
	//vcpu->vmcs.host_DS_selector = read_segreg_ds();
	//vcpu->vmcs.host_ES_selector = read_segreg_es();
	//vcpu->vmcs.host_FS_selector = read_segreg_fs();
	//vcpu->vmcs.host_GS_selector = read_segreg_gs();
	//vcpu->vmcs.host_SS_selector = read_segreg_ss();
	//vcpu->vmcs.host_TR_selector = read_tr_sel();
	//vcpu->vmcs.host_GDTR_base = (u64)xmhf_baseplatform_arch_x86_getgdtbase();
	//vcpu->vmcs.host_IDTR_base = (u64)xmhf_baseplatform_arch_x86_getidtbase();
	//vcpu->vmcs.host_TR_base = (u64)xmhf_baseplatform_arch_x86_gettssbase();
	//vcpu->vmcs.host_RIP = (u64)(u32)xmhf_parteventhub_arch_x86vmx_entry;

	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CR0, read_cr0());
	__vmx_vmwrite(VMCS_HOST_CR0, read_cr0());
	__vmx_vmread(VMCS_HOST_CR0, &lodword);
	printf("\nVMCS_HOST_CR0=%x, read_cr0=%x, lod=%x", xmhfhw_cpu_x86vmx_vmread(VMCS_HOST_CR0), read_cr0(), lodword);
	HALT_ON_ERRORCOND(xmhfhw_cpu_x86vmx_vmread(VMCS_HOST_CR0) == read_cr0());
	
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CR4, read_cr4());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CR3, read_cr3());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CS_SELECTOR, read_segreg_cs());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_DS_SELECTOR, read_segreg_ds());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_ES_SELECTOR, read_segreg_es());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_FS_SELECTOR, read_segreg_fs());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_GS_SELECTOR, read_segreg_gs());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SS_SELECTOR, read_segreg_ss());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_TR_SELECTOR, read_tr_sel());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_GDTR_BASE, xmhf_baseplatform_arch_x86_getgdtbase());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_IDTR_BASE, xmhf_baseplatform_arch_x86_getidtbase());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_TR_BASE, xmhf_baseplatform_arch_x86_gettssbase());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_RIP, (u32)xmhf_parteventhub_arch_x86vmx_entry);
	


/*#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
	if( vcpu->vmcs.host_RIP == (u64)(u32)xmhf_parteventhub_arch_x86vmx_entry)
		vcpu->vmcs.host_RIP = 0xDEADBEEF;
#endif //__XMHF_VERIFICATION__
*/

	//store vcpu at TOS
	vcpu->esp = vcpu->esp - sizeof(u32);
#ifndef __XMHF_VERIFICATION__
	*(u32 *)vcpu->esp = (u32)vcpu;
#endif
	//vcpu->vmcs.host_RSP = (u64)vcpu->esp;
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_RSP, vcpu->esp);
			

#ifndef __XMHF_VERIFICATION__			
	rdmsr(IA32_SYSENTER_CS_MSR, &lodword, &hidword);
	//vcpu->vmcs.host_SYSENTER_CS = lodword;
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_CS, lodword);
	rdmsr(IA32_SYSENTER_ESP_MSR, &lodword, &hidword);
	//vcpu->vmcs.host_SYSENTER_ESP = (u64) (((u64)hidword << 32) | (u64)lodword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_ESP, (u32)(((u64)hidword << 32) | (u64)lodword));
	rdmsr(IA32_SYSENTER_EIP_MSR, &lodword, &hidword);
	//vcpu->vmcs.host_SYSENTER_EIP = (u64) (((u64)hidword << 32) | (u64)lodword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_EIP, (u32)(((u64)hidword << 32) | (u64)lodword));
	rdmsr(IA32_MSR_FS_BASE, &lodword, &hidword);
	//vcpu->vmcs.host_FS_base = (u64) (((u64)hidword << 32) | (u64)lodword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_FS_BASE, (u32) (((u64)hidword << 32) | (u64)lodword) );
	rdmsr(IA32_MSR_GS_BASE, &lodword, &hidword);
	//vcpu->vmcs.host_GS_base = (u64) (((u64)hidword << 32) | (u64)lodword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_GS_BASE, (u32) (((u64)hidword << 32) | (u64)lodword) );
#endif

	//setup default VMX controls
	//vcpu->vmcs.control_VMX_pin_based = vcpu->vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR];
	//vcpu->vmcs.control_VMX_cpu_based = vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR];
	//vcpu->vmcs.control_VM_exit_controls = vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR];
	//vcpu->vmcs.control_VM_entry_controls = vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR];
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_PIN_BASED, vcpu->vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_CONTROLS, vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR]);

	//IO bitmap support
	//vcpu->vmcs.control_IO_BitmapA_address_full = (u32)hva2spa((void*)vcpu->vmx_vaddr_iobitmap);
	//vcpu->vmcs.control_IO_BitmapA_address_high = 0;
	//vcpu->vmcs.control_IO_BitmapB_address_full = (u32)hva2spa( ((void*)vcpu->vmx_vaddr_iobitmap + PAGE_SIZE_4K) );
	//vcpu->vmcs.control_IO_BitmapB_address_high = 0;
	//vcpu->vmcs.control_VMX_cpu_based |= (1 << 25); //enable use IO Bitmaps
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL, (u32)hva2spa((void*)vcpu->vmx_vaddr_iobitmap));
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPA_ADDRESS_HIGH, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL, (u32)hva2spa( ((void*)vcpu->vmx_vaddr_iobitmap + PAGE_SIZE_4K) ));
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPB_ADDRESS_HIGH, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (1 << 25)) );

	//Critical MSR load/store
	{
		u32 i;
		msr_entry_t *hmsr = (msr_entry_t *)vcpu->vmx_vaddr_msr_area_host;
		msr_entry_t *gmsr = (msr_entry_t *)vcpu->vmx_vaddr_msr_area_guest;

		#ifndef __XMHF_VERIFICATION__
		//store initial values of the MSRs
		for(i=0; i < vmx_msr_area_msrs_count; i++){
			u32 msr, eax, edx;
			msr = vmx_msr_area_msrs[i];						
			rdmsr(msr, &eax, &edx);
			hmsr[i].index = gmsr[i].index = msr;
			hmsr[i].data = gmsr[i].data = ((u64)edx << 32) | (u64)eax;
		}
		#endif

		//host MSR load on exit, we store it ourselves before entry
		//vcpu->vmcs.control_VM_exit_MSR_load_address_full=(u32)hva2spa((void*)vcpu->vmx_vaddr_msr_area_host);
		//vcpu->vmcs.control_VM_exit_MSR_load_address_high=0;
		//vcpu->vmcs.control_VM_exit_MSR_load_count= vmx_msr_area_msrs_count;
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL, (u32)hva2spa((void*)vcpu->vmx_vaddr_msr_area_host));
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_HIGH, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);

		//guest MSR load on entry, store on exit
		//vcpu->vmcs.control_VM_entry_MSR_load_address_full=(u32)hva2spa((void*)vcpu->vmx_vaddr_msr_area_guest);
		//vcpu->vmcs.control_VM_entry_MSR_load_address_high=0;
		//vcpu->vmcs.control_VM_entry_MSR_load_count=vmx_msr_area_msrs_count;
		//vcpu->vmcs.control_VM_exit_MSR_store_address_full=(u32)hva2spa((void*)vcpu->vmx_vaddr_msr_area_guest);
		//vcpu->vmcs.control_VM_exit_MSR_store_address_high=0;
		//vcpu->vmcs.control_VM_exit_MSR_store_count=vmx_msr_area_msrs_count;
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, (u32)hva2spa((void*)vcpu->vmx_vaddr_msr_area_guest));
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_HIGH, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, (u32)hva2spa((void*)vcpu->vmx_vaddr_msr_area_guest));
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_HIGH, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, vmx_msr_area_msrs_count);
		
	
		//[debug] dump host and guest MSR regions
		//{
		//	u32 i;
		//	msr_entry_t *hmsr = (msr_entry_t *)vcpu->vmx_vaddr_msr_area_host;
		//	msr_entry_t *gmsr = (msr_entry_t *)vcpu->vmx_vaddr_msr_area_guest;
		//			printf("\n%s: host MSR dump follows", __FUNCTION__);
		//	for(i=0; i < vmx_msr_area_msrs_count; i++)
		//		printf("\n   %02u: MSR=%08x, value=%016llx", i, hmsr[i].index, hmsr[i].data);
		//
		//	printf("\n%s: guest MSR dump follows", __FUNCTION__);
		//	for(i=0; i < vmx_msr_area_msrs_count; i++)
		//		printf("\n   %02u: MSR=%08x, value=%016llx", i, gmsr[i].index, gmsr[i].data);
		//	
		//}
	
	}


	//vcpu->vmcs.control_pagefault_errorcode_mask  = 0x00000000;	//dont be concerned with 
	//vcpu->vmcs.control_pagefault_errorcode_match = 0x00000000; //guest page-faults
	//vcpu->vmcs.control_exception_bitmap = 0;
	//vcpu->vmcs.control_CR3_target_count = 0;
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_PAGEFAULT_ERRORCODE_MASK, 0x00000000);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_PAGEFAULT_ERRORCODE_MATCH, 0x00000000);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EXCEPTION_BITMAP, 0);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR3_TARGET_COUNT, 0);  
      
	//setup guest state
	//CR0, real-mode, PE and PG bits cleared
	//vcpu->vmcs.guest_CR0 = vcpu->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR];
	//vcpu->vmcs.guest_CR0 &= ~(CR0_PE);
	//vcpu->vmcs.guest_CR0 &= ~(CR0_PG);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR0, (vcpu->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR] & ~(CR0_PE) & ~(CR0_PG)) );
	//CR4, required bits set (usually VMX enabled bit)
	//vcpu->vmcs.guest_CR4 = vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR];
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR4, vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
	//CR3 set to 0, does not matter
	//vcpu->vmcs.guest_CR3 = 0;
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, 0);
	//IDTR
	//vcpu->vmcs.guest_IDTR_base = 0;
	//vcpu->vmcs.guest_IDTR_limit = 0x3ff;	//16-bit IVT
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_IDTR_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_IDTR_LIMIT, 0x3ff);
	//GDTR
	//vcpu->vmcs.guest_GDTR_base = 0;
	//vcpu->vmcs.guest_GDTR_limit = 0;	//no GDT
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_LIMIT, 0);
	//LDTR, unusable
	//vcpu->vmcs.guest_LDTR_base = 0;
	//vcpu->vmcs.guest_LDTR_limit = 0;
	//vcpu->vmcs.guest_LDTR_selector = 0;
	//vcpu->vmcs.guest_LDTR_access_rights = 0x10000;
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_LIMIT, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_SELECTOR, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_ACCESS_RIGHTS, 0x10000);
	//TR, should be usable for VMX to work, but not used by guest
	//vcpu->vmcs.guest_TR_base = 0;
	//vcpu->vmcs.guest_TR_limit = 0;
	//vcpu->vmcs.guest_TR_selector = 0;
	//vcpu->vmcs.guest_TR_access_rights = 0x83; //present, 16-bit busy TSS
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_LIMIT, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_SELECTOR, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_ACCESS_RIGHTS, 0x83);
	//RSP
	//vcpu->vmcs.guest_RSP = 0x0;
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RSP, 0);
	
	//RIP and activity state
	if(vcpu->isbsp){
		printf("\nBSP(0x%02x): copying boot-module to boot guest", vcpu->id);
		#ifndef __XMHF_VERIFICATION__
		memcpy((void *)__GUESTOSBOOTMODULE_BASE, (void *)xcbootinfo->richguest_bootmodule_base, xcbootinfo->richguest_bootmodule_size);
		#endif
		//vcpu->vmcs.guest_CS_selector = 0;
		//vcpu->vmcs.guest_CS_base = 0;
		//vcpu->vmcs.guest_RIP = 0x7c00ULL;
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_SELECTOR, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_BASE, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RIP, 0x7c00);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ACTIVITY_STATE, 0);	//normal activity state
	}else{
		//vcpu->vmcs.guest_CS_selector = 0;
		//vcpu->vmcs.guest_CS_base = 0;
		//vcpu->vmcs.guest_RIP = 0;
		//vcpu->vmcs.guest_activity_state=3;	//Wait-for-SIPI
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_SELECTOR, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_BASE, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RIP, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ACTIVITY_STATE, 3);	//wait-for-SIPI
	}

	//vcpu->vmcs.guest_CS_limit = 0xFFFF;	//64K
	//vcpu->vmcs.guest_CS_access_rights = 0x93; //present, system, read-write accessed
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_LIMIT, 0xFFFF);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_ACCESS_RIGHTS, 0x93);

	//RFLAGS
	//vcpu->vmcs.guest_RFLAGS = 0; 
	//vcpu->vmcs.guest_RFLAGS &= ~((1<<3)|(1<<5)|(1<<15));	// reserved 0-bits
	//vcpu->vmcs.guest_RFLAGS |= (1<<1);				// reserved 1-bits
	//vcpu->vmcs.guest_RFLAGS |= (1<<9);				// IF = enable 
	//vcpu->vmcs.guest_RFLAGS &= ~(1<<14);			// Nested Task = disable
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RFLAGS, ((((0 & ~((1<<3)|(1<<5)|(1<<15)) ) | (1 <<1)) | (1<<9)) & ~(1<<14)) );
	//CS, DS, ES, FS, GS and SS segments
	//vcpu->vmcs.guest_DS_selector = 0;
	//vcpu->vmcs.guest_DS_base = 0;
	//vcpu->vmcs.guest_DS_limit = 0xFFFF;	//64K
	//vcpu->vmcs.guest_DS_access_rights = 0x93; //present, system, read-write accessed
	//vcpu->vmcs.guest_ES_selector = 0;
	//vcpu->vmcs.guest_ES_base = 0;
	//vcpu->vmcs.guest_ES_limit = 0xFFFF;	//64K
	//vcpu->vmcs.guest_ES_access_rights = 0x93; //present, system, read-write accessed
	//vcpu->vmcs.guest_FS_selector = 0;
	//vcpu->vmcs.guest_FS_base = 0;
	//vcpu->vmcs.guest_FS_limit = 0xFFFF;	//64K
	//vcpu->vmcs.guest_FS_access_rights = 0x93; //present, system, read-write accessed
	//vcpu->vmcs.guest_GS_selector = 0;
	//vcpu->vmcs.guest_GS_base = 0;
	//vcpu->vmcs.guest_GS_limit = 0xFFFF;	//64K
	//vcpu->vmcs.guest_GS_access_rights = 0x93; //present, system, read-write accessed
	//vcpu->vmcs.guest_SS_selector = 0x0;
	//vcpu->vmcs.guest_SS_base = 0x0;
	//vcpu->vmcs.guest_SS_limit = 0xFFFF;	//64K
	//vcpu->vmcs.guest_SS_access_rights = 0x93; //present, system, read-write accessed
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_SELECTOR, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_LIMIT, 0xFFFF);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_ACCESS_RIGHTS, 0x93);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_SELECTOR, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_LIMIT, 0xFFFF);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_ACCESS_RIGHTS, 0x93);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_SELECTOR, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_LIMIT, 0xFFFF);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_ACCESS_RIGHTS, 0x93);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_SELECTOR, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_LIMIT, 0xFFFF);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_ACCESS_RIGHTS, 0x93);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_SELECTOR, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_LIMIT, 0xFFFF);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_ACCESS_RIGHTS, 0x93);
					

	//activate secondary processor controls
	//vcpu->vmcs.control_VMX_seccpu_based = vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR];
	//vcpu->vmcs.control_VMX_cpu_based |= (1 << 31); //activate secondary processor controls
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (1 << 31)) );

	//setup unrestricted guest
	//vcpu->vmcs.control_VMX_seccpu_based |= (1 << 7); //enable unrestricted guest
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (1 << 7)) );

	//setup VMCS link pointer
	//vcpu->vmcs.guest_VMCS_link_pointer_full = (u32)0xFFFFFFFFUL;
	//vcpu->vmcs.guest_VMCS_link_pointer_high = (u32)0xFFFFFFFFUL;
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_VMCS_LINK_POINTER_FULL, (u32)0xFFFFFFFFUL);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_VMCS_LINK_POINTER_HIGH, (u32)0xFFFFFFFFUL);
	
	//setup NMI intercept for core-quiescing
	//vcpu->vmcs.control_VMX_pin_based |= (1 << 3);	//intercept NMIs
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_PIN_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_PIN_BASED) | (1 << 3) ) );
	
	//trap access to CR0 fixed 1-bits
	//vcpu->vmcs.control_CR0_mask = vcpu->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR];
	//vcpu->vmcs.control_CR0_mask &= ~(CR0_PE);
	//vcpu->vmcs.control_CR0_mask &= ~(CR0_PG);
	//vcpu->vmcs.control_CR0_mask |= CR0_CD;
	//vcpu->vmcs.control_CR0_mask |= CR0_NW;
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR0_MASK, ((((vcpu->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR] & ~(CR0_PE)) & ~(CR0_PG)) | CR0_CD) | CR0_NW) );
	//vcpu->vmcs.control_CR0_shadow = vcpu->vmcs.guest_CR0;
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR0_SHADOW, xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0));
			
	//trap access to CR4 fixed bits (this includes the VMXE bit)
	//vcpu->vmcs.control_CR4_mask = vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR];  
	//vcpu->vmcs.control_CR4_shadow = CR4_VMXE; //let guest know we have VMX enabled
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR4_MASK, vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR4_SHADOW, CR4_VMXE);

	//flush guest TLB to start with
	xmhf_memprot_arch_x86vmx_flushmappings(vcpu);
}



//---initVMCS - intialize VMCS for guest boot-----------------------------------
static void _vmx_initVMCS(VCPU *vcpu){
 	vmx_initunrestrictedguestVMCS(vcpu);
}


//---start a HVM----------------------------------------------------------------
static void _vmx_start_hvm(VCPU *vcpu, u32 vmcs_phys_addr){
/*  //clear VMCS
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
*/  
  //put VMCS to CPU
  //xmhf_baseplatform_arch_x86vmx_putVMCS(vcpu);
  //printf("\nCPU(0x%02x): VMWRITEs success.", vcpu->id);
  HALT_ON_ERRORCOND( xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_VMCS_LINK_POINTER_FULL) == 0xFFFFFFFFUL );

  {
    u32 errorcode;
    errorcode=__vmx_start_hvm();
    HALT_ON_ERRORCOND(errorcode != 2);	//this means the VMLAUNCH implementation violated the specs.
    //get CPU VMCS into VCPU structure
    //xmhf_baseplatform_arch_x86vmx_getVMCS(vcpu);
    
    switch(errorcode){
			case 0:	//no error code, VMCS pointer is invalid
			    printf("\nCPU(0x%02x): VMLAUNCH error; VMCS pointer invalid?. HALT!", vcpu->id);
				break;
			case 1:{//error code available, so dump it
				u32 code=xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMINSTR_ERROR);
				printf("\nCPU(0x%02x): VMLAUNCH error; code=0x%x. HALT!", vcpu->id, code);
			    xmhf_baseplatform_arch_x86vmx_dumpVMCS(vcpu);
				break;
			}
	}
    HALT();
  }

  HALT();
}

//static void _plant_spinloop_in_bda(void){
//	u8 *spinloopmemory = (u8 *)(0x7C00 - 0x2);				//use two bytes just before boot module address at 0x0000: 0x7C00
//	
//	spinloopmemory[0]=0xEB;
//	spinloopmemory[1]=0xFE;		//plant a jmp eip to spin forever
//}


//initialize partition monitor for a given CPU
static void xmhf_partition_arch_x86vmx_initializemonitor(VCPU *vcpu){
    	u32 bcr0;

	    //set bit 5 (EM) of CR0 to be VMX compatible in case of Intel cores
		bcr0 = read_cr0();
		bcr0 |= 0x20;
		write_cr0(bcr0);


  //initialize VT
  _vmx_initVT(vcpu);


	/*#ifndef __XMHF_VERIFICATION__
   //clear VMCS
  memset((void *)&vcpu->vmcs, 0, sizeof(struct _vmx_vmcsfields));
   #endif
   */
	//INT 15h E820 hook enablement for VMX unrestricted guest mode
	//note: this only happens for the BSP
	if(vcpu->isbsp){
		printf("\nCPU(0x%02x, BSP): initializing INT 15 hook for UG mode...", vcpu->id);
		_vmx_int15_initializehook(vcpu);

		//_plant_spinloop_in_bda();
		//printf("\nCPU(0x%02x, BSP): planted spinloop for APs...", vcpu->id);
		
	}

}



//setup guest OS state for the partition
void xmhf_partition_arch_x86vmx_setupguestOSstate(VCPU *vcpu){
		//initialize VMCS
		_vmx_initVMCS(vcpu);
	
}

//start executing the partition and guest OS
static void xmhf_partition_arch_x86vmx_start(VCPU *vcpu){
    
#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
	//ensure that whenever a partition is started on a vcpu, we have extended paging
	//enabled and that the base points to the extended page tables we have initialized
	assert( (vcpu->vmcs.control_EPT_pointer_high == 0) && (vcpu->vmcs.control_EPT_pointer_full == (hva2spa((void*)vcpu->vmx_vaddr_ept_pml4_table) | 0x1E)) );
	assert( (vcpu->vmcs.control_VMX_seccpu_based & 0x2) );
	assert( vcpu->vmcs.host_RIP == 0xDEADBEEF);
#endif

#ifndef __XMHF_VERIFICATION__
    _vmx_start_hvm(vcpu, hva2spa((void*)vcpu->vmx_vmcs_vaddr));
	//we never get here, if we do, we just return and our caller is responsible
	//for halting the core as something really bad happened!
#endif	

}

//set legacy I/O protection for the partition
void xmhf_partition_arch_x86vmx_legacyIO_setprot(VCPU *vcpu, u32 port, u32 size, u32 prottype){

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

//initialize partition monitor for a given CPU
//void xmhf_partition_arch_initializemonitor(VCPU *vcpu){
//void xmhf_partition_arch_initializemonitor(context_desc_t context_desc){
void xmhf_partition_arch_initializemonitor(u32 index_cpudata){
	VCPU *vcpu=&g_bplt_vcpu[index_cpudata];
	
		xmhf_partition_arch_x86vmx_initializemonitor(vcpu);
}

//setup guest OS state for the partition
//void xmhf_partition_arch_setupguestOSstate(VCPU *vcpu){
//void xmhf_partition_arch_setupguestOSstate(context_desc_t context_desc){
void xmhf_partition_arch_setupguestOSstate(u32 index_cpudata){
	VCPU *vcpu=(VCPU *)&g_bplt_vcpu[index_cpudata];
		xmhf_partition_arch_x86vmx_setupguestOSstate(vcpu);
}

//start executing the partition and guest OS
//void xmhf_partition_arch_start(VCPU *vcpu){
//void xmhf_partition_arch_start(context_desc_t context_desc){
void xmhf_partition_arch_start(u32 index_cpudata){
	VCPU *vcpu=(VCPU *)&g_bplt_vcpu[index_cpudata];
		xmhf_partition_arch_x86vmx_start(vcpu);
}

//set legacy I/O protection for the partition
void xmhf_partition_arch_legacyIO_setprot(context_desc_t context_desc, u32 port, u32 size, u32 prottype){
	VCPU *vcpu=(VCPU *)&g_bplt_vcpu[context_desc.cpu_desc.id];
		xmhf_partition_arch_x86vmx_legacyIO_setprot(vcpu, port, size, prottype);
}

//----------------------------------------------------------------------
// start HVM on a given physical core
// on success: this function will not return
// on failure: 1 if a valid error code is present, 0 if no error code, 
// 2 if invalid error info. (should never happen)
//----------------------------------------------------------------------
u32 __vmx_start_hvm(void) __attribute__ ((naked)) {
	//save GPRs
	asm volatile ("pushal\r\n");
   
	//real-mode setup just like the BIOS
	asm volatile ("movl $0x0, %eax\r\n");
	asm volatile ("movl $0x0, %ebx\r\n");
	asm volatile ("movl $0x0, %ecx\r\n");
	asm volatile ("movl $0x80, %edx\r\n");
	asm volatile ("movl $0x0, %ebp\r\n");
	asm volatile ("movl $0x0, %esi\r\n");
	asm volatile ("movl $0x0, %edi\r\n");

	//attempt to instantiate the HVM
	asm volatile ("vmlaunch\r\n");
	 
	//if we get here then some error happened during the launch
	
	//restore stack frame for a return from this procedure
	asm volatile ("popal\r\n");	

	//there are two possible causes of failure, VMFailInvalid or
	//VMFailValid (VM instruction error field contains the error code)
	//check which happened and return appropriate value in eax 
	asm volatile ("jc __vmx_start_hvm_failinvalid\r\n"
				  "jnz	__vmx_start_hvm_undefinedimplementation	\r\n"
				  "movl $0x1, %eax\r\n"
				  "ret\r\n"					//return 1 as we have error code
				  "__vmx_start_hvm_undefinedimplementation:\r\n"
				  "movl $0x2, %eax\r\n"		//violation of VMLAUNCH specs., handle it anyways
				  "ret\r\n"
				  "__vmx_start_hvm_failinvalid:\r\n"
				  "xorl %eax, %eax\r\n"		//return 0 as we have no error code available
				  "ret\r\n"
	);

}
