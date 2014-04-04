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
 * XMHF core base platform component (x86 vmx arch. backend)
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf-core.h>

//initialize CPU state
void xmhf_baseplatform_arch_x86vmx_cpuinitialize(void){
    	u32 bcr0;
	    txt_heap_t  __attribute__((unused)) *txt_heap;
        os_mle_data_t __attribute__((unused)) *os_mle_data ;
  
	    //set bit 5 (EM) of CR0 to be VMX compatible in case of Intel cores
		bcr0 = read_cr0();
		bcr0 |= 0x20;
		write_cr0(bcr0);

#if defined (__DRT__)
        // restore pre-SENTER MTRRs that were overwritten for SINIT launch 
        // NOTE: XXX TODO; BSP MTRRs ALREADY RESTORED IN SL; IS IT
        //   DANGEROUS TO DO THIS TWICE? 
        // sl.c unity-maps 0xfed00000 for 2M so these should work fine 
	#ifndef __XMHF_VERIFICATION__
        txt_heap = get_txt_heap();
        printf("\ntxt_heap = 0x%08x", (u32)txt_heap);
        os_mle_data = get_os_mle_data_start(txt_heap);
        printf("\nos_mle_data = 0x%08x", (u32)os_mle_data);
    
        if(!validate_mtrrs(&(os_mle_data->saved_mtrr_state))) {
             printf("\nSECURITY FAILURE: validate_mtrrs() failed.\n");
             HALT();
        }
        restore_mtrrs(&(os_mle_data->saved_mtrr_state));
        #endif
#endif	//__DRT__
      
}

u32 xmhf_baseplatform_arch_getcpuvendor(void){
	return xmhf_baseplatform_arch_x86_getcpuvendor();
}

//initialize basic platform elements
void xmhf_baseplatform_arch_initialize(void){
	//initialize PCI subsystem
	xmhf_baseplatform_arch_x86_pci_initialize();
	
	//check ACPI subsystem
	{
		ACPI_RSDP rsdp;
		#ifndef __XMHF_VERIFICATION__
			//TODO: plug in a BIOS data area map/model
			if(!xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp)){
				printf("\n%s: ACPI RSDP not found, Halting!", __FUNCTION__);
				HALT();
			}
		#endif //__XMHF_VERIFICATION__
	}

	//initialize TR/TSS
	#ifndef __XMHF_VERIFICATION__
	xmhf_baseplatform_arch_x86_initializeTR();
	#endif //__XMHF_VERIFICATION__

}

void xmhf_baseplatform_arch_cpuinitialize(void){
	xmhf_baseplatform_arch_x86_cpuinitialize();

	//if(cpu_vendor == CPU_VENDOR_INTEL)
		xmhf_baseplatform_arch_x86vmx_cpuinitialize();
}

//----------------------------------------------------------------------
//bplt-x86vmx-reboot

/*//VMX specific platform reboot
void xmhf_baseplatform_arch_x86vmx_reboot(VCPU *vcpu){
	(void)vcpu;

	//shut VMX off, else CPU ignores INIT signal!
	__asm__ __volatile__("vmxoff \r\n");
	write_cr4(read_cr4() & ~(CR4_VMXE));
	
	//fall back on generic x86 reboot
	xmhf_baseplatform_arch_x86_reboot();
}*/

//reboot platform
void xmhf_baseplatform_arch_reboot(context_desc_t context_desc){
	//HALT_ON_ERRORCOND (vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	
	//shut VMX off, else CPU ignores INIT signal!
	__asm__ __volatile__("vmxoff \r\n");
	write_cr4(read_cr4() & ~(CR4_VMXE));
	
	//fall back on generic x86 reboot
	xmhf_baseplatform_arch_x86_reboot();
}


//----------------------------------------------------------------------
//bplt-x86vmx-smp

//allocate and setup VCPU structure for all the CPUs
//note: isbsp is set by xmhf_baseplatform_arch_x86_smpinitialize_commonstart
//in arch/x86/common/bplt-x86-smp.c
void xmhf_baseplatform_arch_x86vmx_allocandsetupvcpus(u32 cpu_vendor){
  u32 i;
  VCPU *vcpu;

#ifndef __XMHF_VERIFICATION__	

	for(i=0; i < g_midtable_numentries; i++){
		//allocate VCPU structure
		//vcpu = (VCPU *)((u32)g_vcpubuffers + (u32)(i * SIZE_STRUCT_VCPU));
		vcpu = (VCPU *)&g_bplt_vcpu[i];

		memset((void *)vcpu, 0, sizeof(VCPU));

		vcpu->cpu_vendor = cpu_vendor;

		//allocate runtime stack
		vcpu->esp = ((u32)g_cpustacks + (i * RUNTIME_STACK_SIZE)) + RUNTIME_STACK_SIZE;    

		//allocate VMXON memory region
		vcpu->vmx_vmxonregion_vaddr = ((u32)g_vmx_vmxon_buffers + (i * PAGE_SIZE_4K)) ;

		//allocate VMCS memory region
		vcpu->vmx_vmcs_vaddr = ((u32)g_vmx_vmcs_buffers + (i * PAGE_SIZE_4K)) ;

		//allocate VMX IO bitmap region
		vcpu->vmx_vaddr_iobitmap = (u32)g_vmx_iobitmap_buffer; 

		//allocate VMX guest and host MSR save areas
		vcpu->vmx_vaddr_msr_area_host = ((u32)g_vmx_msr_area_host_buffers + (i * (2*PAGE_SIZE_4K))) ; 
		vcpu->vmx_vaddr_msr_area_guest = ((u32)g_vmx_msr_area_guest_buffers + (i * (2*PAGE_SIZE_4K))) ; 

		//allocate VMX MSR bitmap region
		vcpu->vmx_vaddr_msrbitmaps = ((u32)g_vmx_msrbitmap_buffers + (i * PAGE_SIZE_4K)) ; 

		//allocate EPT paging structures
		#ifdef __NESTED_PAGING__		
		{
				//vcpu->vmx_vaddr_ept_pml4_table = ((u32)g_vmx_ept_pml4_table_buffers + (i * PAGE_SIZE_4K));
				//vcpu->vmx_vaddr_ept_pdp_table = ((u32)g_vmx_ept_pdp_table_buffers + (i * PAGE_SIZE_4K));  
				//vcpu->vmx_vaddr_ept_pd_tables = ((u32)g_vmx_ept_pd_table_buffers + (i * (PAGE_SIZE_4K*4))); 		
				//vcpu->vmx_vaddr_ept_p_tables = ((u32)g_vmx_ept_p_table_buffers + (i * (PAGE_SIZE_4K*2048))); 
				vcpu->vmx_vaddr_ept_pml4_table = ((u32)g_vmx_ept_pml4_table_buffers);
				vcpu->vmx_vaddr_ept_pdp_table = ((u32)g_vmx_ept_pdp_table_buffers);  
				vcpu->vmx_vaddr_ept_pd_tables = ((u32)g_vmx_ept_pd_table_buffers); 		
				vcpu->vmx_vaddr_ept_p_tables = ((u32)g_vmx_ept_p_table_buffers); 
		}
		#endif

		//other VCPU data such as LAPIC id, SIPI vector and receive indication
		vcpu->id = g_midtable[i].cpu_lapic_id;
		vcpu->idx = i;
		vcpu->sipivector = 0;
		vcpu->sipireceived = 0;

		//map LAPIC to VCPU in midtable
		g_midtable[i].vcpu_vaddr_ptr = (u32)vcpu;	
	}

#else //__XMHF_VERIFICATION__
	//verification is always done in the context of a single core and vcpu/midtable is 
	//populated by the verification driver
#endif

}

//wake up application processors (cores) in the system
void xmhf_baseplatform_arch_x86vmx_wakeupAPs(void){
	//step-1: setup AP boot-strap code at in the desired physical memory location 
	//note that we need an address < 1MB since the APs are woken up in real-mode
	//we choose 0x10000 physical or 0x1000:0x0000 logical
    {
		*_ap_bootstrap_blob_cr3 = read_cr3();
        *_ap_bootstrap_blob_cr4 = read_cr4();
        *_ap_bootstrap_blob_runtime_entrypoint = (u32)&_ap_pmode_entry_with_paging;
        #ifndef __XMHF_VERIFICATION__
        memcpy((void *)0x10000, (void *)_ap_bootstrap_blob, sizeof(_ap_bootstrap_blob));
        #endif
    }

#if defined (__DRT__)	
    //step-2: wake up the APs sending the INIT-SIPI-SIPI sequence as per the
    //MP protocol. Use the APIC for IPI purposes.
    if(!txt_is_launched()) { // XXX TODO: Do actual GETSEC[WAKEUP] in here?
        printf("\nBSP: Using APIC to awaken APs...");
        xmhf_baseplatform_arch_x86_wakeupAPs();
        printf("\nBSP: APs should be awake.");
    }else{
		//we ran SENTER, so do a GETSEC[WAKEUP]
        txt_heap_t *txt_heap;
        os_mle_data_t *os_mle_data;
        mle_join_t *mle_join;
        sinit_mle_data_t *sinit_mle_data;
        os_sinit_data_t *os_sinit_data;

        // sl.c unity-maps 0xfed00000 for 2M so these should work fine 
        #ifndef __XMHF_VERIFICATION__
        txt_heap = get_txt_heap();
        //printf("\ntxt_heap = 0x%08x", (u32)txt_heap);
        os_mle_data = get_os_mle_data_start(txt_heap);
        (void)os_mle_data;
        //printf("\nos_mle_data = 0x%08x", (u32)os_mle_data);
        sinit_mle_data = get_sinit_mle_data_start(txt_heap);
        //printf("\nsinit_mle_data = 0x%08x", (u32)sinit_mle_data);
        os_sinit_data = get_os_sinit_data_start(txt_heap);
        //printf("\nos_sinit_data = 0x%08x", (u32)os_sinit_data);
	#endif
            
        // Start APs.  Choose wakeup mechanism based on
        // capabilities used. MLE Dev Guide says MLEs should
        // support both types of Wakeup mechanism. 

        // We are jumping straight into the 32-bit portion of the
        // unity-mapped trampoline that starts at 64K
        // physical. Without SENTER, or with AMD, APs start in
        // 16-bit mode.  We get to skip that. 
        //printf("\nBSP: _mle_join_start = 0x%08x, _ap_bootstrap_start = 0x%08x",
		//	(u32)_mle_join_start, (u32)_ap_bootstrap_start);
        printf("\nBSP: _ap_bootstrap_blob_mle_join_start = 0x%08x, _ap_bootstrap_blob = 0x%08x",
			(u32)_ap_bootstrap_blob_mle_join_start, (u32)_ap_bootstrap_blob);

        // enable SMIs on BSP before waking APs (which will enable them on APs)
        // because some SMM may take immediate SMI and hang if AP gets in first 
        //printf("Enabling SMIs on BSP\n");
        //__getsec_smctrl();
                
        #ifndef __XMHF_VERIFICATION__
        mle_join = (mle_join_t*)((u32)_ap_bootstrap_blob_mle_join_start - (u32)_ap_bootstrap_blob + 0x10000); // XXX magic number
        #endif
        
        printf("\nBSP: mle_join.gdt_limit = %x", mle_join->gdt_limit);
        printf("\nBSP: mle_join.gdt_base = %x", mle_join->gdt_base);
        printf("\nBSP: mle_join.seg_sel = %x", mle_join->seg_sel);
        printf("\nBSP: mle_join.entry_point = %x", mle_join->entry_point);                

	#ifndef __XMHF_VERIFICATION__
        write_priv_config_reg(TXTCR_MLE_JOIN, (uint64_t)(unsigned long)mle_join);
		
        if (os_sinit_data->capabilities.rlp_wake_monitor) {
            printf("\nBSP: joining RLPs to MLE with MONITOR wakeup");
            printf("\nBSP: rlp_wakeup_addr = 0x%x", sinit_mle_data->rlp_wakeup_addr);
            *((uint32_t *)(unsigned long)(sinit_mle_data->rlp_wakeup_addr)) = 0x01;
        }else {
            printf("\nBSP: joining RLPs to MLE with GETSEC[WAKEUP]");
            __getsec_wakeup();
            printf("\nBSP: GETSEC[WAKEUP] completed");
        }
	#endif

		
	}
	
#else //!__DRT__
        printf("\nBSP: Using APIC to awaken APs...");
        xmhf_baseplatform_arch_x86_wakeupAPs();
        printf("\nBSP: APs should be awake.");

#endif 


}

//initialize SMP
void xmhf_baseplatform_arch_smpinitialize(void){
  u32 cpu_vendor;
  
  //grab CPU vendor
  cpu_vendor = xmhf_baseplatform_arch_getcpuvendor();
  //HALT_ON_ERRORCOND(cpu_vendor == CPU_VENDOR_AMD || cpu_vendor == CPU_VENDOR_INTEL);
  HALT_ON_ERRORCOND(cpu_vendor == CPU_VENDOR_INTEL);

  
  //setup Master-ID Table (MIDTABLE)
  {
    int i;
	#ifndef __XMHF_VERIFICATION__
		for(i=0; i < (int)rpb->XtVmmMPCpuinfoNumEntries; i++){
			g_midtable[g_midtable_numentries].cpu_lapic_id = g_cpumap[i].lapic_id;
			g_midtable[g_midtable_numentries].vcpu_vaddr_ptr = 0;
			g_midtable_numentries++;
		}
	#else
	//verification is always done in the context of a single core and vcpu/midtable is 
	//populated by the verification driver
	//TODO: incorporate some sort of BIOS data area within the verification harness that will
	//allow us to populate these tables during verification
	#endif
  }


  ////allocate and setup VCPU structure on each CPU
  //if(cpu_vendor == CPU_VENDOR_AMD)
	//xmhf_baseplatform_arch_x86svm_allocandsetupvcpus(cpu_vendor);
  //else //CPU_VENDOR_INTEL
	xmhf_baseplatform_arch_x86vmx_allocandsetupvcpus(cpu_vendor);

	//signal that basic base platform data structure initialization is complete 
	//(used by the exception handler component)
	g_bplt_initiatialized = true;

  //wake up APS
  if(g_midtable_numentries > 1){
    //if(cpu_vendor == CPU_VENDOR_AMD)
	 // xmhf_baseplatform_arch_x86svm_wakeupAPs();
    //else //CPU_VENDOR_INTEL
	  xmhf_baseplatform_arch_x86vmx_wakeupAPs();
  }


  //fall through to common code  
  {
	 void _ap_pmode_entry_with_paging(void);
   printf("\nRelinquishing BSP thread and moving to common...");
   // Do some low-level init and then call allcpus_common_start() below
   _ap_pmode_entry_with_paging(); 
   printf("\nBSP must never get here. HALT!");
   HALT();
  }
}

//---putVMCS--------------------------------------------------------------------
// routine takes vcpu vmcsfields and stores it in the CPU VMCS 
void xmhf_baseplatform_arch_x86vmx_putVMCS(VCPU *vcpu){
    unsigned int i;
    for(i=0; i < g_vmx_vmcsrwfields_encodings_count; i++){
      u32 *field = (u32 *)((u32)&vcpu->vmcs + (u32)g_vmx_vmcsrwfields_encodings[i].fieldoffset);
      u32 fieldvalue = *field;
      //printf("\nvmwrite: enc=0x%08x, value=0x%08x", vmcsrwfields_encodings[i].encoding, fieldvalue);
      if(!__vmx_vmwrite(g_vmx_vmcsrwfields_encodings[i].encoding, fieldvalue)){
        printf("\nCPU(0x%02x): VMWRITE failed. HALT!", vcpu->id);
        HALT();
      }
    }
}

//---getVMCS--------------------------------------------------------------------
// routine takes CPU VMCS and stores it in vcpu vmcsfields  
void xmhf_baseplatform_arch_x86vmx_getVMCS(VCPU *vcpu){
  unsigned int i;
  for(i=0; i < g_vmx_vmcsrwfields_encodings_count; i++){
      u32 *field = (u32 *)((u32)&vcpu->vmcs + (u32)g_vmx_vmcsrwfields_encodings[i].fieldoffset);
      __vmx_vmread(g_vmx_vmcsrwfields_encodings[i].encoding, field);
  }  
  for(i=0; i < g_vmx_vmcsrofields_encodings_count; i++){
      u32 *field = (u32 *)((u32)&vcpu->vmcs + (u32)g_vmx_vmcsrofields_encodings[i].fieldoffset);
      __vmx_vmread(g_vmx_vmcsrofields_encodings[i].encoding, field);
  }  
}

//--debug: dumpVMCS dumps VMCS contents-----------------------------------------
void xmhf_baseplatform_arch_x86vmx_dumpVMCS(VCPU *vcpu){
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
