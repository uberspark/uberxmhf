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

// runtime.c
// author: amit vasudevan (amitvasudevan@acm.org)

//---includes-------------------------------------------------------------------
#include <xmhf.h> 


//---runtime main---------------------------------------------------------------
void emhf_runtime_entry(void){
	u32 cpu_vendor;

	//get CPU vendor
	cpu_vendor = emhf_baseplatform_getcpuvendor();
        (void)cpu_vendor;

	//initialize Runtime Parameter Block (rpb)
	rpb = (RPB *)&arch_rpb;

	//setup debugging	
	emhf_debug_init((char *)&rpb->RtmUartConfig);
	printf("\nruntime initializing...");

  	//initialize basic platform elements
	emhf_baseplatform_initialize();

    //[debug] dump E820 and MP table
 	printf("\nNumber of E820 entries = %u", rpb->XtVmmE820NumEntries);
	{
		int i;
		for(i=0; i < (int)rpb->XtVmmE820NumEntries; i++){
		printf("\n0x%08x%08x, size=0x%08x%08x (%u)", 
          g_e820map[i].baseaddr_high, g_e820map[i].baseaddr_low,
          g_e820map[i].length_high, g_e820map[i].length_low,
          g_e820map[i].type);
		}
  	}
	printf("\nNumber of MP entries = %u", rpb->XtVmmMPCpuinfoNumEntries);
	{
		int i;
		for(i=0; i < (int)rpb->XtVmmMPCpuinfoNumEntries; i++)
			printf("\nCPU #%u: bsp=%u, lapic_id=0x%02x", i, g_cpumap[i].isbsp, g_cpumap[i].lapic_id);
	}


	//setup EMHF exception handler component
	emhf_xcphandler_initialize();


	//[debug]: test IDT/exception routing
	//__asm__ __volatile__ ("int $0x03\r\n");


#if defined (__DRTM_DMA_PROTECTION__)
	#if defined (__DMAPROT__)
		{
				u64 protectedbuffer_paddr;
				u32 protectedbuffer_vaddr;
				u32 protectedbuffer_size;
				
				protectedbuffer_paddr = hva2spa(&g_rntm_dmaprot_buffer);
				protectedbuffer_vaddr = (u32)&g_rntm_dmaprot_buffer;
				protectedbuffer_size = emhf_dmaprot_getbuffersize(ADDR_4GB);
				ASSERT(protectedbuffer_size <= SIZE_G_RNTM_DMAPROT_BUFFER);
				
				printf("\nRuntime: Re-initializing DMA protection...");
				if(!emhf_dmaprot_initialize(protectedbuffer_paddr, protectedbuffer_vaddr, protectedbuffer_size)){
					printf("\nRuntime: Unable to re-initialize DMA protection. HALT!");
					HALT();
				}

				//protect SL and runtime memory regions
				emhf_dmaprot_protect(rpb->XtVmmRuntimePhysBase - PAGE_SIZE_2M, rpb->XtVmmRuntimeSize+PAGE_SIZE_2M);
				printf("\nRuntime: Protected SL+Runtime (%08lx-%08x) from DMA.", 
					rpb->XtVmmRuntimePhysBase - PAGE_SIZE_2M,
					rpb->XtVmmRuntimePhysBase+rpb->XtVmmRuntimeSize);
		}
	#endif //__DMAPROT__
#else //!__DRTM_DMA_PROTECTION__
	if(cpu_vendor == CPU_VENDOR_INTEL)
	{
		extern void vmx_eap_zap(void);
		vmx_eap_zap();
	}
#endif

	printf("\nPreSelectors CS=0x%04x, DS=0x%04x, ES=0x%04x, SS=0x%04x", 
			(u16)read_segreg_cs(), (u16)read_segreg_ds(),
			(u16)read_segreg_es(), (u16)read_segreg_ss());
	printf("\nPreSelectors FS=0x%04x, GS=0x%04x", 
			(u16)read_segreg_fs(), (u16)read_segreg_gs());
	printf("\nPreSelectors TR=0x%04x", (u16)read_tr_sel());


	//initialize base platform with SMP 
	emhf_baseplatform_smpinitialize();
	
	printf("\nRuntime: We should NEVER get here!");
	ASSERT(0);
	HALT();
}

//we get control here in the context of *each* physical CPU core 
//vcpu->isbsp = 1 if the core is a BSP or 0 if its an AP
//isEarlyInit = 1 if we were boot-strapped by the BIOS and is 0
//in the event we were launched from a running OS
void emhf_runtime_main(VCPU *vcpu, u32 isEarlyInit){
  //initialize CPU
  emhf_baseplatform_cpuinitialize();

  //initialize partition monitor (i.e., hypervisor) for this CPU
  emhf_partition_initializemonitor(vcpu);

  //setup guest OS state for partition
  emhf_partition_setupguestOSstate(vcpu);

  //initialize memory protection for this core
  emhf_memprot_initialize(vcpu);

  //initialize application parameter block and call app main
  {
  	APP_PARAM_BLOCK appParamBlock;
  	
	appParamBlock.bootsector_ptr = (u32)rpb->XtGuestOSBootModuleBase;
  	appParamBlock.bootsector_size = (u32)rpb->XtGuestOSBootModuleSize;
  	appParamBlock.optionalmodule_ptr = (u32)rpb->runtime_appmodule_base;
  	appParamBlock.optionalmodule_size = (u32)rpb->runtime_appmodule_size;
	appParamBlock.runtimephysmembase = (u32)rpb->XtVmmRuntimePhysBase;  
    COMPILE_TIME_ASSERT(sizeof(appParamBlock.cmdline) >= sizeof(rpb->cmdline));
    strncpy(appParamBlock.cmdline, rpb->cmdline, sizeof(appParamBlock.cmdline));

  	//call app main
  	if(emhf_app_main(vcpu, &appParamBlock)){
    	printf("\nCPU(0x%02x): EMHF app. failed to initialize. HALT!", vcpu->id);
    	HALT();
  	}
  }   	

  //increment app main success counter
  spin_lock(&g_lock_appmain_success_counter);
  g_appmain_success_counter++;
  spin_unlock(&g_lock_appmain_success_counter);
	
  //if BSP, wait for all cores to go through app main successfully
  //TODO: conceal g_midtable_numentries behind interface
  //emhf_baseplatform_getnumberofcpus
  if(vcpu->isbsp && (g_midtable_numentries > 1)){
		printf("\nCPU(0x%02x): Waiting for all cores to cycle through appmain...", vcpu->id);
		while(g_appmain_success_counter < g_midtable_numentries);	
		printf("\nCPU(0x%02x): All cores have successfully been through appmain.", vcpu->id);
  }

	//late initialization is still WiP and we can get only this far 
	//currently
	if(!isEarlyInit){
		printf("\nCPU(0x%02x): Late-initialization, WiP, HALT!", vcpu->id);
		HALT();
	}

  //initialize support for SMP guests
  emhf_smpguest_initialize(vcpu);

  //XXX: debug
  //__asm__ __volatile__("int $0x02\r\n");
  //printf("\nCPU(0x%02x): Halting!", vcpu->id);
	printf("\n[%02x]Selectors CS=0x%04x, DS=0x%04x, ES=0x%04x, SS=0x%04x", vcpu->id,
			(u16)read_segreg_cs(), (u16)read_segreg_ds(),
			(u16)read_segreg_es(), (u16)read_segreg_ss());
	printf("\n[%02x]Selectors FS=0x%04x, GS=0x%04x", vcpu->id,
			(u16)read_segreg_fs(), (u16)read_segreg_gs());
	printf("\n[%02x]Selectors TR=0x%04x", vcpu->id, (u16)read_tr_sel());
  	
	
  //start partition
  printf("\n%s[%02x]: starting partition...", __FUNCTION__, vcpu->id);
  emhf_partition_start(vcpu);

  printf("\nCPU(0x%02x): FATAL, should not be here. HALTING!", vcpu->id);
  HALT();

}
