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
#include <xmhf-core.h> 

void xmhf_runtime_entry(void){
	//initialize Runtime Parameter Block (rpb)
	rpb = (RPB *)&arch_rpb;
	
	//setup debugging	
	xmhf_debug_init((char *)&rpb->RtmUartConfig);
	printf("\nxmhf-core: starting...");

  	//initialize basic platform elements
	xmhf_baseplatform_initialize();

    //[debug] dump E820 and MP table
 	#ifndef __XMHF_VERIFICATION__
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
	#endif //__XMHF_VERIFICATION__

	#ifndef __XMHF_VERIFICATION__
	//setup EMHF exception handler component
	xmhf_xcphandler_initialize();
	#endif

	printf("\nproceeding to test IDT\n\n");
	asm volatile("int $0x03 \r\n");

	printf("\nXMHF Tester Finished!");
	printf("\nHalting");
	printf("\n");
	HALT();	
}

//---runtime main---------------------------------------------------------------
void disabled_xmhf_runtime_entry(void){
	u32 cpu_vendor;
	//XMHF_HYPAPP_HEADER *hypappheader;

	//get CPU vendor
	cpu_vendor = xmhf_baseplatform_getcpuvendor();
        (void)cpu_vendor;

	//initialize Runtime Parameter Block (rpb)
	rpb = (RPB *)&arch_rpb;

	//setup debugging	
	xmhf_debug_init((char *)&rpb->RtmUartConfig);
	printf("\nruntime initializing...");

  	//initialize basic platform elements
	xmhf_baseplatform_initialize();

    //[debug] dump E820 and MP table
 	#ifndef __XMHF_VERIFICATION__
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
	#endif //__XMHF_VERIFICATION__


	#ifndef __XMHF_VERIFICATION__
	//setup EMHF exception handler component
	xmhf_xcphandler_initialize();
	#endif

#if defined (__DMAP__)
	xmhf_dmaprot_reinitialize();
#endif


	//invoke XMHF api hub initialization function to initialize core API
	//interface layer
	xmhf_apihub_initialize();


	//paramhypapp->param1 = 0;	//write to hypapp parameter region, should trgger a #pf
	//*((u32 *)0x1D000000) = 0;	//write to hypapp code/data/stack region, shoulod trigger a #pf
	//{
	//		typedef void (*testfun)(void);
	//		testfun fun = (testfun)0x1D000000;
	//		fun();	//execute code in hypapp memory region, should trigger a #pf
	//}
	
	//call hypapp main function
	{
		//APP_PARAM_BLOCK appParamBlock;
  	
		//appParamBlock.bootsector_ptr = (u32)rpb->XtGuestOSBootModuleBase;
		//appParamBlock.bootsector_size = (u32)rpb->XtGuestOSBootModuleSize;
		//appParamBlock.optionalmodule_ptr = (u32)rpb->runtime_appmodule_base;
		//appParamBlock.optionalmodule_size = (u32)rpb->runtime_appmodule_size;
		//appParamBlock.runtimephysmembase = (u32)rpb->XtVmmRuntimePhysBase;  
		//appParamBlock.runtimesize = (u32)rpb->XtVmmRuntimeSize;
		//COMPILE_TIME_ASSERT(sizeof(appParamBlock.cmdline) >= sizeof(rpb->cmdline));
		//#ifndef __XMHF_VERIFICATION__
		//strncpy(appParamBlock.cmdline, rpb->cmdline, sizeof(appParamBlock.cmdline));
		//#endif
		hypapp_env_block_t hypappenvb;
		hypappenvb.runtimephysmembase = (u32)rpb->XtVmmRuntimePhysBase;  
		hypappenvb.runtimesize = (u32)rpb->XtVmmRuntimeSize;
	
		//call app main
		printf("\n%s: proceeding to call xmhfhypapp_main on BSP", __FUNCTION__);
		//xmhfhypapp_main(&appParamBlock);
		xmhfhypapp_main(hypappenvb);
		printf("\n%s: came back into core", __FUNCTION__);

	}   	

	//[]debug
	//printf("\n%s: Halting", __FUNCTION__);
	//printf("\n%s: XMHF Tester Finished!", __FUNCTION__);
	//HALT();

	//initialize base platform with SMP 
	xmhf_baseplatform_smpinitialize();

	printf("\nRuntime: We should NEVER get here!");
	HALT_ON_ERRORCOND(0);
}

//we get control here in the context of *each* physical CPU core 
void xmhf_runtime_main(context_desc_t context_desc){ 
	//[debug]
	printf("\n%s: partdesc.id=%u, cpudesc.id=%u, cpudesc.isbsp=%u", __FUNCTION__, context_desc.partition_desc.id, context_desc.cpu_desc.id, context_desc.cpu_desc.isbsp);

	//TODO: check if this CPU is allocated to the "rich" guest. if so, pass it on to
	//the rich guest initialization procedure. if the CPU is not allocated to the
	//rich guest, enter it into a CPU pool for use by other partitions
	
	//initialize and boot "rich" guest
	xmhf_smpguest_initialize(context_desc);

	//TODO: implement CPU pooling for use by other partitions
	
	#ifndef __XMHF_VERIFICATION__
	printf("\nCPU(0x%02x): FATAL, should not be here. HALTING!", context_desc.cpu_desc.id);
	HALT();
	#endif //__XMHF_VERIFICATION__
	
}
