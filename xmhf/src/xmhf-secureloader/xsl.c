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

//sl.c 
//XMHF secure loader implementation
//author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h> 

//this is the SL parameter block and is placed in a seperate (untrusted)
//section. It is populated by the XMHF bootloader.
struct _sl_parameter_block slpb __attribute__(( section(".sl_untrusted_params") )) = {
	.magic = SL_PARAMETER_BLOCK_MAGIC,
};

// we get here from _xmhf_sl_entry
void xmhf_sl_main(void){
	u32 runtime_physical_base;
	u32 runtime_size_2Maligned;
	RPB *rpb = (RPB *)&xmhf_rpb_start;

	//initialize debugging early on
	xmhf_debug_init((char *)&slpb.uart_config);

	printf("%s: alive and starting...\n", __FUNCTION__);
	
	//debug: dump SL parameter block
	printf("SL: slpb at = 0x%08x\n", (u32)&slpb);
	printf("	errorHandler=0x%08x\n", slpb.errorHandler);
	printf("	isEarlyInit=0x%08x\n", slpb.isEarlyInit);
	printf("	numE820Entries=%u\n", slpb.numE820Entries);
	printf("	system memory map buffer at 0x%08x\n", (u32)&slpb.memmapbuffer);
	printf("	numCPUEntries=%u\n", slpb.numCPUEntries);
	printf("	cpuinfo buffer at 0x%08x\n", (u32)&slpb.cpuinfobuffer);
	printf("	runtime size= %u bytes\n", slpb.runtime_size);
	printf("	OS bootmodule at 0x%08x, size=%u bytes\n", 
		slpb.runtime_osbootmodule_base, slpb.runtime_osbootmodule_size);
    printf("\tcmdline = \"%s\"\n", slpb.cmdline);

	//get runtime physical base
	runtime_physical_base = __TARGET_BASE_CORE;
	
	//compute 2M aligned runtime size
	runtime_size_2Maligned = PAGE_ALIGN_UP2M(slpb.runtime_size);

	printf("SL: runtime at 0x%08x; size=0x%08x bytes adjusted to 0x%08x bytes (2M aligned)\n", 
			runtime_physical_base, slpb.runtime_size, runtime_size_2Maligned);

	//setup runtime parameter block with required parameters
	{
		printf("SL: RPB at 0x%08x, magic=0x%08x\n", (u32)rpb, rpb->magic);
		HALT_ON_ERRORCOND(rpb->magic == RUNTIME_PARAMETER_BLOCK_MAGIC);
			
		//populate runtime parameter block fields
		rpb->isEarlyInit = slpb.isEarlyInit; //tell runtime if we started "early" or "late"
		
		//store runtime physical and virtual base addresses along with size
		rpb->XtVmmRuntimePhysBase = runtime_physical_base; 
		rpb->XtVmmRuntimeVirtBase = __TARGET_BASE_CORE;
		rpb->XtVmmRuntimeSize = slpb.runtime_size;

		//store revised E820 map and number of entries
		memcpy(hva2sla((void *)rpb->XtVmmE820Buffer), (void *)&slpb.memmapbuffer, (sizeof(GRUBE820) * slpb.numE820Entries) );
		rpb->XtVmmE820NumEntries = slpb.numE820Entries; 

		//store CPU table and number of CPUs
		memcpy(hva2sla((void *)rpb->XtVmmMPCpuinfoBuffer), (void *)&slpb.cpuinfobuffer, (sizeof(PCPU) * slpb.numCPUEntries) );
		rpb->XtVmmMPCpuinfoNumEntries = slpb.numCPUEntries; 

		//setup guest OS boot module info in LPB	
		rpb->XtGuestOSBootModuleBase=slpb.runtime_osbootmodule_base;
		rpb->XtGuestOSBootModuleSize=slpb.runtime_osbootmodule_size;

		//pass optional app module if any
		rpb->runtime_appmodule_base = slpb.runtime_appmodule_base;
		rpb->runtime_appmodule_size = slpb.runtime_appmodule_size;

	#if defined (__DEBUG_SERIAL__)
		//pass along UART config for serial debug output
		//rpb->RtmUartConfig = slpb.uart_config;
		memcpy(&rpb->RtmUartConfig, &slpb.uart_config, sizeof(rpb->RtmUartConfig));
	#endif

		//pass command line configuration forward 
		COMPILE_TIME_ASSERT(sizeof(slpb.cmdline) == sizeof(rpb->cmdline));
		strncpy(rpb->cmdline, (void *)&slpb.cmdline, sizeof(slpb.cmdline));
	}

	//initialize basic platform elements
	xmhf_sl_arch_baseplatform_initialize();
	
	//sanitize cache/MTRR/SMRAM (most important is to ensure that MTRRs 
	//do not contain weird mappings)
#if defined (__DRT__)
    xmhf_sl_arch_sanitize_post_launch();
#endif	//__DRT__

#if defined (__DMAP__)    
	//setup DMA protection on runtime (secure loader is already DMA protected)
	//xmhf_sl_arch_early_dmaprot_init(slpb.runtime_size);
	xmhf_sl_arch_early_dmaprot_init(__TARGET_BASE_SL, __TARGET_SIZE_SL + slpb.runtime_size);
#endif

	//transfer control to runtime
	xmhf_sl_arch_xfer_control_to_runtime(rpb);

#ifndef __XMHF_VERIFICATION__
	//we should never get here
	printf("\nSL: Fatal, should never be here!");
	HALT();
#else
	return;
#endif
} 

