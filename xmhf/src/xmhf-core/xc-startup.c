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

// XMHF core startup module
// author: amit vasudevan (amitvasudevan@acm.org)

//---includes-------------------------------------------------------------------
#include <xmhf-core.h> 

void xmhf_runtime_entry(void){
	xc_cpu_t *xc_cpu_bsp;

	//setup debugging	
	xmhf_debug_init((char *)&xcbootinfo->debugcontrol_buffer);
	printf("\nxmhf-core: starting...");

    //[debug] dump E820
 	#ifndef __XMHF_VERIFICATION__
 	printf("\nNumber of E820 entries = %u", xcbootinfo->memmapinfo_numentries);
	{
		int i;
		for(i=0; i < (int)xcbootinfo->memmapinfo_numentries; i++){
			printf("\n0x%08x%08x, size=0x%08x%08x (%u)", 
			  xcbootinfo->memmapinfo_buffer[i].baseaddr_high, xcbootinfo->memmapinfo_buffer[i].baseaddr_low,
			  xcbootinfo->memmapinfo_buffer[i].length_high, xcbootinfo->memmapinfo_buffer[i].length_low,
			  xcbootinfo->memmapinfo_buffer[i].type);
		}
  	}
	#endif //__XMHF_VERIFICATION__

	//initialize global data structures
	xc_cpu_bsp = (xc_cpu_t *)xc_globaldata_initialize((void *)xcbootinfo);

  	//initialize basic platform elements
	xmhf_baseplatform_initialize();

	#ifndef __XMHF_VERIFICATION__
	//setup XMHF exception handler component
	xmhf_xcphandler_initialize();
	#endif

	#if defined (__DMAP__)
	xmhf_dmaprot_reinitialize();
	#endif

	//initialize richguest
	xmhf_richguest_initialize(xc_partition_richguest_index);

	//invoke XMHF api hub initialization function to initialize core API
	//interface layer
	xmhf_apihub_initialize();

	//initialize base platform with SMP 
	xmhf_baseplatform_smpinitialize();

	printf("\nRuntime: We should NEVER get here!");
	HALT_ON_ERRORCOND(0);
}


//we get control here in the context of *each* physical CPU core 
//void xmhf_runtime_main(xc_cpu_t *xc_cpu){ 
void xmhf_runtime_main(u32 cpu_index){ 
	static u32 _xc_startup_hypappmain_counter = 0; 
	static u32 _xc_startup_hypappmain_counter_lock = 1; 
	xc_cpu_t *xc_cpu = &g_xc_cpu[cpu_index];

	//[debug]
	printf("\n%s: cpu id=%u", __FUNCTION__, xc_cpu->cpuid);

	//add cpu to rich guest partition
	//TODO: check if this CPU is allocated to the "rich" guest. if so, pass it on to
	//the rich guest initialization procedure. if the CPU is not allocated to the
	//rich guest, enter it into a CPU pool for use by other partitions
	xmhf_richguest_addcpu(xc_cpu, xc_partition_richguest_index);
	
	//call hypapp main function
    spin_lock(&_xc_startup_hypappmain_counter_lock);
	{
		hypapp_env_block_t hypappenvb;
		context_desc_t context_desc;
		xc_partition_t *xc_partition = &g_xc_primary_partition[xc_cpu->parentpartition_index];

		context_desc.partition_desc.partition_index = xc_partition->partitionid;
		//context_desc.cpu_desc.cpuid = xc_cpu->cpuid;
		context_desc.cpu_desc.isbsp = xc_cpu->is_bsp;
		context_desc.cpu_desc.cpu_index = cpu_index;
		
		hypappenvb.runtimephysmembase = (u32)xcbootinfo->physmem_base;  
		hypappenvb.runtimesize = (u32)xcbootinfo->size;
	
		//call app main
		printf("\n%s: proceeding to call xmhfhypapp_main on BSP", __FUNCTION__);
		xc_hypapp_initialization(context_desc, hypappenvb);
		_xc_startup_hypappmain_counter++;
		printf("\n%s: came back into core", __FUNCTION__);

	}   	
    spin_unlock(&_xc_startup_hypappmain_counter_lock);

	//wait for hypapp main to execute on all the cpus
	while(_xc_startup_hypappmain_counter < g_xc_cpu_count);
	
	//start cpu in corresponding partition
	printf("\n%s[%u]: starting in partition...", __FUNCTION__, xc_cpu->cpuid);
	xmhf_partition_start(xc_cpu);
	
	#ifndef __XMHF_VERIFICATION__
	printf("\n%s: index_cpudata=%u: FATAL, should not be here. HALTING!", __FUNCTION__, xc_cpu->cpuid);
	HALT();
	#endif //__XMHF_VERIFICATION__
}
