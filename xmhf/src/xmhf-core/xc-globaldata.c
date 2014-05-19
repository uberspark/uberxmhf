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

/**
 * XMHF core global data module
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf-core.h>


//core DMA protection buffer (if DMA protections need to be re-initialized on the target platform)
//u8 g_core_dmaprot_buffer[SIZE_CORE_DMAPROT_BUFFER] __attribute__(( section(".palign_data") ));

//core parameter block
XMHF_HYPAPP_PARAMETERBLOCK *paramcore = (XMHF_HYPAPP_PARAMETERBLOCK *)&paramcore_start;

//hypapp parameter block
XMHF_HYPAPP_PARAMETERBLOCK *paramhypapp = (XMHF_HYPAPP_PARAMETERBLOCK *)&paramhypapp_start;

//hypapp header
XMHF_HYPAPP_HEADER *g_hypappheader=(XMHF_HYPAPP_HEADER *)__TARGET_BASE_XMHFHYPAPP;

//hypapp callback hub entry point and hypapp top of stack
u32 hypapp_cbhub_pc=0;
u32 hypapp_tos=0;

// platform cpus
xc_cpu_t g_xc_cpu[MAX_PLATFORM_CPUS] __attribute__(( section(".data") ));

// primary partitions
xc_partition_t g_xc_primary_partition[MAX_PRIMARY_PARTITIONS] __attribute__(( section(".data") ));

// partition index for the richguest
//u32 xc_partition_richguest_index = 0;


//----------------------------------------------------------------------------------
// global data initialization function
//----------------------------------------------------------------------------------

void *xc_globaldata_initialize(void *input){
	u32 i;
	xc_cpu_t *xc_cpu_bsp;
	XMHF_BOOTINFO *xcbootinfo = (XMHF_BOOTINFO *)input;
	
	/*//initialize cpu data structure
	printf("\nNo. of CPU entries = %u", xcbootinfo->cpuinfo_numentries);

	for(i=0; i < xcbootinfo->cpuinfo_numentries; i++){
		g_xc_cpu[i].cpuid = xcbootinfo->cpuinfo_buffer[i].lapic_id;
		g_xc_cpu[i].is_bsp = xcbootinfo->cpuinfo_buffer[i].isbsp;
		g_xc_cpu[i].is_quiesced = false;
		g_xc_cpu[i].parentpartition_index = XC_PARTITION_INDEX_INVALID;
		printf("\nCPU #%u: bsp=%u, lapic_id=0x%02x, cpuarchdata=%08x", i, xcbootinfo->cpuinfo_buffer[i].isbsp, xcbootinfo->cpuinfo_buffer[i].lapic_id, (u32)g_xc_cpu[i].cpuarchdata);
	}*/

	//g_xc_cpu_count = xcbootinfo->cpuinfo_numentries;
	
	/*//initialize partition data structures
		//primary partitions
		for(i=0; i < MAX_PRIMARY_PARTITIONS; i++){
				g_xc_primary_partition[i].partitionid=i;
				g_xc_primary_partition[i].partitiontype = XC_PARTITION_PRIMARY;
		}*/

	//initialize cpu table
	/*for(i=0; i < g_xc_cpu_count; i++){
			g_xc_cputable[i].cpuid = xcbootinfo->cpuinfo_buffer[i].lapic_id;
			g_xc_cputable[i].cpu_index = i;
			if(xcbootinfo->cpuinfo_buffer[i].isbsp)
				xc_cpu_bsp = &g_xc_cpu[i];
	}*/
	
	//return index_cpudata_bsp;
	return xc_cpu_bsp;
}


