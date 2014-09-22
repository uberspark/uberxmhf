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

#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcapi.h>

/*
 * 	XMHF core API
 *
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */

//////
//HPT related core APIs
void xc_api_hpt_setprot(context_desc_t context_desc, u64 gpa, u32 prottype){
	xc_api_hpt_arch_setprot(context_desc, gpa, prottype);
}

u32 xc_api_hpt_getprot(context_desc_t context_desc, u64 gpa){
	return xc_api_hpt_arch_getprot(context_desc, gpa);
}

void xc_api_hpt_setentry(context_desc_t context_desc, u64 gpa, u64 entry){
	xc_api_hpt_arch_setentry(context_desc, gpa, entry);
}

u64 xc_api_hpt_getentry(context_desc_t context_desc, u64 gpa){
	return xc_api_hpt_arch_getentry(context_desc, gpa);
}

//*
void xc_api_hpt_flushcaches(context_desc_t context_desc){
	xc_api_hpt_arch_flushcaches(context_desc, false);
}

//*
void xc_api_hpt_flushcaches_smp(context_desc_t context_desc){
	xc_api_hpt_arch_flushcaches(context_desc, true);
}

u64 xc_api_hpt_lvl2pagewalk(context_desc_t context_desc, u64 gva){
	return xc_api_hpt_arch_lvl2pagewalk(context_desc, gva);
}


//////
//Trapmask related APIs
void xc_api_trapmask_set(context_desc_t context_desc, xc_hypapp_arch_param_t trapmaskparams){
	xc_api_trapmask_arch_set(context_desc, trapmaskparams);
}

void xc_api_trapmask_clear(context_desc_t context_desc, xc_hypapp_arch_param_t trapmaskparams){
	xc_api_trapmask_arch_clear(context_desc, trapmaskparams);
}

//////
//cpu state related core APIs
void xc_api_cpustate_set(context_desc_t context_desc, xc_hypapp_arch_param_t cpustateparams){
	xc_api_cpustate_arch_set(context_desc, cpustateparams);
}

xc_hypapp_arch_param_t xc_api_cpustate_get(context_desc_t context_desc, u64 operation){
	return xc_api_cpustate_arch_get(context_desc, operation);
}



//////
//partition related core APIs

static u32 _partition_current_index=0;
static u32 _xc_cpu_current_index=0;
static xc_cpupartitiontable_t _xc_cpupartitiontable[MAX_PLATFORM_CPUS];
static u32 _xc_cpupartitiontable_current_index=0;

//*
static void _xc_api_partition_create_establishEPTshape(xc_partition_hptdata_x86vmx_t *eptdata){
	u64 *pml4_table, *pdp_table, *pd_table;
	u32 i, j, paddr=0;

	pml4_table = (u64 *)eptdata->vmx_ept_pml4_table;
	pml4_table[0] = (u64) (hva2spa((void*)eptdata->vmx_ept_pdp_table) | 0x7);

	pdp_table = (u64 *)eptdata->vmx_ept_pdp_table;

	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		pdp_table[i] = (u64) ( hva2spa((void*)eptdata->vmx_ept_pd_tables + (PAGE_SIZE_4K * i)) | 0x7 );
		pd_table = (u64 *)  ((u32)eptdata->vmx_ept_pd_tables + (PAGE_SIZE_4K * i)) ;

		for(j=0; j < PAE_PTRS_PER_PDT; j++){
			pd_table[j] = (u64) ( hva2spa((void*)eptdata->vmx_ept_p_tables + (PAGE_SIZE_4K * ((i*PAE_PTRS_PER_PDT)+j))) | 0x7 );
		}
	}
}

//*
u32 xc_api_partition_create(u32 partitiontype){
	u32 partition_index = XC_PARTITION_INDEX_INVALID;

	//we only support primary partitions
	if(partitiontype != XC_PARTITION_PRIMARY)
		return partition_index;

	//check if we have run out of partition memory backing
	if(_partition_current_index > MAX_PRIMARY_PARTITIONS)
		return partition_index;

	g_xc_primary_partition[_partition_current_index].partitionid=_partition_current_index;
	g_xc_primary_partition[_partition_current_index].partitiontype = XC_PARTITION_PRIMARY;
	g_xc_primary_partition[_partition_current_index].numcpus = 0;

	_xc_api_partition_create_establishEPTshape( (xc_partition_hptdata_x86vmx_t *)g_xc_primary_partition[_partition_current_index].hptdata );

    partition_index = _partition_current_index;
    _partition_current_index++;

    return partition_index;
}

//*
context_desc_t xc_api_partition_addcpu(u32 partition_index, u32 cpuid, bool is_bsp){
	context_desc_t context_desc;
	u32 cpu_index;

	//_XDPRINTF_("%s(%u): partition_index=%u, cpuid=%x, is_bsp=%u\n", __FUNCTION__, cpuid, partition_index, cpuid, is_bsp);

	//initialize context_desc
	context_desc.cpu_desc.cpu_index = XC_PARTITION_INDEX_INVALID;
	context_desc.cpu_desc.isbsp = is_bsp;
	context_desc.partition_desc.partition_index = XC_PARTITION_INDEX_INVALID;

	//sanity check partition_index
	if ( !(partition_index >=0 && partition_index < MAX_PRIMARY_PARTITIONS)	)
		return context_desc;

	//check if have run out of xc_cpu memory backing
	if(_xc_cpu_current_index > MAX_PLATFORM_CPUS)
		return context_desc;

	//check if we are beyond the maximum cpus supported
	if(_xc_cpupartitiontable_current_index > MAX_PLATFORM_CPUS)
		return context_desc;

	if(g_xc_primary_partition[partition_index].numcpus >= MAX_PLATFORM_CPUS)
		return context_desc;

	cpu_index = _xc_cpu_current_index++;

	g_xc_cpu[cpu_index].cpuid = cpuid;
	g_xc_cpu[cpu_index].is_bsp = is_bsp;
	g_xc_cpu[cpu_index].is_quiesced = false;
	g_xc_cpu[cpu_index].parentpartition_index = partition_index;

	_xc_cpupartitiontable[_xc_cpupartitiontable_current_index].cpuid = cpuid;
	_xc_cpupartitiontable[_xc_cpupartitiontable_current_index].partition_index = partition_index;
	_xc_cpupartitiontable[_xc_cpupartitiontable_current_index].cpu_index = cpu_index;
	_xc_cpupartitiontable_current_index++;

	g_xc_primary_partition[partition_index].cputable[g_xc_primary_partition[partition_index].numcpus].cpuid = cpuid;
	g_xc_primary_partition[partition_index].cputable[g_xc_primary_partition[partition_index].numcpus].cpu_index = cpu_index;
	g_xc_primary_partition[partition_index].numcpus++;

	//perform arch. specific cpu partition initialization
	if(!xc_api_partition_arch_addcpu(partition_index, cpu_index))
		return context_desc;

	//create context_desc for the partition and cpu
	context_desc.cpu_desc.cpu_index = cpu_index;
	context_desc.partition_desc.partition_index = partition_index;

	//_XDPRINTF_("%s(%u): returning %u (numcpus=%u)\n", __FUNCTION__, cpuid, cpu_index, g_xc_primary_partition[partition_index].numcpus);
	return context_desc;
}

//**
context_desc_t xc_api_partition_getcontextdesc(u32 cpuid){
		context_desc_t context_desc;
		u32 partition_index, cpu_index, i;
		bool found_indices=false;

		//initialize context_desc to invalid values so we can just return it if
		//we encounter any errors
		context_desc.cpu_desc.cpu_index = XC_PARTITION_INDEX_INVALID;
		context_desc.cpu_desc.isbsp = false;
		context_desc.partition_desc.partition_index = XC_PARTITION_INDEX_INVALID;

		//obtain partition_index from cpuid
		for(i=0; i < _xc_cpupartitiontable_current_index; i++){
				if(_xc_cpupartitiontable[i].cpuid == cpuid){
					partition_index = _xc_cpupartitiontable[i].partition_index;
					cpu_index = _xc_cpupartitiontable[i].cpu_index;
					found_indices = true;
					break;
				}
		}

		//check if we got a valid cpu and partition indices
		if(!found_indices)
			return context_desc;


		//populate context_desc with cpu and partition indices
		context_desc.cpu_desc.cpu_index = cpu_index;
		context_desc.cpu_desc.isbsp = g_xc_cpu[cpu_index].is_bsp;
		context_desc.partition_desc.partition_index = partition_index;

		return context_desc;
}

bool xc_api_partition_startcpu(context_desc_t context_desc){
	return xc_api_partition_arch_startcpu(context_desc);

}


//////
//platform related core API
void xc_api_platform_shutdown(context_desc_t context_desc){
	xc_api_platform_arch_shutdown(context_desc);
}

xc_platformdevice_desc_t xc_api_platform_initializeandenumeratedevices(context_desc_t context_desc){
    return xc_api_platform_arch_initializeandenumeratedevices(context_desc);
}

bool xc_api_platform_allocdevices_to_partition(context_desc_t context_desc, xc_platformdevice_desc_t device_descs){
    return xc_api_platform_arch_allocdevices_to_partition(context_desc, device_descs);
}

bool xc_api_platform_deallocdevices_from_partition(context_desc_t context_desc, xc_platformdevice_desc_t device_descs){
    return xc_api_platform_arch_deallocdevices_from_partition(context_desc, device_descs);
}



///////
XMHF_SLAB("coreapi")

