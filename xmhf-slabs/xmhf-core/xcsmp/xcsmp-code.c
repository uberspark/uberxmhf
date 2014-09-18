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

// XMHF core SMP initialization (xcsmp)
// author: amit vasudevan (amitvasudevan@acm.org)

//---includes-------------------------------------------------------------------
#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcsmp.h>
#include <xcrichguest.h>

static volatile u32 _cpucount = 0; // count of platform cpus
static u32 xc_richguest_partition_index=XC_PARTITION_INDEX_INVALID;

bool xcsmp_entry(void){

//#if defined (__DMAP__)
//	xcsmp_arch_dmaprot_reinitialize();
//#endif

	//create rich guest partition
	_XDPRINTF_("%s: proceeding to create rich guest partition...\n", __FUNCTION__);
	xc_richguest_partition_index = XMHF_SLAB_CALL(xc_api_partition_create(XC_PARTITION_PRIMARY));
	if(xc_richguest_partition_index == XC_PARTITION_INDEX_INVALID){
		_XDPRINTF_("%s: Fatal error, could not create rich guest partition!\n", __FUNCTION__);
		HALT();
	}
	_XDPRINTF_("%s: created rich guest partition %u\n", __FUNCTION__, xc_richguest_partition_index);


    //process system device allocation and DMA protection
    if(!xcdev_initialize(xc_richguest_partition_index)){
        _XDPRINTF_("%s: Fatal, could not perform system device allocation and DMA protection. Halting!\n", __FUNCTION__);
        HALT();
    }

    //initialize rich guest partition
    XMHF_SLAB_CALL(xcrichguest_initialize(xc_richguest_partition_index));
    _XDPRINTF_("\n%s: initialized rich guest partition %u\n", __FUNCTION__, xc_richguest_partition_index);


	if( xcsmp_arch_smpinitialize() ){
		_XDPRINTF_("\nRuntime: We should NEVER get here!");
		HALT();
	}

}

//executes in the context of each physical CPU
void xcsmp_smpstart(u32 cpuid, bool isbsp){
    static u32 _smpinitialize_lock = 1;
    context_desc_t context_desc;

    //serialize execution
    spin_lock(&_smpinitialize_lock);

        //initialize CPU
        xcsmp_arch_initializecpu(cpuid, isbsp);

        //add cpu to rich guest partition
        //TODO: check if this CPU is allocated to the "rich" guest. if so, pass it on to
        //the rich guest initialization procedure. if the CPU is not allocated to the
        //rich guest, enter it into a CPU pool for use by other partitions
        _XDPRINTF_("%s(%u): Proceeding to call xcrichguest_addcpu...\n", __FUNCTION__, (u32)cpuid);
        context_desc = XMHF_SLAB_CALL(xcrichguest_addcpu(xc_richguest_partition_index, cpuid, isbsp));

       	//call hypapp initialization function
        {
            hypapp_env_block_t hypappenvb;

            hypappenvb.runtimephysmembase = (u32)xcbootinfo->physmem_base;
            hypappenvb.runtimesize = (u32)xcbootinfo->size;

            _XDPRINTF_("%s(%u): proceeding to call xmhfhypapp_main...\n", __FUNCTION__, context_desc.cpu_desc.cpu_index);
            XMHF_SLAB_CALL(xmhf_hypapp_initialization(context_desc, hypappenvb));
            _XDPRINTF_("%s(%u): came back into core\n", __FUNCTION__, context_desc.cpu_desc.cpu_index);
        }

        if(!isbsp){
            _XDPRINTF_("%s(%u): starting in partition...\n", __FUNCTION__, context_desc.cpu_desc.cpu_index);
            //increment CPU count
            _cpucount++;
        }

    spin_unlock(&_smpinitialize_lock);


    if(isbsp){
        _XDPRINTF_("%s: BSP: waiting for all APs to get into partition...\n", __FUNCTION__);
        while(_cpucount < (xcbootinfo->cpuinfo_numentries-1));
        xmhf_baseplatform_arch_x86_udelay(6666);
        _XDPRINTF_("%s: BSP: APs all in partition, kickstarting BSP within partition...\n", __FUNCTION__);
    }

	if(!XMHF_SLAB_CALL(xc_api_partition_startcpu(context_desc))){
        _XDPRINTF_("%s(%u):%u: Should never be here. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
        HALT();
	}

}

///////
XMHF_SLAB("xcsmp")

