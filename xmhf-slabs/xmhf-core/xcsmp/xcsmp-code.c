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

bool xcsmp_entry(void){

#if defined (__DMAP__)
	xcsmp_arch_dmaprot_reinitialize();
#endif

	if( xcsmp_arch_smpinitialize() ){
		_XDPRINTF_("\nRuntime: We should NEVER get here!");
		HALT();
	}

}

//executes in the context of each physical CPU
void xcsmp_smpstart(u32 cpuid, bool isbsp){
    static volatile bool bspdone=false;
    static u32 _smpinitialize_lock = 1;
    context_desc_t context_desc;

    if(!isbsp){
        //this is an AP, so we wait until BSP gives us go ahead
        _XDPRINTF_("%s: AP: cpuid=%u, is_bsp=%u, rsp=%016llx. Waiting to proceed...\n", __FUNCTION__, (u32)cpuid, (u32)isbsp, read_rsp());
        while(!bspdone);
        _XDPRINTF_("%s: AP: cpuid=%u, is_bsp=%u, rsp=%016llx. Moving on...\n", __FUNCTION__, (u32)cpuid, (u32)isbsp, read_rsp());
    }else{
        _XDPRINTF_("%s: BSP: cpuid=%u, is_bsp=%u, rsp=%016llx\n", __FUNCTION__, (u32)cpuid, (u32)isbsp, read_rsp());
        _XDPRINTF_("%s: BSP going first...\n", __FUNCTION__);
    }

    //serialize execution
    spin_lock(&_smpinitialize_lock);

        //increment CPU count
        _cpucount++;

        //initialize CPU
        xcsmp_arch_initializecpu(cpuid, isbsp);


        _XDPRINTF_("%s(%u): Proceeding to call xcrichguest_entry...\n", __FUNCTION__, (u32)cpuid);
        context_desc = XMHF_SLAB_CALL(xcrichguest_entry(cpuid, isbsp));

    spin_unlock(&_smpinitialize_lock);


    //if this is the BSP, then signal that APs can proceed
    if(isbsp)
        bspdone=true;

	_XDPRINTF_("%s(%u): isbsp=%u, syncing...\n", __FUNCTION__, cpuid, isbsp);
    while(_cpucount < xcbootinfo->cpuinfo_numentries);

	//start cpu in corresponding partition
	_XDPRINTF_("%s(%u): starting in partition...\n", __FUNCTION__, context_desc.cpu_desc.cpu_index);

	if(!XMHF_SLAB_CALL(xc_api_partition_startcpu(context_desc))){
        _XDPRINTF_("%s(%u):%u: Should never be here. Halting!\n", __FUNCTION__, (u32)cpuid, __LINE__);
        HALT();
	}

}

///////
XMHF_SLAB("initbs")

