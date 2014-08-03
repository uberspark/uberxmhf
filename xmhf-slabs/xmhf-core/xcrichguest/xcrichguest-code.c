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
#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcrichguest.h>

#include <xcapi.h>

/* originally in xc-init-richguest.c */

//add given cpu to the rich guest partition
context_desc_t xmhf_richguest_setup(u32 partition_index, u32 cpuid, bool is_bsp){
	context_desc_t context_desc;

	_XDPRINTF_("%s: starting\n", __FUNCTION__);
	
	_XDPRINTF_("%s: proceeding to call xc_api_partition_addcpu\n", __FUNCTION__);
	//add cpu to the richguest partition
	context_desc = XMHF_SLAB_CALL(xc_api_partition_addcpu(partition_index, cpuid, is_bsp));
	_XDPRINTF_("%s: back\n", __FUNCTION__);

	//bail out if we could not add cpu to the rich guest partition
	if(context_desc.cpu_desc.cpu_index == XC_PARTITION_INDEX_INVALID || context_desc.partition_desc.partition_index == XC_PARTITION_INDEX_INVALID){
			_XDPRINTF_("\n%s: could not add cpu to rich guest partition. Halting!", __FUNCTION__);
			return context_desc;
	}

	_XDPRINTF_("%s: proceeding to call xmhf_richguest_setupguestOSstate\n", __FUNCTION__);
	
	//setup guest OS state for partition
	xmhf_richguest_setupguestOSstate(context_desc);
	//_XDPRINTF_("%s: back\n", __FUNCTION__);

	return context_desc;
}


/* originally in init-entry.c */

//we get control here in the context of *each* physical CPU core 
void init_entry(u32 cpuid, bool is_bsp){
	static u32 _xc_startup_hypappmain_counter = 0; 
	static u32 _xc_startup_hypappmain_counter_lock = 1; 
	context_desc_t context_desc;
	static volatile bool bsp_done=false;
	static u32 xc_richguest_partition_index=XC_PARTITION_INDEX_INVALID;

	_XDPRINTF_("\n%s: cpu=%x, is_bsp=%u. Halting\n", __FUNCTION__, cpuid, is_bsp);
	//asm volatile("int $0x03 \r\n");
	//HALT();
	
	//_XDPRINTF_("\nXMHF Tester Finished!\n\n");
	//HALT();
	
	//ensure BSP is the first to grab the lock below
	if(!is_bsp)
		while(!bsp_done);
	
	//serialize execution
    spin_lock(&_xc_startup_hypappmain_counter_lock);

	//[debug]
	_XDPRINTF_("\n%s: cpuid=%08x, is_bsp=%u...\n", __FUNCTION__, cpuid, is_bsp);

	
	//create rich guest partition if we are the BSP
	if(is_bsp){
		_XDPRINTF_("\n%s: proceeding to create rich guest partition (esp=%x)\n", __FUNCTION__, read_esp());
		xc_richguest_partition_index = XMHF_SLAB_CALL(xc_api_partition_create(XC_PARTITION_PRIMARY));
		//_XDPRINTF_("\n%s: came back (esp=%x)\n", __FUNCTION__, read_esp());
		if(xc_richguest_partition_index == XC_PARTITION_INDEX_INVALID){
			_XDPRINTF_("\n%s: Fatal error, could not create rich guest partition!", __FUNCTION__);
			HALT();
		}
		_XDPRINTF_("\n%s: BSP: created rich guest partition %u", __FUNCTION__, xc_richguest_partition_index);
		xmhf_richguest_initialize(xc_richguest_partition_index);
		_XDPRINTF_("\n%s: BSP: initialized rich guest partition %u", __FUNCTION__, xc_richguest_partition_index);
	}
	
	//add cpu to rich guest partition
	//TODO: check if this CPU is allocated to the "rich" guest. if so, pass it on to
	//the rich guest initialization procedure. if the CPU is not allocated to the
	//rich guest, enter it into a CPU pool for use by other partitions
	//xmhf_richguest_addcpu(xc_cpu, xc_partition_richguest_index);
	//cpu_index=xmhf_richguest_setup(cpuid, is_bsp);
	context_desc=xmhf_richguest_setup(xc_richguest_partition_index, cpuid, is_bsp);
	
	if(context_desc.cpu_desc.cpu_index == XC_PARTITION_INDEX_INVALID || context_desc.partition_desc.partition_index == XC_PARTITION_INDEX_INVALID){
		_XDPRINTF_("\n%s: Fatal error, could not add cpu to rich guest. Halting!", __FUNCTION__);
		HALT();
	}
	
	//call hypapp main function
	{
		hypapp_env_block_t hypappenvb;
		
		hypappenvb.runtimephysmembase = (u32)xcbootinfo->physmem_base;  
		hypappenvb.runtimesize = (u32)xcbootinfo->size;
	
		//call app main
		//_XDPRINTF_("\n%s: proceeding to call xmhfhypapp_main on BSP", __FUNCTION__);
		//xc_hypapp_initialization(context_desc, hypappenvb);
		//_XDPRINTF_("\n%s: came back into core", __FUNCTION__);
	}   	
    
    _xc_startup_hypappmain_counter++;
    
    //end serialized execution
    spin_unlock(&_xc_startup_hypappmain_counter_lock);

	//if we are the BSP, signal that APs can go ahead and do the above setup
	if(is_bsp)
		bsp_done=true;

	_XDPRINTF_("\n%s: cpu %x, isbsp=%u, Waiting for all cpus fo cycle through hypapp main", __FUNCTION__, cpuid, is_bsp);
	_XDPRINTF_("\n\n");
	
	//wait for hypapp main to execute on all the cpus
	while(_xc_startup_hypappmain_counter < xcbootinfo->cpuinfo_numentries);

	
	//start cpu in corresponding partition
	_XDPRINTF_("\n%s[%u]: starting in partition...\n", __FUNCTION__, context_desc.cpu_desc.cpu_index);
	//HALT();
	
	//xmhf_partition_start(context_desc.cpu_desc.cpu_index);
	if(!XMHF_SLAB_CALL(xc_api_partition_startcpu(context_desc))){
		_XDPRINTF_("\n%s: should not be here. HALTING!", __FUNCTION__);
		HALT();
	}
}

///////
XMHF_SLAB("init")

XMHF_SLAB_DEFINTERFACE(
	XMHF_SLAB_DEFEXPORTFN(init_entry, XMHF_SLAB_INIT_FNINITENTRY, XMHF_SLAB_FN_RETTYPE_NORMAL)
)
