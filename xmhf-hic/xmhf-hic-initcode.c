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

#include <xcprimeon.h>

#include <xcsmp.h>
#include <testslab1.h>


void xmhfhic_entry(void){
    u64 pgtblbase;

	//initialize debugging early on
	xmhfhw_platform_serial_init((char *)&xcbootinfo->debugcontrol_buffer);

/*	//store runtime physical and virtual base addresses along with size
	//xcbootinfo->physmem_base = __TARGET_BASE_SL;
	//xcbootinfo->virtmem_base = __TARGET_BASE_SL;
	//xcbootinfo->size = xcbootinfo->size;
	xcbootinfo->xmhf_base = __TARGET_BASE_XMHF;
	xcbootinfo->xmhf_size = __TARGET_SIZE_XMHF;*/


	//[debug] print relevant startup info.
	_XDPRINTF_("%s: alive and starting...\n", __FUNCTION__);

	_XDPRINTF_("    xcbootinfo at = 0x%08x\n", (u32)xcbootinfo);
	_XDPRINTF_("	numE820Entries=%u\n", xcbootinfo->memmapinfo_numentries);
	_XDPRINTF_("	system memory map buffer at 0x%08x\n", (u32)&xcbootinfo->memmapinfo_buffer);
	_XDPRINTF_("	numCPUEntries=%u\n", xcbootinfo->cpuinfo_numentries);
	_XDPRINTF_("	cpuinfo buffer at 0x%08x\n", (u32)&xcbootinfo->cpuinfo_buffer);
	_XDPRINTF_("	XMHF size= %u bytes\n", __TARGET_SIZE_XMHF);
	_XDPRINTF_("	OS bootmodule at 0x%08x, size=%u bytes\n",
		xcbootinfo->richguest_bootmodule_base, xcbootinfo->richguest_bootmodule_size);
    _XDPRINTF_("\tcmdline = \"%s\"\n", xcbootinfo->cmdline_buffer);
	_XDPRINTF_("SL: runtime at 0x%08x; size=0x%08x bytes\n", __TARGET_BASE_XMHF, __TARGET_SIZE_XMHF);
	_XDPRINTF_("SL: XMHF_BOOTINFO at 0x%08x, magic=0x%08x\n", (u32)xcbootinfo, xcbootinfo->magic);
	HALT_ON_ERRORCOND(xcbootinfo->magic == RUNTIME_PARAMETER_BLOCK_MAGIC);
 	_XDPRINTF_("\nNumber of E820 entries = %u", xcbootinfo->memmapinfo_numentries);
	{
		u32 i;
		for(i=0; i < (u32)xcbootinfo->memmapinfo_numentries; i++){
			_XDPRINTF_("\n0x%08x%08x, size=0x%08x%08x (%u)",
			  xcbootinfo->memmapinfo_buffer[i].baseaddr_high, xcbootinfo->memmapinfo_buffer[i].baseaddr_low,
			  xcbootinfo->memmapinfo_buffer[i].length_high, xcbootinfo->memmapinfo_buffer[i].length_low,
			  xcbootinfo->memmapinfo_buffer[i].type);
		}
  	}

	/*//initialize cpu table and total platform CPUs
	{
	    u32 i;
	    for(i=0; i < xcbootinfo->cpuinfo_numentries; i++){
            _cputable[i].cpuid = xcbootinfo->cpuinfo_buffer[i].lapic_id;
            _cputable[i].cpu_index = i;
        }
        _totalcpus=xcbootinfo->cpuinfo_numentries;
	}*/



    //sanity check HIC (hardware) requirements
    xmhfhic_arch_sanity_check_requirements();

    //setup slab system device allocation
    xmhfhic_arch_setup_slab_device_allocation();

    //setup hypervisor slab page tables
    xmhfhic_arch_setup_hypervisor_slab_page_tables();

    //seutp guest slab page tables
    xmhfhic_arch_setup_guest_slab_page_tables();


    //setup base CPU data structures
    xmhfhic_arch_setup_base_cpu_data_structures();

    //setup SMP and move on to xmhfhic_smp_entry
    xmhfhic_arch_switch_to_smp();

    //we should never get here
    _XDPRINTF_("Should never be here. Halting!\n");
    HALT();
}


void xmhfhic_smp_entry(u64 cpuid){
    bool isbsp = (cpuid & 0x8000000000000000ULL) ? true : false;

    _XDPRINTF_("%s[%u,%u]: rsp=%016llx. Starting...\n",
            __FUNCTION__, cpuid, isbsp, read_rsp());

    //setup CPU state for HIC
    //if(isbsp){
        xmhf_hic_arch_setup_cpu_state(cpuid);
    //}


    //if(isbsp){
    //relinquish HIC initialization and move on to the first slab
    xmhfhic_arch_relinquish_control_to_init_slab(cpuid);
    //}

    _XDPRINTF_("%s[%u,%u]: Should never be here. Halting!\n", __FUNCTION__, cpuid, isbsp);
    HALT();

}

#if 0

    //debug
    _XDPRINTF_("Halting!\n");
    _XDPRINTF_("XMHF Tester Finished!\n");
    HALT();

#endif // 0
