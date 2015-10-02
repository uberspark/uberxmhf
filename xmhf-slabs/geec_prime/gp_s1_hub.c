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
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <geec_prime.h>
#include <geec_sentinel.h>
#include <uapi_slabmempgtbl.h>
#include <uapi_slabdevpgtbl.h>
#include <xc_init.h>


////////////////////////////////////////////////////////////
// setup slab info

void xmhfhic_arch_setup_slab_info(void){





}





void gp_s1_hub(void){


	//initialize debugging early on
	xmhf_debug_init((char *)&xcbootinfo->debugcontrol_buffer);


	//[debug] print relevant startup info.
	_XDPRINTF_("%s: alive and starting...\n", __func__);

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

	//print out slab table
	{
		u32 i, j;

		for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
			_XDPRINTF_("slab %u: dumping slab header\n", i);
			_XDPRINTF_("	slabtype=%08x\n", xmhfgeec_slab_info_table[i].slabtype);
			_XDPRINTF_("	slab_inuse=%s\n", ( xmhfgeec_slab_info_table[i].slab_inuse ? "true" : "false") );
			_XDPRINTF_("	slab_callcaps=%08x\n", xmhfgeec_slab_info_table[i].slab_callcaps);
			//_XDPRINTF_("	slab_devices=%s\n", ( xmhfgeec_slab_info_table[i].slab_devices.desc_valid ? "true" : "false") );
			_XDPRINTF_("	incl_devices_count=%u\n", xmhfgeec_slab_info_table[i].incl_devices_count );
			for(j=0; j < xmhfgeec_slab_info_table[i].incl_devices_count; j++)
				_XDPRINTF_("        vendor_id=%x, device_id=%x\n",
					   xmhfgeec_slab_info_table[i].incl_devices[j].vendor_id,
					   xmhfgeec_slab_info_table[i].incl_devices[j].device_id);
			_XDPRINTF_("	excl_devices_count=%u\n", xmhfgeec_slab_info_table[i].excl_devices_count );
			for(j=0; j < xmhfgeec_slab_info_table[i].excl_devices_count; j++)
				_XDPRINTF_("        vendor_id=%x, device_id=%x\n",
					   xmhfgeec_slab_info_table[i].excl_devices[j].vendor_id,
					   xmhfgeec_slab_info_table[i].excl_devices[j].device_id);

			_XDPRINTF_("	slab_pgtblbase=%x\n", ( xmhfgeec_slab_info_table[i].mempgtbl_cr3) );
			_XDPRINTF_("	slab_iotblbase=%x\n", ( xmhfgeec_slab_info_table[i].iotbl_base) );
			_XDPRINTF_("  slab_code(%08x-%08x)\n", xmhfgeec_slab_info_table[i].slab_physmem_extents[0].addr_start, xmhfgeec_slab_info_table[i].slab_physmem_extents[0].addr_end);
			_XDPRINTF_("  slab_data(%08x-%08x)\n", xmhfgeec_slab_info_table[i].slab_physmem_extents[1].addr_start, xmhfgeec_slab_info_table[i].slab_physmem_extents[1].addr_end);
			_XDPRINTF_("  slab_stack(%08x-%08x)\n", xmhfgeec_slab_info_table[i].slab_physmem_extents[2].addr_start, xmhfgeec_slab_info_table[i].slab_physmem_extents[2].addr_end);
			_XDPRINTF_("  slab_dmadata(%08x-%08x)\n", xmhfgeec_slab_info_table[i].slab_physmem_extents[3].addr_start, xmhfgeec_slab_info_table[i].slab_physmem_extents[3].addr_end);
			_XDPRINTF_("  slab_entrystub=%08x\n", xmhfgeec_slab_info_table[i].entrystub);

		}
	}


	//sanity check hardware requirements
	gp_s1_chkreq();

#if defined (__DRT__)
	//post DRT cleanup first
	gp_s1_postdrt();
#endif	//__DRT__


	//initialize platform bus
	xmhfhw_platform_bus_init();

	//check ACPI subsystem
	{
		ACPI_RSDP rsdp;
		if(!xmhfhw_platform_x86pc_acpi_getRSDP(&rsdp)){
			_XDPRINTF_("%s: ACPI RSDP not found, Halting!\n", __func__);
			HALT();
		}
	}


	gp_s2_entry();
}

