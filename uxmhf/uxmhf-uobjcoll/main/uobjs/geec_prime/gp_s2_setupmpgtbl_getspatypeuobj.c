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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
// #include <xmhfgeec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_prime.h>


//@ghost bool gisiotbl, gisdevicemmio;
/*@
	requires 0 <= slab_index < XMHFGEEC_TOTAL_SLABS ;
	requires \forall uint32_t x; 0 <= x < MAX_PLATFORM_CPUS ==> (_sda_slab_devicemap[slab_index].sysdev_mmioregions_indices[x] < MAX_PLATFORM_DEVICES);
	requires 0 <= _sda_slab_devicemap[slab_index].device_count < MAX_PLATFORM_DEVICES;
	assigns gisiotbl, gisdevicemmio;
	ensures ( (\result == _SLAB_SPATYPE_GEEC_PRIME_IOTBL) ||
		(\result == _SLAB_SPATYPE_SLAB_CODE) ||
		(\result == _SLAB_SPATYPE_SLAB_DATA) ||
		(\result == _SLAB_SPATYPE_SLAB_STACK) ||
		(\result == _SLAB_SPATYPE_SLAB_DMADATA) ||
		(\result == _SLAB_SPATYPE_SLAB_DEVICEMMIO) ||
		(\result == _SLAB_SPATYPE_OTHER) );
	ensures ( (gisiotbl == true) ) ==> (\result == _SLAB_SPATYPE_GEEC_PRIME_IOTBL);
	ensures ( (gisiotbl == false) &&  (spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_end)) ==> (\result == _SLAB_SPATYPE_SLAB_CODE);
	ensures ( (gisiotbl == false) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_end) &&
		  (spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_end)
		) ==> (\result == _SLAB_SPATYPE_SLAB_DATA);
	ensures ( (gisiotbl == false) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_end) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_end) &&
		  (spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_end)
		) ==> (\result == _SLAB_SPATYPE_SLAB_STACK);
	ensures ( (gisiotbl == false) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_end) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_end) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_end) &&
		  (spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[3].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[3].addr_end)
		) ==> (\result == _SLAB_SPATYPE_SLAB_DMADATA);
	ensures ( (gisiotbl == false) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_end) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_end) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_end) &&
		  !(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[3].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[3].addr_end) &&
		  (gisdevicemmio == true)
		) ==> (\result == _SLAB_SPATYPE_SLAB_DEVICEMMIO);


@*/
uint32_t gp_s2_setupmpgtbl_getspatypeuobj(uint32_t slab_index, uint32_t spa){
		bool isiotbl, isdevicemmio;

		isiotbl = gp_s2_setupmpgtbl_getspatypeuobj_isiotbl(slab_index, spa);
		//@ghost gisiotbl = isiotbl;
		isdevicemmio = gp_s2_setupmpgtbl_getspatypeuobj_ismmio(slab_index, spa);
		//@ghost gisdevicemmio = isdevicemmio;

		if(isiotbl)
		    return _SLAB_SPATYPE_GEEC_PRIME_IOTBL;
		if(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[0].addr_end)
		    return _SLAB_SPATYPE_SLAB_CODE;
		if(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[1].addr_end)
		    return _SLAB_SPATYPE_SLAB_DATA;
		if(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[2].addr_end)
		    return _SLAB_SPATYPE_SLAB_STACK;
		if(spa >= xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[3].addr_start && spa < xmhfgeec_slab_info_table[slab_index].slab_physmem_extents[3].addr_end)
		    return _SLAB_SPATYPE_SLAB_DMADATA;
		if(isdevicemmio)
		    return _SLAB_SPATYPE_SLAB_DEVICEMMIO;

		return _SLAB_SPATYPE_OTHER;
}
