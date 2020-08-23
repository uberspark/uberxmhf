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


/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS ;
	requires \forall uint32_t x; 0 <= x < MAX_PLATFORM_CPUS ==> (_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x] < MAX_PLATFORM_DEVICES);
	requires 0 <= _sda_slab_devicemap[slabid].device_count < MAX_PLATFORM_DEVICES;
	assigns \nothing;
	ensures (\result == true) || (\result == false) ;
	ensures (\forall uint32_t x, uint32_t y; ( (0 <= x < _sda_slab_devicemap[slabid].device_count) &&
					   (0 <= y < PCI_CONF_MAX_BARS) ) ==> !(sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x]].memioextents[y].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_MEM &&
			(spa >= sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x]].memioextents[y].addr_start &&
			    spa < sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x]].memioextents[y].addr_end) )) ==> 	(\result == false);

@*/
bool gp_s2_setupmpgtbl_getspatypeuobj_ismmio(uint32_t slabid, uint32_t spa){
    uint32_t i, j;

	/*@
		loop invariant c1: 0 <= i <= _sda_slab_devicemap[slabid].device_count;
		loop assigns i, j;
		loop variant _sda_slab_devicemap[slabid].device_count - i;
	@*/
	for(i=0; i < _sda_slab_devicemap[slabid].device_count; i++){

		/*@
			loop invariant c2: 0 <= j <= PCI_CONF_MAX_BARS;
			loop invariant c3: \forall integer x; 0 <= x < j ==> (!(sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[i]].memioextents[x].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_MEM &&
			(spa >= sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[i]].memioextents[x].addr_start &&
			    spa < sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[i]].memioextents[x].addr_end) ));
			loop assigns j;
			loop variant PCI_CONF_MAX_BARS - j;
		@*/
		for(j=0; j < PCI_CONF_MAX_BARS; j++){
		    if(sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[i]].memioextents[j].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_MEM &&
			(spa >= sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[i]].memioextents[j].addr_start &&
			    spa < sysdev_memioregions[_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[i]].memioextents[j].addr_end) )
			    return true;
		}
	}

    return false;
}
