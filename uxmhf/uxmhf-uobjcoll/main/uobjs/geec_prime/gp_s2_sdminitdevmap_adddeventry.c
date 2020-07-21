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
#include <uberspark/include/uberspark.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_prime.h>


/*@
	ghost bool gp_s2_sdminitdevmap_adddeventry_syshalt = false;
@*/
/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;

	behavior addentry:
		assumes (0 <= _sda_slab_devicemap[slabid].device_count < MAX_PLATFORM_DEVICES);
		assigns gp_s2_sdminitdevmap_adddeventry_syshalt;
		assigns _sda_slab_devicemap[slabid].sysdev_mmioregions_indices[_sda_slab_devicemap[slabid].device_count];
		assigns _sda_slab_devicemap[slabid].device_count;
		ensures gp_s2_sdminitdevmap_adddeventry_syshalt == false;
		ensures _sda_slab_devicemap[slabid].sysdev_mmioregions_indices[\at(_sda_slab_devicemap[slabid].device_count, Pre)] == sysdev_mmioregions_index;
		ensures (_sda_slab_devicemap[slabid].device_count == (\at(_sda_slab_devicemap[slabid].device_count, Pre) + 1));
		ensures (_sda_slab_devicemap[slabid].device_count <= MAX_PLATFORM_DEVICES);

	behavior invalidhalt:
		assumes ( _sda_slab_devicemap[slabid].device_count >= MAX_PLATFORM_DEVICES);
		assigns gp_s2_sdminitdevmap_adddeventry_syshalt;
		ensures gp_s2_sdminitdevmap_adddeventry_syshalt == true;

	complete behaviors;
	disjoint behaviors;
@*/
void gp_s2_sdminitdevmap_adddeventry(uint32_t slabid, uint32_t sysdev_mmioregions_index){

	if( _sda_slab_devicemap[slabid].device_count >= MAX_PLATFORM_DEVICES){
	    _XDPRINTF_("%s: Halting! device_count >= MAX_PLATFORM_DEVICES\n", __func__);
	    CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
		//@ghost gp_s2_sdminitdevmap_adddeventry_syshalt = true;
	}else{
		//@ghost gp_s2_sdminitdevmap_adddeventry_syshalt = false;
		_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[_sda_slab_devicemap[slabid].device_count]=sysdev_mmioregions_index;
		_sda_slab_devicemap[slabid].device_count++;
	}
}


