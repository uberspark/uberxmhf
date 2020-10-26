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
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec_prime.h>


/*@
	requires ( \forall integer i, integer j; (0 <= i < XMHFGEEC_TOTAL_SLABS) ==> (_sda_slab_devicemap[i].device_count < MAX_PLATFORM_DEVICES) );
	requires ( \forall integer i, integer j; (0 <= i < XMHFGEEC_TOTAL_SLABS) && (0 <= j < _sda_slab_devicemap[i].device_count) ==> (0 <= _sda_slab_devicemap[i].sysdev_mmioregions_indices[j] < MAX_PLATFORM_DEVICES) );

	assigns \nothing;

	ensures foundbdf: ( \forall integer i, integer j; (0 <= i < XMHFGEEC_TOTAL_SLABS) && (0 <= j < _sda_slab_devicemap[i].device_count)
		&& (
				sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[j]) ].b == bus &&
				sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[j]) ].d == dev &&
				sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[j]) ].f == func
			)
		) ==> (0 <= \result < XMHFGEEC_TOTAL_SLABS );

	ensures notfoundbdf: ( \forall integer i, integer j; (0 <= i < XMHFGEEC_TOTAL_SLABS) && (0 <= j < _sda_slab_devicemap[i].device_count)
		&& !(
				sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[j]) ].b == bus &&
				sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[j]) ].d == dev &&
				sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[j]) ].f == func
			)
		) ==> (\result == 0xFFFFFFFFUL );

@*/
uint32_t gp_s2_sdadoalloc_getuobjfordev(uint32_t bus, uint32_t dev, uint32_t func){
    uint32_t i;
    uint32_t j;

	/*@
		loop invariant a1: 0 <= i <= XMHFGEEC_TOTAL_SLABS;
		loop invariant a4:	\forall integer x, integer y; 0 <= x < i && 0 <= y < _sda_slab_devicemap[x].device_count ==> (
			!( sysdev_memioregions[ (_sda_slab_devicemap[x].sysdev_mmioregions_indices[y]) ].b == bus &&
				sysdev_memioregions[ (_sda_slab_devicemap[x].sysdev_mmioregions_indices[y]) ].d == dev &&
				sysdev_memioregions[ (_sda_slab_devicemap[x].sysdev_mmioregions_indices[y]) ].f == func)
		);
		loop assigns i;
		loop assigns j;
		loop variant XMHFGEEC_TOTAL_SLABS - i;
	@*/
    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
    	/*@
    		loop invariant a2: 0 <= j <= _sda_slab_devicemap[i].device_count;
			loop invariant a3:	\forall integer y; 0 <= y < j ==> (
				!( sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[y]) ].b == bus &&
    				sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[y]) ].d == dev &&
					sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[y]) ].f == func)
			);
    		loop assigns j;
    		loop variant (_sda_slab_devicemap[i].device_count) - j;
    	@*/
    	for (j=0; j < _sda_slab_devicemap[i].device_count; j++){

    		if ( sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[j]) ].b == bus &&
    				sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[j]) ].d == dev &&
					sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[j]) ].f == func)
    			return i;
       	}
    }


	/*@assert ( \forall integer i, integer j; (0 <= i < XMHFGEEC_TOTAL_SLABS) && (0 <= j < _sda_slab_devicemap[i].device_count) ==>
			!(
				sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[j]) ].b == bus &&
				sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[j]) ].d == dev &&
				sysdev_memioregions[ (_sda_slab_devicemap[i].sysdev_mmioregions_indices[j]) ].f == func
			)
	);
	@*/
    return 0xFFFFFFFFUL;
}


