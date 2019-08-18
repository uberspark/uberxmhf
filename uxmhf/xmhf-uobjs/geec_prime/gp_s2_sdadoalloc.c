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

//@ghost uint32_t uobjfordev[MAX_PLATFORM_DEVICES];
//@ghost bool invokedgetuobjfordev[MAX_PLATFORM_DEVICES];
//@ghost bool invokedsdabinddevice[MAX_PLATFORM_DEVICES];
/*@
	requires 0 <= numentries_sysdev_memioregions < MAX_PLATFORM_DEVICES;
	assigns uobjfordev[0..(numentries_sysdev_memioregions-1)];
	assigns invokedgetuobjfordev[0..(numentries_sysdev_memioregions-1)];
	assigns invokedsdabinddevice[0..(numentries_sysdev_memioregions-1)];
	ensures \forall integer x; 0 <= x < numentries_sysdev_memioregions ==> (
			(
				(sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_GENERAL ||
				sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE ||
				sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN)
			)==> (invokedgetuobjfordev[x] == true) );
	ensures \forall integer x; 0 <= x < numentries_sysdev_memioregions ==> (
			(
				(sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_GENERAL ||
				sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE ||
				sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN)
				&&
				(uobjfordev[x] == 0xFFFFFFFFUL || (uobjfordev[x] >= XMHFGEEC_TOTAL_SLABS))
			)==> (invokedsdabinddevice[x] == false) );
	ensures \forall integer x; 0 <= x < numentries_sysdev_memioregions ==> (
			(
				(sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_GENERAL ||
				sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE ||
				sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN)
				&&
				!(uobjfordev[x] == 0xFFFFFFFFUL || (uobjfordev[x] >= XMHFGEEC_TOTAL_SLABS))
			)==> (invokedsdabinddevice[x] == true) );

@*/
void gp_s2_sdadoalloc(void){
	uint32_t i;
	uint32_t dst_slabid;


		/*@
		loop invariant a1: 0 <= i <= numentries_sysdev_memioregions;
		loop invariant a2: \forall integer x; 0 <= x < i ==> (
			(
				(sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_GENERAL ||
				sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE ||
				sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN)
			)==> (invokedgetuobjfordev[x] == true) );
		loop invariant a3: \forall integer x; 0 <= x < i ==> (
			(
				(sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_GENERAL ||
				sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE ||
				sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN)
				&&
				(uobjfordev[x] == 0xFFFFFFFFUL || (uobjfordev[x] >= XMHFGEEC_TOTAL_SLABS))
			)==> (invokedsdabinddevice[x] == false) );
		loop invariant a4: \forall integer x; 0 <= x < i ==> (
			(
				(sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_GENERAL ||
				sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE ||
				sysdev_memioregions[x].dtype == SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN)
				&&
				!(uobjfordev[x] == 0xFFFFFFFFUL || (uobjfordev[x] >= XMHFGEEC_TOTAL_SLABS))
			)==> (invokedsdabinddevice[x] == true) );
		loop assigns i;
		loop assigns dst_slabid;
		loop assigns uobjfordev[0..(numentries_sysdev_memioregions-1)];
		loop assigns invokedgetuobjfordev[0..(numentries_sysdev_memioregions-1)];
		loop assigns invokedsdabinddevice[0..(numentries_sysdev_memioregions-1)];
		loop variant numentries_sysdev_memioregions - i;
	@*/
	for(i=0; i <numentries_sysdev_memioregions; i++){
		if(sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_GENERAL ||
		   sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE ||
		   sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN){

			dst_slabid = gp_s2_sdadoalloc_getuobjfordev(sysdev_memioregions[i].b,
								sysdev_memioregions[i].d,
								sysdev_memioregions[i].f);
			//@ghost invokedgetuobjfordev[i] = true;
			//@ghost uobjfordev[i] = dst_slabid;

			if(dst_slabid == 0xFFFFFFFFUL){
				_XDPRINTF_("Could not find slab for device %x:%x:%x (vid:did=%x:%x, type=%x), skipping...\n", sysdev_memioregions[i].b,
						   sysdev_memioregions[i].d, sysdev_memioregions[i].f, sysdev_memioregions[i].vendor_id,
						   sysdev_memioregions[i].device_id, sysdev_memioregions[i].dtype);

				//@ghost invokedsdabinddevice[i] = false;
			}else{
				gp_s2_sdabinddevice(dst_slabid, vtd_pagewalk_level,
						sysdev_memioregions[i].b, sysdev_memioregions[i].d, sysdev_memioregions[i].f);

				_XDPRINTF_("Allocated device %x:%x:%x (vid:did=%x:%x, type=%x) to slab %u...\n", sysdev_memioregions[i].b,
						   sysdev_memioregions[i].d, sysdev_memioregions[i].f, sysdev_memioregions[i].vendor_id,
						   sysdev_memioregions[i].device_id, sysdev_memioregions[i].dtype, dst_slabid);
				//@ghost invokedsdabinddevice[i] = true;
			}
		}
	}
}

