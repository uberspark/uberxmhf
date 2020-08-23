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


//@ghost bool gp_s2_sdminitdevmap_adddevtouobj_coradddeventry[MAX_PLATFORM_DEVICES];
//@ghost bool gp_s2_sdminitdevmap_adddevtouobj_isdevinexcl[MAX_PLATFORM_DEVICES];

/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
	requires 0 <= numentries_sysdev_memioregions <= MAX_PLATFORM_DEVICES;
	requires 0 <= xmhfgeec_slab_info_table[slabid].excl_devices_count <= XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES;

	assigns gp_s2_sdminitdevmap_adddevtouobj_isdevinexcl[0..(numentries_sysdev_memioregions-1)];
	assigns gp_s2_sdminitdevmap_adddevtouobj_coradddeventry[0..(numentries_sysdev_memioregions-1)];

	ensures e2: \forall integer x; 0 <= x < numentries_sysdev_memioregions &&
			((sysdev_memioregions[x].vendor_id == vendor_id) &&
             (sysdev_memioregions[x].device_id == device_id) &&
			 (gp_s2_sdminitdevmap_adddevtouobj_isdevinexcl[x] == false)) ==>
			(gp_s2_sdminitdevmap_adddevtouobj_coradddeventry[x] == true);
	ensures e3: \forall integer x; 0 <= x < numentries_sysdev_memioregions &&
			!((sysdev_memioregions[x].vendor_id == vendor_id) &&
             (sysdev_memioregions[x].device_id == device_id) &&
			 (gp_s2_sdminitdevmap_adddevtouobj_isdevinexcl[x] == false)) ==>
			(gp_s2_sdminitdevmap_adddevtouobj_coradddeventry[x] == false);
@*/
void gp_s2_sdminitdevmap_adddevtouobj(uint32_t slabid, uint32_t vendor_id, uint32_t device_id){
	uint32_t k;
	bool isdevinexcl;

	/*@
		loop invariant k1: 0 <= k <= numentries_sysdev_memioregions;
		loop invariant k2: \forall integer x; 0 <= x < k &&
			((sysdev_memioregions[x].vendor_id == vendor_id) &&
             (sysdev_memioregions[x].device_id == device_id) &&
			 (gp_s2_sdminitdevmap_adddevtouobj_isdevinexcl[x] == false)) ==>
			(gp_s2_sdminitdevmap_adddevtouobj_coradddeventry[x] == true);
		loop invariant k3: \forall integer x; 0 <= x < k &&
			!((sysdev_memioregions[x].vendor_id == vendor_id) &&
             (sysdev_memioregions[x].device_id == device_id) &&
			 (gp_s2_sdminitdevmap_adddevtouobj_isdevinexcl[x] == false)) ==>
			(gp_s2_sdminitdevmap_adddevtouobj_coradddeventry[x] == false);
		loop assigns k;
		loop assigns isdevinexcl;
		loop assigns gp_s2_sdminitdevmap_adddevtouobj_isdevinexcl[0..(numentries_sysdev_memioregions-1)];
		loop assigns gp_s2_sdminitdevmap_adddevtouobj_coradddeventry[0..(numentries_sysdev_memioregions-1)];
		loop variant numentries_sysdev_memioregions - k;
	@*/

	for(k=0; k < numentries_sysdev_memioregions; k++){
        isdevinexcl = gp_s2_sdminitdevmap_isdevinexcl(slabid, vendor_id, device_id);
    	//@ghost gp_s2_sdminitdevmap_adddevtouobj_isdevinexcl[k] = isdevinexcl;
        //@assert (gp_s2_sdminitdevmap_adddevtouobj_isdevinexcl[k] == true) || (gp_s2_sdminitdevmap_adddevtouobj_isdevinexcl[k] == false);

		if( (sysdev_memioregions[k].vendor_id == vendor_id) &&
            (sysdev_memioregions[k].device_id == device_id) &&
            !isdevinexcl
        ){
        	gp_s2_sdminitdevmap_adddeventry(slabid, k);
        	//@ghost gp_s2_sdminitdevmap_adddevtouobj_coradddeventry[k] = true;
        }else{
        	//@ghost gp_s2_sdminitdevmap_adddevtouobj_coradddeventry[k] = false;
        }
    }

}

