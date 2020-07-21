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
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_iotbl.h>

//@ghost bool gp_s2_setupiotblug_helper_invokedportaccess[PCI_CONF_MAX_BARS];
/*@
	requires (slabid >= XMHFGEEC_UGSLAB_BASE_IDX && slabid <= XMHFGEEC_UGSLAB_MAX_IDX);
	requires sysdev_memioregions_index < MAX_PLATFORM_DEVICES;
	assigns gp_s2_setupiotblug_helper_invokedportaccess[0..(PCI_CONF_MAX_BARS-1)];
	ensures \forall integer x; 0 <= x < (PCI_CONF_MAX_BARS-1) ==> (
				((sysdev_memioregions[sysdev_memioregions_index].memioextents[x].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_IO &&
				(sysdev_memioregions[sysdev_memioregions_index].memioextents[x].addr_start <= sysdev_memioregions[sysdev_memioregions_index].memioextents[x].addr_end))) ==>
				(gp_s2_setupiotblug_helper_invokedportaccess[x] == true)
						);
@*/
static inline void gp_s2_setupiotblug_helper(uint32_t slabid, uint32_t sysdev_memioregions_index){
	uint32_t k, portnum;

	/*@
		loop invariant b1: 0 <= k <= PCI_CONF_MAX_BARS;
		loop invariant b2: \forall integer x; 0 <= x < k ==> (
				((sysdev_memioregions[sysdev_memioregions_index].memioextents[x].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_IO &&
				(sysdev_memioregions[sysdev_memioregions_index].memioextents[x].addr_start <= sysdev_memioregions[sysdev_memioregions_index].memioextents[x].addr_end))) ==>
				(gp_s2_setupiotblug_helper_invokedportaccess[x] == true)
						);
		loop assigns k;
		loop assigns portnum;
		loop assigns gp_s2_setupiotblug_helper_invokedportaccess[0..(PCI_CONF_MAX_BARS-1)];
		loop variant PCI_CONF_MAX_BARS - k;
	@*/
	for(k=0; k < PCI_CONF_MAX_BARS; k++){
		if(sysdev_memioregions[sysdev_memioregions_index].memioextents[k].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_IO &&
			(sysdev_memioregions[sysdev_memioregions_index].memioextents[k].addr_start <= sysdev_memioregions[sysdev_memioregions_index].memioextents[k].addr_end)){

			/*@
				loop invariant c1: sysdev_memioregions[sysdev_memioregions_index].memioextents[k].addr_start <= portnum <= sysdev_memioregions[sysdev_memioregions_index].memioextents[k].addr_end;
				loop assigns portnum;
				loop variant sysdev_memioregions[sysdev_memioregions_index].memioextents[k].addr_end - portnum;
			@*/
			for(portnum= sysdev_memioregions[sysdev_memioregions_index].memioextents[k].addr_start;
				portnum < sysdev_memioregions[sysdev_memioregions_index].memioextents[k].addr_end; portnum++){
				{
					slab_params_t spl;
					uapi_iotbl_setupiotblugportaccess_t *ps = (uapi_iotbl_setupiotblugportaccess_t *)spl.in_out_params;

					spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
					spl.dst_slabid = UOBJ_UAPI_IOTBL;
					spl.cpuid = 0;
					spl.dst_uapifn = UXMHF_UAPI_IOTBL_SETUPIOTBLUGPORTACCESS;

					ps->ugslabiobitmap_idx = slabid;
					ps->port = portnum;
					ps->port_size = 1;

					XMHF_SLAB_CALLNEW(&spl);
				}
			}

			//@ghost gp_s2_setupiotblug_helper_invokedportaccess[k] = true;
		}
	}
}



//@ghost bool gp_s2_setupiotblug_invokedhelper[MAX_PLATFORM_DEVICES];
/*@
	requires (slabid >= XMHFGEEC_UGSLAB_BASE_IDX && slabid <= XMHFGEEC_UGSLAB_MAX_IDX);
	requires _sda_slab_devicemap[slabid].device_count < MAX_PLATFORM_DEVICES;
	requires  \forall integer x; 0 <= x < MAX_PLATFORM_DEVICES ==> (_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x] < MAX_PLATFORM_DEVICES);
	assigns gp_s2_setupiotblug_invokedhelper[0..(_sda_slab_devicemap[slabid].device_count-1)];
	assigns gp_rwdatahdr.gp_ugslab_iobitmap[(slabid - XMHFGEEC_UGSLAB_BASE_IDX)][0..(3*PAGE_SIZE_4K-1)];
	assigns gp_s2_setupiotblug_helper_invokedportaccess[0..(PCI_CONF_MAX_BARS-1)];
	ensures \forall integer x; 0 <= x < (_sda_slab_devicemap[slabid].device_count-1) ==>
				(gp_s2_setupiotblug_invokedhelper[x] == true);
@*/
void gp_s2_setupiotblug(uint32_t slabid){
	uint32_t i;

        {
        	slab_params_t spl;
        	uapi_iotbl_initiotbl_t *ps = (uapi_iotbl_initiotbl_t *)spl.in_out_params;

        	spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
        	spl.dst_slabid = UOBJ_UAPI_IOTBL;
        	spl.cpuid = 0;
        	spl.dst_uapifn = UXMHF_UAPI_IOTBL_INITIOTBL;

        	ps->dst_slabid = slabid;

        	XMHF_SLAB_CALLNEW(&spl);
        }
    	/*@
		loop invariant a1: 0 <= i <= _sda_slab_devicemap[slabid].device_count;
		loop invariant a2: \forall integer x; 0 <= x < i ==>
				(gp_s2_setupiotblug_invokedhelper[x] == true);
		loop assigns i;
		loop assigns gp_s2_setupiotblug_invokedhelper[0..(_sda_slab_devicemap[slabid].device_count-1)];
		loop assigns gp_s2_setupiotblug_helper_invokedportaccess[0..(PCI_CONF_MAX_BARS-1)];
		loop variant _sda_slab_devicemap[slabid].device_count - i;
	@*/
	for(i=0; i < _sda_slab_devicemap[slabid].device_count; i++){
		gp_s2_setupiotblug_helper(slabid, _sda_slab_devicemap[slabid].sysdev_mmioregions_indices[i]);
		//@ghost gp_s2_setupiotblug_invokedhelper[i] = true;
	}
}


