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

//returns true if a given device vendor_id:device_id is in the slab device exclusion
//list
/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
	requires 0 <= xmhfgeec_slab_info_table[slabid].excl_devices_count <= XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES;

	assigns \nothing;

	ensures isinexclres: \exists integer x; 0 <= x < xmhfgeec_slab_info_table[slabid].excl_devices_count &&
			(xmhfgeec_slab_info_table[slabid].excl_devices[x].vendor_id == vendor_id &&
           xmhfgeec_slab_info_table[slabid].excl_devices[x].device_id == device_id) ==>
			(\result == true);

	ensures isnotinexclres: !(\exists integer x; 0 <= x < xmhfgeec_slab_info_table[slabid].excl_devices_count &&
			(xmhfgeec_slab_info_table[slabid].excl_devices[x].vendor_id == vendor_id &&
           xmhfgeec_slab_info_table[slabid].excl_devices[x].device_id == device_id)) ==>
			(\result == false);

@*/
static bool gp_s2_sdminitdevmap_isdevinexcl(u32 slabid, u32 vendor_id, u32 device_id){
    u32 i;

	/*@
		loop invariant a1: 0 <= i <= xmhfgeec_slab_info_table[slabid].excl_devices_count;
		loop invariant a2: \forall integer x; 0 <= x < i ==>
			!(xmhfgeec_slab_info_table[slabid].excl_devices[x].vendor_id == vendor_id &&
           xmhfgeec_slab_info_table[slabid].excl_devices[x].device_id == device_id);
		loop assigns i;
		loop variant xmhfgeec_slab_info_table[slabid].excl_devices_count - i;
	@*/
    for(i=0; i < xmhfgeec_slab_info_table[slabid].excl_devices_count; i++){
        if(xmhfgeec_slab_info_table[slabid].excl_devices[i].vendor_id == vendor_id &&
           xmhfgeec_slab_info_table[slabid].excl_devices[i].device_id == device_id)
            return true;
    }

    /*@assert a3: \forall integer x; 0 <= x < xmhfgeec_slab_info_table[slabid].excl_devices_count ==>
		!(xmhfgeec_slab_info_table[slabid].excl_devices[x].vendor_id == vendor_id &&
   	   xmhfgeec_slab_info_table[slabid].excl_devices[x].device_id == device_id);
   	@*/
    return false;
}


static void gp_s2_sdminitdevmap_adddeventry(u32 slabid, u32 sysdev_mmioregions_index){

	if( _sda_slab_devicemap[slabid].device_count >= MAX_PLATFORM_DEVICES){
	    _XDPRINTF_("%s: Halting! device_count >= MAX_PLATFORM_DEVICES\n", __func__);
	    CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
	}else{
		_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[_sda_slab_devicemap[slabid].device_count]=sysdev_mmioregions_index;
		_sda_slab_devicemap[slabid].device_count++;
	}

}



static void gp_s2_sdminitdevmap_addalldevstouobj(u32 slabid){
	u32 k;

    for(k=0; k < numentries_sysdev_memioregions; k++){
        if(!gp_s2_sdminitdevmap_isdevinexcl(slabid, sysdev_memioregions[k].vendor_id, sysdev_memioregions[k].device_id)){
        	gp_s2_sdminitdevmap_adddeventry(slabid, k);
        }
    }

}

static void gp_s2_sdminitdevmap_adddevstouobj(u32 slabid, u32 vendor_id, u32 device_id){
	u32 k;

	for(k=0; k < numentries_sysdev_memioregions; k++){
        if( (sysdev_memioregions[k].vendor_id == vendor_id) &&
            (sysdev_memioregions[k].device_id == device_id) &&
            !gp_s2_sdminitdevmap_isdevinexcl(slabid, vendor_id, device_id)
        ){
        	gp_s2_sdminitdevmap_adddeventry(slabid, k);
        }
    }

}



void gp_s2_sdminitdevmap(void){
    u32 i, j, k;

    _XDPRINTF_("%s: numentries_sysdev_mmioregions=%u\n", __func__, numentries_sysdev_memioregions);

    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
        _sda_slab_devicemap[i].device_count = 0;

        for(j=0; j < xmhfgeec_slab_info_table[i].incl_devices_count; j++){
            if( xmhfgeec_slab_info_table[i].incl_devices[j].vendor_id == 0xFFFF &&
               xmhfgeec_slab_info_table[i].incl_devices[j].device_id == 0xFFFF){
            	gp_s2_sdminitdevmap_addalldevstouobj(i);
            }else{
            	gp_s2_sdminitdevmap_adddevstouobj(i, xmhfgeec_slab_info_table[i].incl_devices[j].vendor_id,
            			xmhfgeec_slab_info_table[i].incl_devices[j].device_id);
            }
        }

        #if defined (__DEBUG_SERIAL__)
        //add device SERIAL0 to all the slabs if debugging is enabled
    	gp_s2_sdminitdevmap_adddevstouobj(i, PCI_VENDOR_ID_XMHFGEEC, PCI_DEVICE_ID_XMHFGEEC_SERIAL0);
        #endif // defined

    }

	#if defined (__DEBUG_SERIAL__)
    //debug dump
    {
        u32 i, j;
        for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
            _XDPRINTF_("%s: slab %u...\n", __func__, i);
            for(j=0; j < _sda_slab_devicemap[i].device_count; j++){
                _XDPRINTF_("     device idx=%u\n", _sda_slab_devicemap[i].sysdev_mmioregions_indices[j]);
            }
        }
    }
	#endif // defined


}



