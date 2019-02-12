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

//@ghost bool gp_s2_sdminitdevmap_coraddalldevstouobj[XMHFGEEC_TOTAL_SLABS];
//@ghost bool gp_s2_sdminitdevmap_coradddevtouobj[XMHFGEEC_TOTAL_SLABS];
/*@
	requires \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==>
		(0 <= xmhfgeec_slab_info_table[x].incl_devices_count <= XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES);
	requires \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==>
		(0 <= xmhfgeec_slab_info_table[x].excl_devices_count <= XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES);
	requires 0 <= numentries_sysdev_memioregions <= MAX_PLATFORM_DEVICES;

	assigns _sda_slab_devicemap[0..(XMHFGEEC_TOTAL_SLABS-1)].device_count;
    assigns t1: gp_s2_sdminitdevmap_coraddalldevstouobj[0..(XMHFGEEC_TOTAL_SLABS-1)];
    assigns t2: gp_s2_sdminitdevmap_coradddevtouobj[0..(XMHFGEEC_TOTAL_SLABS-1)];

	ensures \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==>
		(_sda_slab_devicemap[x].device_count <= MAX_PLATFORM_DEVICES);

   	ensures \exists integer x, integer y; 0 <= x < XMHFGEEC_TOTAL_SLABS && 0 <= y < xmhfgeec_slab_info_table[x].incl_devices_count &&
    			( xmhfgeec_slab_info_table[x].incl_devices[y].vendor_id == 0xFFFF &&
               xmhfgeec_slab_info_table[x].incl_devices[y].device_id == 0xFFFF) ==>
                (gp_s2_sdminitdevmap_coraddalldevstouobj[x] == true &&
            	 gp_s2_sdminitdevmap_coradddevtouobj[x] == false);
   	ensures \exists integer x, integer y; 0 <= x < XMHFGEEC_TOTAL_SLABS && 0 <= y < xmhfgeec_slab_info_table[x].incl_devices_count &&
    			!( xmhfgeec_slab_info_table[x].incl_devices[y].vendor_id == 0xFFFF &&
               xmhfgeec_slab_info_table[x].incl_devices[y].device_id == 0xFFFF) ==>
                (gp_s2_sdminitdevmap_coraddalldevstouobj[x] == false &&
            	 gp_s2_sdminitdevmap_coradddevtouobj[x] == true);

@*/
void gp_s2_sdminitdevmap(void){
    uint32_t i, j, k;

    _XDPRINTF_("%s: numentries_sysdev_mmioregions=%u\n", __func__, numentries_sysdev_memioregions);

	/*@
		loop invariant i1: 0 <= i <= XMHFGEEC_TOTAL_SLABS;
		loop invariant i2: \forall integer x; 0 <= x < i ==>
		 	 (_sda_slab_devicemap[x].device_count <= MAX_PLATFORM_DEVICES);
   		loop invariant i5: \exists integer x, integer y; 0 <= x < i && 0 <= y < xmhfgeec_slab_info_table[x].incl_devices_count &&
    			( xmhfgeec_slab_info_table[x].incl_devices[y].vendor_id == 0xFFFF &&
               xmhfgeec_slab_info_table[x].incl_devices[y].device_id == 0xFFFF) ==>
                (gp_s2_sdminitdevmap_coraddalldevstouobj[x] == true &&
            	 gp_s2_sdminitdevmap_coradddevtouobj[x] == false);
   		loop invariant i6: \exists integer x, integer y; 0 <= x < i && 0 <= y < xmhfgeec_slab_info_table[x].incl_devices_count &&
    			!( xmhfgeec_slab_info_table[x].incl_devices[y].vendor_id == 0xFFFF &&
               xmhfgeec_slab_info_table[x].incl_devices[y].device_id == 0xFFFF) ==>
                (gp_s2_sdminitdevmap_coraddalldevstouobj[x] == false &&
            	 gp_s2_sdminitdevmap_coradddevtouobj[x] == true);
		loop assigns i;
		loop assigns j;
		loop assigns _sda_slab_devicemap[0..(XMHFGEEC_TOTAL_SLABS-1)].device_count;
    	loop assigns i3: gp_s2_sdminitdevmap_coraddalldevstouobj[0..(XMHFGEEC_TOTAL_SLABS-1)];
    	loop assigns i4: gp_s2_sdminitdevmap_coradddevtouobj[0..(XMHFGEEC_TOTAL_SLABS-1)];
		loop variant XMHFGEEC_TOTAL_SLABS - i;
	@*/
    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
        _sda_slab_devicemap[i].device_count = 0;

    	/*@
    		loop invariant j1: 0 <= j <= xmhfgeec_slab_info_table[i].incl_devices_count;
    		loop invariant j4: \exists integer x; 0 <= x < j &&
    			( xmhfgeec_slab_info_table[i].incl_devices[x].vendor_id == 0xFFFF &&
               xmhfgeec_slab_info_table[i].incl_devices[x].device_id == 0xFFFF) ==>
                (gp_s2_sdminitdevmap_coraddalldevstouobj[i] == true &&
            	 gp_s2_sdminitdevmap_coradddevtouobj[i] == false);
    		loop invariant j5: \exists integer x; 0 <= x < j &&
    			!( xmhfgeec_slab_info_table[i].incl_devices[x].vendor_id == 0xFFFF &&
               xmhfgeec_slab_info_table[i].incl_devices[x].device_id == 0xFFFF) ==>
                (gp_s2_sdminitdevmap_coraddalldevstouobj[i] == false &&
            	 gp_s2_sdminitdevmap_coradddevtouobj[i] == true);
    		loop assigns j;
    		loop assigns j2: gp_s2_sdminitdevmap_coraddalldevstouobj[i];
    		loop assigns j3: gp_s2_sdminitdevmap_coradddevtouobj[i];
    		loop variant xmhfgeec_slab_info_table[i].incl_devices_count - j;
    	@*/
        for(j=0; j < xmhfgeec_slab_info_table[i].incl_devices_count; j++){
            if( xmhfgeec_slab_info_table[i].incl_devices[j].vendor_id == 0xFFFF &&
               xmhfgeec_slab_info_table[i].incl_devices[j].device_id == 0xFFFF){
            	gp_s2_sdminitdevmap_addalldevstouobj(i);
            	//@ghost gp_s2_sdminitdevmap_coraddalldevstouobj[i] = true;
            	//@ghost gp_s2_sdminitdevmap_coradddevtouobj[i] = false;
            }else{
            	gp_s2_sdminitdevmap_adddevtouobj(i, xmhfgeec_slab_info_table[i].incl_devices[j].vendor_id,
            			xmhfgeec_slab_info_table[i].incl_devices[j].device_id);
            	//@ghost gp_s2_sdminitdevmap_coraddalldevstouobj[i] = false;
            	//@ghost gp_s2_sdminitdevmap_coradddevtouobj[i] = true;
            }
        }

        #if defined (__DEBUG_SERIAL__)
        //add device SERIAL0 to all the slabs if debugging is enabled
    	gp_s2_sdminitdevmap_adddevtouobj(i, PCI_VENDOR_ID_XMHFGEEC, PCI_DEVICE_ID_XMHFGEEC_SERIAL0);
        #endif // defined

    }



	#if defined (__DEBUG_SERIAL__)
    //debug dump
    {
        uint32_t i, j;
        for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
            _XDPRINTF_("%s: slab %u...\n", __func__, i);
            for(j=0; j < _sda_slab_devicemap[i].device_count; j++){
                _XDPRINTF_("     device idx=%u\n", _sda_slab_devicemap[i].sysdev_mmioregions_indices[j]);
            }
        }
    }
	#endif // defined


}



