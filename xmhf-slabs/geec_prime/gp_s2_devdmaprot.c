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

//////////////////////////////////////////////////////////////////////////////
//setup slab device allocation (sda)









//initialize vtd hardware and return vt-d pagewalk level
static u32 _geec_prime_vtd_initialize(u32 vtd_ret_addr){
    u32 vtd_pagewalk_level = VTD_PAGEWALK_NONE;
    //vtd_drhd_handle_t vtd_drhd_maxhandle=0;
	vtd_drhd_handle_t drhd_handle;
	//u32 vtd_dmar_table_physical_address=0;
    vtd_slpgtbl_handle_t vtd_slpgtbl_handle;
    u32 i, b, d, f;


	//initialize all DRHD units
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
   		VTD_CAP_REG cap;

		_XDPRINTF_("%s: Setting up DRHD unit %u...\n", __func__, drhd_handle);

		if(!xmhfhw_platform_x86pc_vtd_drhd_initialize(&vtd_drhd[drhd_handle]) ){
            _XDPRINTF_("%s: error setting up DRHD unit %u. halting!\n", __func__, drhd_handle);
			HALT();
		}

        //read and store DRHD supported page-walk length
        unpack_VTD_CAP_REG(&cap, _vtd_reg_read(&vtd_drhd[drhd_handle], VTD_CAP_REG_OFF));
        if(cap.sagaw & 0x2){
            if(vtd_pagewalk_level == VTD_PAGEWALK_NONE || vtd_pagewalk_level == VTD_PAGEWALK_3LEVEL){
                vtd_pagewalk_level = VTD_PAGEWALK_3LEVEL;
                _XDPRINTF_("%s: DRHD unit %u - 3-level page-walk\n", __func__, drhd_handle);
            }else{
                _XDPRINTF_("%s: Halting: mixed hardware supported page-walk lengths\n",
                            __func__);
                HALT();
            }
        }

        if(cap.sagaw & 0x4){
            if(vtd_pagewalk_level == VTD_PAGEWALK_NONE || vtd_pagewalk_level == VTD_PAGEWALK_4LEVEL){
                vtd_pagewalk_level = VTD_PAGEWALK_4LEVEL;
                _XDPRINTF_("%s: DRHD unit %u - 4-level page-walk\n", __func__, drhd_handle);
            }else{
                _XDPRINTF_("%s: Halting: mixed hardware supported page-walk lengths\n",
                            __func__);
                HALT();
            }
        }


		//set DRHD root entry table
		if(!xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table(&vtd_drhd[drhd_handle], vtd_ret_addr)){
            _XDPRINTF_("%s: Halting: error in setting DRHD RET\n", __func__);
            HALT();
		}

		//invalidate caches
		if(!xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(&vtd_drhd[drhd_handle])){
            _XDPRINTF_("%s: Halting: error in invalidating caches\n", __func__);
            HALT();
		}

		//enable VT-d translation
		xmhfhw_platform_x86pc_vtd_drhd_enable_translation(&vtd_drhd[drhd_handle]);

		//disable PMRs now (since DMA protection is active via translation)
		xmhfhw_platform_x86pc_vtd_drhd_disable_pmr(&vtd_drhd[drhd_handle]);

		_XDPRINTF_("%s: Successfully setup DRHD unit %u\n", __func__, drhd_handle);
	}

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	xmhfhw_sysmemaccess_writeu32(vtd_dmar_table_physical_address, 0UL);


    _XDPRINTF_("%s: final page-walk level=%u\n", __func__, vtd_pagewalk_level);

    return vtd_pagewalk_level;
}




//returns 0xFFFFFFFF on error
static u32 _geec_prime_getslabfordevice(u32 bus, u32 dev, u32 func){
    u32 i;

/*    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
        //for now detect rich guest slab and allocate all platform devices to it
        if(xmhfgeec_slab_info_table[i].slab_devices.desc_valid &&
            xmhfgeec_slab_info_table[i].slab_devices.numdevices == 0xFFFFFFFFUL)
            return i;
    }

    return 0xFFFFFFFFUL;
*/
    //XXX: allocate all devices to rich guest slab for now
    return XMHFGEEC_SLAB_XG_RICHGUEST;

}





void xmhfhic_arch_setup_slab_device_allocation(void){
    u32 i, vtd_pagewalk_level;
    //slab_platformdevices_t ddescs;
    slab_params_t spl;
    xmhfgeec_uapi_slabdevpgtbl_initretcet_params_t *initretcetp =
        (xmhfgeec_uapi_slabdevpgtbl_initretcet_params_t *)spl.in_out_params;
    xmhfgeec_uapi_slabdevpgtbl_initdevpgtbl_params_t *initdevpgtblp =
        (xmhfgeec_uapi_slabdevpgtbl_initdevpgtbl_params_t *)spl.in_out_params;
    xmhfgeec_uapi_slabdevpgtbl_binddevice_params_t *binddevicep =
        (xmhfgeec_uapi_slabdevpgtbl_binddevice_params_t *)spl.in_out_params;


    spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABDEVPGTBL;
    spl.cpuid = 0; //XXX: fixme, needs to be BSP id





    //slabdevpgtbl:init
    spl.dst_uapifn = XMHFGEEC_UAPI_SDEVPGTBL_INIT;
    XMHF_SLAB_CALLNEW(&spl);

    //slabdevpgtbl:initretcet
    spl.dst_uapifn = XMHFGEEC_UAPI_SDEVPGTBL_INITRETCET;
    XMHF_SLAB_CALLNEW(&spl);

    //use slabdevpgtbl:initdevpgtbl to initialize all slab device page tables
    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
        spl.dst_uapifn = XMHFGEEC_UAPI_SDEVPGTBL_INITDEVPGTBL;
        initdevpgtblp->dst_slabid = i;
        XMHF_SLAB_CALLNEW(&spl);
    }
    _XDPRINTF_("%s: initialized slab device page tables\n", __func__);

    //intialize VT-d subsystem and obtain
    vtd_pagewalk_level = _geec_prime_vtd_initialize(initretcetp->result_retpaddr);
    _XDPRINTF_("%s: setup vt-d, page-walk level=%u\n", __func__, vtd_pagewalk_level);


    //allocate system devices to slabs for direct DMA
    {
        u32 i;
        for(i=0; i <numentries_sysdev_memioregions; i++){
            if(sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_GENERAL ||
               sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE ||
               sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN){

                spl.dst_uapifn = XMHFGEEC_UAPI_SDEVPGTBL_BINDDEVICE;
                binddevicep->dst_slabid = _geec_prime_getslabfordevice(sysdev_memioregions[i].b, sysdev_memioregions[i].d, sysdev_memioregions[i].f);
                if(binddevicep->dst_slabid == 0xFFFFFFFFUL){
                    _XDPRINTF_("Could not find slab for device %x:%x:%x (vid:did=%x:%x, type=%x), skipping...\n", sysdev_memioregions[i].b,
                               sysdev_memioregions[i].d, sysdev_memioregions[i].f, sysdev_memioregions[i].vendor_id,
                               sysdev_memioregions[i].device_id, sysdev_memioregions[i].dtype);
                }else{
                    binddevicep->bus = sysdev_memioregions[i].b;
                    binddevicep->dev = sysdev_memioregions[i].d;
                    binddevicep->func = sysdev_memioregions[i].f;
                    binddevicep->pagewalk_level = vtd_pagewalk_level;
                    XMHF_SLAB_CALLNEW(&spl);
                    _XDPRINTF_("Allocated device %x:%x:%x (vid:did=%x:%x, type=%x) to slab %u...\n", sysdev_memioregions[i].b,
                               sysdev_memioregions[i].d, sysdev_memioregions[i].f, sysdev_memioregions[i].vendor_id,
                               sysdev_memioregions[i].device_id, sysdev_memioregions[i].dtype, binddevicep->dst_slabid);
                }
            }
        }
    }


}


