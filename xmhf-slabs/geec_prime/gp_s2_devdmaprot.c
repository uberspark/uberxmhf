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
#include <xc_init.h>

//////////////////////////////////////////////////////////////////////////////
//setup slab device allocation (sda)













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




/*static void _slabdevpgtbl_init(void){
    u32 i;

    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
        _slabdevpgtbl_infotable[i].devpgtbl_initialized=false;
    }
}*/




static void _slabdevpgtbl_initdevpgtbl(u32 slabid){
    u32 i;
    u64 default_flags = (VTD_PAGE_READ | VTD_PAGE_WRITE);
    u32 paddr=0, pt_paddr;
    u32 pt_index=0;
    u32 paddr_dmadata_start, paddr_dmadata_end;

    paddr_dmadata_start =
        xmhfgeec_slab_info_table[slabid].slab_physmem_extents[3].addr_start;
    paddr_dmadata_end =
        xmhfgeec_slab_info_table[slabid].slab_physmem_extents[3].addr_end;

    //sanity checks
    if(slabid > XMHFGEEC_TOTAL_SLABS){
        _XDPRINTF_("%s: Error: slabid (%u) > XMHFGEEC_TOTAL_SLABS(%u). bailing out!\n", __func__, slabid, XMHFGEEC_TOTAL_SLABS);
        return;
    }
    if( (paddr_dmadata_end - paddr_dmadata_start) >
        MAX_SLAB_DMADATA_SIZE ){
        _XDPRINTF_("%s: Error: slab %u dmadata section over limit. bailing out!\n",
                   __func__, slabid);
        return;
    }


    //initialize lvl1 page table (pml4t)
    memset(&_slabdevpgtbl_pml4t[slabid], 0, sizeof(_slabdevpgtbl_pml4t[0]));
    _slabdevpgtbl_pml4t[slabid][0] =
        vtd_make_pml4te((u64)_slabdevpgtbl_pdpt[slabid], default_flags);

    //initialize lvl2 page table (pdpt)
    memset(&_slabdevpgtbl_pdpt[slabid], 0, sizeof(_slabdevpgtbl_pdpt[0]));
    for(i=0; i < VTD_PTRS_PER_PDPT; i++){
        _slabdevpgtbl_pdpt[slabid][i] =
            vtd_make_pdpte((u64)_slabdevpgtbl_pdt[slabid][i], default_flags);
    }


    paddr = paddr_dmadata_start;

    do {
        //grab index of pdpt, pdt this paddr
        u32 pdpt_index = pae_get_pdpt_index(paddr);
        u32 pdt_index = pae_get_pdt_index(paddr);

        //stick a pt for the pdt entry
        _slabdevpgtbl_pdt[slabid][pdpt_index][pdt_index] =
            vtd_make_pdte((u64)_slabdevpgtbl_pt[slabid][pt_index], default_flags);

        //populate pt entries
        pt_paddr = paddr;
        for(i=0; i < VTD_PTRS_PER_PT; i++){
            _slabdevpgtbl_pt[slabid][pt_index][i] =
                vtd_make_pte(pt_paddr, default_flags);
            pt_paddr += PAGE_SIZE_4K;
        }

        pt_index++;
        paddr += PAGE_SIZE_2M;
    } while (paddr < paddr_dmadata_end);


    _slabdevpgtbl_infotable[slabid].devpgtbl_initialized = true;
}



static void _slabdevpgtbl_binddevice(u32 slabid, u32 pagewalk_lvl,  u32 bus, u32 dev, u32 func){
    //sanity checks
    if(slabid > XMHFGEEC_TOTAL_SLABS){
        _XDPRINTF_("%s: Error: slabid (%u) > XMHFGEEC_TOTAL_SLABS(%u). bailing out!\n", __func__, slabid, XMHFGEEC_TOTAL_SLABS);
        return;
    }

    if(!_slabdevpgtbl_infotable[slabid].devpgtbl_initialized){
        _XDPRINTF_("%s: Error: slabid (%u) devpgtbl not initialized\n",
                   __func__, slabid);
        return;
    }

    if ( !(bus < PCI_BUS_MAX &&
           dev < PCI_DEVICE_MAX &&
           func < PCI_FUNCTION_MAX) ){
        _XDPRINTF_("%s: Error: slabid (%u) b:d:f out of limits\n",
                   __func__, slabid);
        return;
    }

    //b is our index into ret
    // (d* PCI_FUNCTION_MAX) + f = index into the cet
    if(pagewalk_lvl == VTD_PAGEWALK_4LEVEL){
        _slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[0] =
            vtd_make_cete((u64)&_slabdevpgtbl_pml4t[slabid], VTD_CET_PRESENT);
        _slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[1] =
            vtd_make_cetehigh(2, (slabid+1));
    }else if (pagewalk_lvl == VTD_PAGEWALK_3LEVEL){
        _slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[0] =
            vtd_make_cete((u64)&_slabdevpgtbl_pdpt[slabid], VTD_CET_PRESENT);
        _slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[1] =
            vtd_make_cetehigh(1, (slabid+1));
    }else{ //unknown page walk length, fail
        _XDPRINTF_("%s: Error: slabid (%u) unknown pagewalk\n",
                   __func__, slabid);
        return;
    }


}




void gp_s2_sdadoalloc(void){
	u32 i;
	u32 dst_slabid;

        for(i=0; i <numentries_sysdev_memioregions; i++){
            if(sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_GENERAL ||
               sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE ||
               sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN){

		dst_slabid = _geec_prime_getslabfordevice(sysdev_memioregions[i].b, sysdev_memioregions[i].d, sysdev_memioregions[i].f);
                if(dst_slabid == 0xFFFFFFFFUL){
                    _XDPRINTF_("Could not find slab for device %x:%x:%x (vid:did=%x:%x, type=%x), skipping...\n", sysdev_memioregions[i].b,
                               sysdev_memioregions[i].d, sysdev_memioregions[i].f, sysdev_memioregions[i].vendor_id,
                               sysdev_memioregions[i].device_id, sysdev_memioregions[i].dtype);
                }else{
			_slabdevpgtbl_binddevice(dst_slabid, vtd_pagewalk_level,
						sysdev_memioregions[i].b, sysdev_memioregions[i].d, sysdev_memioregions[i].f);

                    _XDPRINTF_("Allocated device %x:%x:%x (vid:did=%x:%x, type=%x) to slab %u...\n", sysdev_memioregions[i].b,
                               sysdev_memioregions[i].d, sysdev_memioregions[i].f, sysdev_memioregions[i].vendor_id,
                               sysdev_memioregions[i].device_id, sysdev_memioregions[i].dtype, dst_slabid);
                }
            }
        }
}




void gp_s2_sda(void){
	u32 i;

	for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
		_slabdevpgtbl_infotable[i].devpgtbl_initialized=false;
	}

	//initialize all slab device page tables
	for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
		_slabdevpgtbl_initdevpgtbl(i);

	}

	_XDPRINTF_("%s: initialized slab device page tables\n", __func__);

	gp_s2_sdadoalloc();
}


