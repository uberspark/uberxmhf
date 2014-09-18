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

/*
 * XMHF core device initialization slab (xcdev), x86-vmx-x86pc arch. backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcdev.h>

__attribute__((aligned(4096))) static vtd_ret_entry_t _vtd_ret[VTD_RET_MAXPTRS];
__attribute__((aligned(4096))) static vtd_cet_entry_t _vtd_cet[VTD_RET_MAXPTRS][VTD_CET_MAXPTRS];

__attribute__((aligned(4096))) static vtd_slpgtbl_t _vtd_slpgtbl[MAX_PRIMARY_PARTITIONS];

static bool _xcdev_arch_allocdevicetopartition(u32 partition_index, u32 b, u32 d, u32 f){

    //sanity check b, d, f triad
    if ( !(b < PCI_BUS_MAX && d < PCI_DEVICE_MAX && f < PCI_FUNCTION_MAX) )
        return false;

    //b is our index into ret
    // (d* PCI_DEVICE_MAX) + f = index into the cet
    _vtd_cet[b][(d*PCI_DEVICE_MAX) + f].fields.p = 1; //present
    _vtd_cet[b][(d*PCI_DEVICE_MAX) + f].fields.did = 1; //domain
    _vtd_cet[b][(d*PCI_DEVICE_MAX) + f].fields.aw = 2; //4-level
    _vtd_cet[b][(d*PCI_DEVICE_MAX) + f].fields.slptptr = _vtd_slpgtbl[partition_index].pml4t;

    return true;
}

static vtd_slpgtbl_handle_t _xcdev_arch_setup_vtd_slpgtbl(u32 partition_index){
    vtd_slpgtbl_handle_t retval = {0, 0};
    u32 i, j, k, paddr=0;

    //sanity check partition index
    if(partition_index >= MAX_PRIMARY_PARTITIONS){
        _XDPRINTF_("%s: Error: partition_index >= MAX_PRIMARY_PARTITIONS. bailing out!\n", __FUNCTION__);
        return retval;
    }

    //setup device memory access for the partition
    _vtd_slpgtbl[partition_index].pml4t[0].fields.r = 1;
    _vtd_slpgtbl[partition_index].pml4t[0].fields.w = 1;
    _vtd_slpgtbl[partition_index].pml4t[0].fields.slpdpt = &_vtd_slpgtbl[partition_index].pdpt;

    for(i=0; i < PAE_PTRS_PER_PDPT; i++){
        _vtd_slpgtbl[partition_index].pdpt[i].fields.r = 1;
        _vtd_slpgtbl[partition_index].pdpt[i].fields.w = 1;
        _vtd_slpgtbl[partition_index].pdpt[i].fields.slpdt = &_vtd_slpgtbl[partition_index].pdt[i];

        for(j=0; j < PAE_PTRS_PER_PDT; j++){
            _vtd_slpgtbl[partition_index].pdt[i][j].fields.r = 1;
            _vtd_slpgtbl[partition_index].pdt[i][j].fields.w = 1;
            _vtd_slpgtbl[partition_index].pdt[i][j].fields.slpt = &_vtd_slpgtbl[partition_index].pt[i][j];

            for(k=0; k < PAE_PTRS_PER_PT; k++){
                _vtd_slpgtbl[partition_index].pt[i][j][k].fields.r = 1;
                _vtd_slpgtbl[partition_index].pt[i][j][k].fields.w = 1;
                _vtd_slpgtbl[partition_index].pt[i][j][k].fields.pageaddr = paddr;
                paddr += PAGE_SIZE_4K;
            }
        }
    }

    retval.addr_vtd_pml4t = _vtd_slpgtbl[partition_index].pml4t;
    retval.addr_vtd_pdpt = _vtd_slpgtbl[partition_index].pdpt;

    return retval;
}

static u64 _xcdev_arch_setup_vtd_retcet(void){
    u32 i, j;

    for(i=0; i< VTD_RET_MAXPTRS; i++){
        _vtd_ret[i].qwords[0] = _vtd_ret[i].qwords[1] = 0ULL;
        _vtd_ret[i].fields.p = 1;
        _vtd_ret[i].fields.ctp = &_vtd_cet[i];

        for(j=0; j < VTD_CET_MAXPTRS; j++){
            _vtd_cet[i][j].qwords[0] = _vtd_cet[i][j].qwords[1] = 0ULL;
        }
    }

    return (u64)&_vtd_ret;
}


bool xcdev_arch_initialize(u32 partition_index){
    u64 vtd_ret_addr;
	vtd_drhd_handle_t drhd_handle;
	u32 vtd_dmar_table_physical_address=0;
	vtd_drhd_handle_t vtd_drhd_maxhandle;
    vtd_slpgtbl_handle_t vtd_slpgtbl_handle;
    u32 b, d, f;

	//zero out RET; will be used to prevent DMA reads and writes
	//for the entire system
	//memset((void *)&vtd_ret_table, 0, sizeof(vtd_ret_table));
    vtd_ret_addr = _xcdev_arch_setup_vtd_retcet();

    //setup partition vt-d page tables
    vtd_slpgtbl_handle = _xcdev_arch_setup_vtd_slpgtbl(partition_index);

    if(vtd_slpgtbl_handle.addr_vtd_pml4t == 0 &&
        vtd_slpgtbl_handle.addr_vtd_pdpt == 0){
        _XDPRINTF_("%s: unable to initialize vt-d pagetables for partition %u\n", __FUNCTION__, partition_index);
		return false;
    }


	//scan for available DRHD units in the platform
	if(!xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(&vtd_drhd_maxhandle, &vtd_dmar_table_physical_address)){
        _XDPRINTF_("%s: unable to scan for DRHD units. bailing out!\n", __FUNCTION__);
		return false;
	}

    _XDPRINTF_("%s: maxhandle = %u, dmar table addr=0x%08x\n", __FUNCTION__,
                (u32)vtd_drhd_maxhandle, (u32)vtd_dmar_table_physical_address);


	//initialize all DRHD units
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
   		//VTD_CAP_REG cap;
		//VTD_ECAP_REG ecap;

		_XDPRINTF_("%s: Setting up DRHD unit %u...\n", __FUNCTION__, drhd_handle);

		if(!xmhfhw_platform_x86pc_vtd_drhd_initialize(drhd_handle) ){
            _XDPRINTF_("%s: error setting up DRHD unit %u. bailing out!\n", __FUNCTION__, drhd_handle);
			return false;
		}

		//set DRHD root entry table
		if(!xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table(drhd_handle, vtd_ret_addr))
			return false;

		//invalidate caches
		if(!xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(drhd_handle))
			return false;

		//enable VT-d translation
		xmhfhw_platform_x86pc_vtd_drhd_enable_translation(drhd_handle);

		//disable PMRs now (since DMA protection is active via translation)
		xmhfhw_platform_x86pc_vtd_drhd_disable_pmr(drhd_handle);

		_XDPRINTF_("%s: Successfully setup DRHD unit %u\n", __FUNCTION__, drhd_handle);
	}

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	xmhfhw_sysmemaccess_writeu32(vtd_dmar_table_physical_address, 0UL);


    //enumerate PCI bus to find out all the devices
	//bus numbers range from 0-255, device from 0-31 and function from 0-7
	_XDPRINTF_("%: enumerating system devices...\n", __FUNCTION__);

	for(b=0; b < PCI_BUS_MAX; b++){
		for(d=0; d < PCI_DEVICE_MAX; d++){
			for(f=0; f < PCI_FUNCTION_MAX; f++){
				u32 vendor_id, device_id;
				//read device and vendor ids, if no device then both will be 0xFFFF
				xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_VENDOR_ID, sizeof(u16), &vendor_id);
				xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_DEVICE_ID, sizeof(u16), &device_id);
				if(vendor_id == 0xFFFF && device_id == 0xFFFF)
					break;

				_XDPRINTF_("  %02x:%02x.%1x -> vendor_id=%04x, device_id=%04x\n", b, d, f, vendor_id, device_id);
                _xcdev_arch_allocdevicetopartition(partition_index, b, d, f);
			}
		}
	}


    return true;
}
