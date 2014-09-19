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
#include <xcapi.h>


//__attribute__((aligned(4096))) static vtd_slpgtbl_t _vtd_slpgtbl[MAX_PRIMARY_PARTITIONS];


/*static bool _xcdev_arch_allocdevicetopartition(u32 partition_index, u32 b, u32 d, u32 f){
	vtd_drhd_handle_t drhd_handle;

    //sanity check b, d, f triad
    if ( !(b < PCI_BUS_MAX && d < PCI_DEVICE_MAX && f < PCI_FUNCTION_MAX) )
        return false;

    //b is our index into ret
    // (d* PCI_FUNCTION_MAX) + f = index into the cet

    if(vtd_pagewalk_level == VTD_PAGEWALK_4LEVEL){
        _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.slptptr = ((u64)_vtd_slpgtbl[partition_index].pml4t >> 12);
        _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.aw = 2; //4-level
        _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.did = (partition_index + 1); //domain
        _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.p = 1; //present
    }else if (vtd_pagewalk_level == VTD_PAGEWALK_3LEVEL){
        _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.slptptr = ((u64)_vtd_slpgtbl[partition_index].pdpt >> 12);
        _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.aw = 1; //3-level
        _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.did = (partition_index + 1); //domain
        _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.p = 1; //present
    }else{ //unknown page walk length, fail
        return false;
    }

	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
		//invalidate caches
		if(!xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(drhd_handle))
			return false;
	}

    return true;
}*/




bool xcdev_arch_initialize(u32 partition_index){
    /*u64 vtd_ret_addr;
	vtd_drhd_handle_t drhd_handle;
	u32 vtd_dmar_table_physical_address=0;
    vtd_slpgtbl_handle_t vtd_slpgtbl_handle;
    u32 b, d, f;

	//setup basic RET/CET structure; will initially prevent DMA reads and writes
	//for the entire system
    vtd_ret_addr = _xcdev_arch_setup_vtd_retcet();

	//scan for available DRHD units in the platform
	if(!xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(&vtd_drhd_maxhandle, &vtd_dmar_table_physical_address)){
        _XDPRINTF_("%s: unable to scan for DRHD units. bailing out!\n", __FUNCTION__);
		return false;
	}

    _XDPRINTF_("%s: maxhandle = %u, dmar table addr=0x%08x\n", __FUNCTION__,
                (u32)vtd_drhd_maxhandle, (u32)vtd_dmar_table_physical_address);

	//initialize all DRHD units
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
   		VTD_CAP_REG cap;

		_XDPRINTF_("%s: Setting up DRHD unit %u...\n", __FUNCTION__, drhd_handle);

		if(!xmhfhw_platform_x86pc_vtd_drhd_initialize(drhd_handle) ){
            _XDPRINTF_("%s: error setting up DRHD unit %u. bailing out!\n", __FUNCTION__, drhd_handle);
			return false;
		}

        //read and store DRHD supported page-walk length
        cap.value = xmhfhw_platform_x86pc_vtd_drhd_reg_read(drhd_handle, VTD_CAP_REG_OFF);
        if(cap.bits.sagaw & 0x2){
            if(vtd_pagewalk_level == VTD_PAGEWALK_NONE || vtd_pagewalk_level == VTD_PAGEWALK_3LEVEL){
                vtd_pagewalk_level = VTD_PAGEWALK_3LEVEL;
                _XDPRINTF_("%s: DRHD unit %u - 3-level page-walk\n", __FUNCTION__, drhd_handle);
            }else{
                _XDPRINTF_("%s: Halting: mixed hardware supported page-walk lengths\n",
                            __FUNCTION__);
                HALT();
            }
        }

        if(cap.bits.sagaw & 0x4){
            if(vtd_pagewalk_level == VTD_PAGEWALK_NONE || vtd_pagewalk_level == VTD_PAGEWALK_4LEVEL){
                vtd_pagewalk_level = VTD_PAGEWALK_4LEVEL;
                _XDPRINTF_("%s: DRHD unit %u - 4-level page-walk\n", __FUNCTION__, drhd_handle);
            }else{
                _XDPRINTF_("%s: Halting: mixed hardware supported page-walk lengths\n",
                            __FUNCTION__);
                HALT();
            }
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


    _XDPRINTF_("%s: final page-walk level=%u\n", __FUNCTION__, vtd_pagewalk_level);

    //setup partition vt-d page tables
    vtd_slpgtbl_handle = _xcdev_arch_setup_vtd_slpgtbl(partition_index);

    if(vtd_slpgtbl_handle.addr_vtd_pml4t == 0 &&
        vtd_slpgtbl_handle.addr_vtd_pdpt == 0){
        _XDPRINTF_("%s: unable to initialize vt-d pagetables for partition %u\n", __FUNCTION__, partition_index);
		return false;
    }*/


	{
        u32 i;
	    xc_platformdevice_desc_t ddescs;
        context_desc_t ctx;

        ctx.cpu_desc.cpu_index = 0;
        ctx.cpu_desc.isbsp = true;
        ctx.partition_desc.partition_index = partition_index;

        ddescs = XMHF_SLAB_CALL(xc_api_platform_enumeratedevices(ctx));

        if(!ddescs.desc_valid){
            _XDPRINTF_("%s: Error: could not obtain platform device descriptors\n",
                        __FUNCTION__);
            return false;
        }

        for(i=0; i < ddescs.numdevices; i++){
			_XDPRINTF_("  %02x:%02x.%1x -> vendor_id=%04x, device_id=%04x\n", ddescs.arch_desc[i].pci_bus,
              ddescs.arch_desc[i].pci_device, ddescs.arch_desc[i].pci_function,
              ddescs.arch_desc[i].vendor_id, ddescs.arch_desc[i].device_id);
        }

        if(!XMHF_SLAB_CALL(xc_api_platform_allocdevices_to_partition(ctx, ddescs))){
                _XDPRINTF_("%s: Halting.unable to allocate devices to partition %u\n",
                            __FUNCTION__, partition_index);
                HALT();
        }
	}

    return true;
}
