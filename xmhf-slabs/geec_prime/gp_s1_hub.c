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



//scan for available DRHD units on the platform and populate the
//global variables set:
//vtd_drhd[] (struct representing a DRHD unit)
//vtd_num_drhd (number of DRHD units detected)
//vtd_dmar_table_physical_address (physical address of the DMAR table)
//returns: true if all is fine else false; dmar_phys_addr_var contains
//max. value of DRHD unit handle (0 through maxhandle-1 are valid handles
//that can subsequently be passed to any of the other vtd drhd functions)
//physical address of the DMAR table in the system
//static bool xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(vtd_drhd_handle_t *maxhandle, u32 *dmar_phys_addr_var){
static bool xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(void){

	ACPI_RSDP rsdp;
	ACPI_RSDT rsdt;
	u32 num_rsdtentries;
	u32 rsdtentries[ACPI_MAX_RSDT_ENTRIES];
	u32 status;
	VTD_DMAR dmar;
	u32 i, dmarfound;
	u32 remappingstructuresaddrphys;
	//u32 vtd_dmar_table_physical_address;

	//zero out rsdp and rsdt structures
	//memset(&rsdp, 0, sizeof(ACPI_RSDP));
	//memset(&rsdt, 0, sizeof(ACPI_RSDT));

	//set maxhandle to 0 to start with. if we have any errors before
	//we finalize maxhandle we can just bail out
	vtd_drhd_maxhandle=0;

	//get ACPI RSDP
	status=xmhfhw_platform_x86pc_acpi_getRSDP(&rsdp);
	if(status == 0)
		return false;

	//_XDPRINTF_("\n%s: RSDP at %08x", __func__, status);

	//grab ACPI RSDT
	xmhfhw_sysmemaccess_copy((u8 *)&rsdt, (u8 *)rsdp.rsdtaddress, sizeof(ACPI_RSDT));
	//_XDPRINTF_("\n%s: RSDT at %08x, len=%u bytes, hdrlen=%u bytes",
	//	__func__, rsdp.rsdtaddress, rsdt.length, sizeof(ACPI_RSDT));

	//get the RSDT entry list
	num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT))/ sizeof(u32);
	if(num_rsdtentries >= ACPI_MAX_RSDT_ENTRIES){
			//_XDPRINTF_("\n%s: Error num_rsdtentries(%u) > ACPI_MAX_RSDT_ENTRIES (%u)", __func__, num_rsdtentries, ACPI_MAX_RSDT_ENTRIES);
			return false;
	}

	xmhfhw_sysmemaccess_copy((u8 *)&rsdtentries, (u8 *)(rsdp.rsdtaddress + sizeof(ACPI_RSDT)),
			sizeof(u32)*num_rsdtentries);
	//_XDPRINTF_("\n%s: RSDT entry list at %08x, len=%u", __func__,
	//	(rsdp.rsdtaddress + sizeof(ACPI_RSDT)), num_rsdtentries);

	//find the VT-d DMAR table in the list (if any)
	for(i=0; i< num_rsdtentries; i++){
		xmhfhw_sysmemaccess_copy((u8 *)&dmar, (u8 *)rsdtentries[i], sizeof(VTD_DMAR));
		if(dmar.signature == VTD_DMAR_SIGNATURE){
		  dmarfound=1;
		  break;
		}
	}

	//if no DMAR table, bail out
	if(!dmarfound){
		//_XDPRINTF_("\n%s: Error No DMAR table", __func__);
		return false;
	}

	vtd_dmar_table_physical_address = rsdtentries[i]; //DMAR table physical memory address;
	//*dmar_phys_addr_var = vtd_dmar_table_physical_address; //store it in supplied argument
	//_XDPRINTF_("\n%s: DMAR at %08x", __func__, vtd_dmar_table_physical_address);

	//detect DRHDs in the DMAR table
	i=0;
	remappingstructuresaddrphys=vtd_dmar_table_physical_address+sizeof(VTD_DMAR);
	//_XDPRINTF_("\n%s: remapping structures at %08x", __func__, remappingstructuresaddrphys);

	while(i < (dmar.length-sizeof(VTD_DMAR))){
		u16 type, length;
		xmhfhw_sysmemaccess_copy((u8 *)&type, (u8 *)(remappingstructuresaddrphys+i), sizeof(u16));
		xmhfhw_sysmemaccess_copy((u8 *)&length, (u8 *)(remappingstructuresaddrphys+i+sizeof(u16)), sizeof(u16));

		switch(type){
			case  0:  //DRHD
				//_XDPRINTF_("\nDRHD at %08x, len=%u bytes", (u32)(remappingstructuresaddrphys+i), length);
				if(vtd_num_drhd >= VTD_MAX_DRHD){
						//_XDPRINTF_("\n%s: Error vtd_num_drhd (%u) > VTD_MAX_DRHD (%u)", __func__, vtd_num_drhd, VTD_MAX_DRHD);
						return false;
				}
				xmhfhw_sysmemaccess_copy((u8 *)&vtd_drhd[vtd_num_drhd], (u8 *)(remappingstructuresaddrphys+i), length);
				vtd_num_drhd++;
				i+=(u32)length;
				break;

			default:	//unknown type, we skip this
				i += (u32)length;
				break;
		}
	}
    _XDPRINTF_("%s: total DRHDs detected= %u units\n", __func__, vtd_num_drhd);

    //populate IVA and IOTLB register addresses within all the DRHD unit
    //structures
    for(i=0; i < vtd_num_drhd; i++){
        VTD_ECAP_REG ecap;

        //ecap.value = _vtd_reg_read(&vtd_drhd[i], VTD_ECAP_REG_OFF);
        unpack_VTD_ECAP_REG(&ecap, _vtd_reg_read(&vtd_drhd[i], VTD_ECAP_REG_OFF));
        vtd_drhd[i].iotlb_regaddr= vtd_drhd[i].regbaseaddr+(ecap.iro*16)+0x8;
        vtd_drhd[i].iva_regaddr= vtd_drhd[i].regbaseaddr+(ecap.iro*16);
	}



	//[DEBUG]: be a little verbose about what we found
	//_XDPRINTF_("\n%s: DMAR Devices:", __func__);
	for(i=0; i < vtd_num_drhd; i++){
		VTD_CAP_REG cap;
		VTD_ECAP_REG ecap;
		_XDPRINTF_("	Device %u on PCI seg %04x; base=0x%016llx\n", i,
					vtd_drhd[i].pcisegment, vtd_drhd[i].regbaseaddr);
		unpack_VTD_CAP_REG(&cap, _vtd_reg_read(&vtd_drhd[i], VTD_CAP_REG_OFF));
		_XDPRINTF_("		cap=0x%016llx\n", pack_VTD_CAP_REG(&cap));
		//ecap.value = _vtd_reg_read(&vtd_drhd[i], VTD_ECAP_REG_OFF);
		unpack_VTD_ECAP_REG(&ecap, _vtd_reg_read(&vtd_drhd[i], VTD_ECAP_REG_OFF));
		_XDPRINTF_("		ecap=0x%016llx\n", (u64)pack_VTD_ECAP_REG(&ecap));
		_XDPRINTF_("	iotlb_regaddr=%08x, iva_regaddr=%08x\n",
					vtd_drhd[i].iotlb_regaddr, vtd_drhd[i].iva_regaddr);

	}

	vtd_drhd_maxhandle = vtd_num_drhd;
	vtd_drhd_scanned = true;

	return true;
}



static void _slabdevpgtbl_initretcet(void){
    u32 i, j;

    for(i=0; i< VTD_RET_MAXPTRS; i++){
        _slabdevpgtbl_vtd_ret[i].qwords[0] =
            vtd_make_rete((u64)&_slabdevpgtbl_vtd_cet[i], VTD_RET_PRESENT);
        _slabdevpgtbl_vtd_ret[i].qwords[1] = 0ULL;

        for(j=0; j < VTD_CET_MAXPTRS; j++){
            _slabdevpgtbl_vtd_cet[i][j].qwords[0] =
                _slabdevpgtbl_vtd_cet[i][j].qwords[1] = 0ULL;
        }
    }
}


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





void gp_s1_hub(void){


#if defined (__DEBUG_SERIAL__)

	//initialize debugging early on
	xmhf_debug_init((char *)&xcbootinfo->debugcontrol_buffer);


	//[debug] print relevant startup info.
	_XDPRINTF_("%s: alive and starting...\n", __func__);

	_XDPRINTF_("    xcbootinfo at = 0x%08x\n", (u32)xcbootinfo);
	_XDPRINTF_("	numE820Entries=%u\n", xcbootinfo->memmapinfo_numentries);
	_XDPRINTF_("	system memory map buffer at 0x%08x\n", (u32)&xcbootinfo->memmapinfo_buffer);
	_XDPRINTF_("	numCPUEntries=%u\n", xcbootinfo->cpuinfo_numentries);
	_XDPRINTF_("	cpuinfo buffer at 0x%08x\n", (u32)&xcbootinfo->cpuinfo_buffer);
	_XDPRINTF_("	XMHF size= %u bytes\n", __TARGET_SIZE_XMHF);
	_XDPRINTF_("	OS bootmodule at 0x%08x, size=%u bytes\n",
		xcbootinfo->richguest_bootmodule_base, xcbootinfo->richguest_bootmodule_size);
	_XDPRINTF_("\tcmdline = \"%s\"\n", xcbootinfo->cmdline_buffer);
	_XDPRINTF_("SL: runtime at 0x%08x; size=0x%08x bytes\n", __TARGET_BASE_XMHF, __TARGET_SIZE_XMHF);
	_XDPRINTF_("SL: XMHF_BOOTINFO at 0x%08x, magic=0x%08x\n", (u32)xcbootinfo, xcbootinfo->magic);
	HALT_ON_ERRORCOND(xcbootinfo->magic == RUNTIME_PARAMETER_BLOCK_MAGIC);
 	_XDPRINTF_("\nNumber of E820 entries = %u", xcbootinfo->memmapinfo_numentries);
	{
		u32 i;
		for(i=0; i < (u32)xcbootinfo->memmapinfo_numentries; i++){
			_XDPRINTF_("\n0x%08x%08x, size=0x%08x%08x (%u)",
			  xcbootinfo->memmapinfo_buffer[i].baseaddr_high, xcbootinfo->memmapinfo_buffer[i].baseaddr_low,
			  xcbootinfo->memmapinfo_buffer[i].length_high, xcbootinfo->memmapinfo_buffer[i].length_low,
			  xcbootinfo->memmapinfo_buffer[i].type);
		}
  	}

	//print out slab table
	{
		u32 i, j;

		for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
			_XDPRINTF_("slab %u: dumping slab header\n", i);
			_XDPRINTF_("	slabtype=%08x\n", xmhfgeec_slab_info_table[i].slabtype);
			_XDPRINTF_("	slab_inuse=%s\n", ( xmhfgeec_slab_info_table[i].slab_inuse ? "true" : "false") );
			_XDPRINTF_("	slab_callcaps=%08x\n", xmhfgeec_slab_info_table[i].slab_callcaps);
			//_XDPRINTF_("	slab_devices=%s\n", ( xmhfgeec_slab_info_table[i].slab_devices.desc_valid ? "true" : "false") );
			_XDPRINTF_("	incl_devices_count=%u\n", xmhfgeec_slab_info_table[i].incl_devices_count );
			for(j=0; j < xmhfgeec_slab_info_table[i].incl_devices_count; j++)
				_XDPRINTF_("        vendor_id=%x, device_id=%x\n",
					   xmhfgeec_slab_info_table[i].incl_devices[j].vendor_id,
					   xmhfgeec_slab_info_table[i].incl_devices[j].device_id);
			_XDPRINTF_("	excl_devices_count=%u\n", xmhfgeec_slab_info_table[i].excl_devices_count );
			for(j=0; j < xmhfgeec_slab_info_table[i].excl_devices_count; j++)
				_XDPRINTF_("        vendor_id=%x, device_id=%x\n",
					   xmhfgeec_slab_info_table[i].excl_devices[j].vendor_id,
					   xmhfgeec_slab_info_table[i].excl_devices[j].device_id);

			_XDPRINTF_("	slab_pgtblbase=%x\n", ( xmhfgeec_slab_info_table[i].mempgtbl_cr3) );
			_XDPRINTF_("	slab_iotblbase=%x\n", ( xmhfgeec_slab_info_table[i].iotbl_base) );
			_XDPRINTF_("  slab_code(%08x-%08x)\n", xmhfgeec_slab_info_table[i].slab_physmem_extents[0].addr_start, xmhfgeec_slab_info_table[i].slab_physmem_extents[0].addr_end);
			_XDPRINTF_("  slab_data(%08x-%08x)\n", xmhfgeec_slab_info_table[i].slab_physmem_extents[1].addr_start, xmhfgeec_slab_info_table[i].slab_physmem_extents[1].addr_end);
			_XDPRINTF_("  slab_stack(%08x-%08x)\n", xmhfgeec_slab_info_table[i].slab_physmem_extents[2].addr_start, xmhfgeec_slab_info_table[i].slab_physmem_extents[2].addr_end);
			_XDPRINTF_("  slab_dmadata(%08x-%08x)\n", xmhfgeec_slab_info_table[i].slab_physmem_extents[3].addr_start, xmhfgeec_slab_info_table[i].slab_physmem_extents[3].addr_end);
			_XDPRINTF_("  slab_entrystub=%08x\n", xmhfgeec_slab_info_table[i].entrystub);

		}
	}

#endif // __DEBUG_SERIAL__


	//sanity check hardware requirements
	gp_s1_chkreq();

	//post DRT cleanup first
	gp_s1_postdrt();


	//scan for IOMMU and halt if not present
	if(!xmhfhw_platform_x86pc_vtd_scanfor_drhd_units()){
		_XDPRINTF_("%s: unable to scan for DRHD units. halting!\n", __func__);
		HALT();
	}

	_XDPRINTF_("%s: Vt-d: maxhandle = %u, dmar table addr=0x%08x\n", __func__,
		(u32)vtd_drhd_maxhandle, (u32)vtd_dmar_table_physical_address);



	// (zero) initialize RET and CET
	_slabdevpgtbl_initretcet();


	//intialize VT-d subsystem and obtain page-walk level
	vtd_pagewalk_level = _geec_prime_vtd_initialize((u32)&_slabdevpgtbl_vtd_ret);
	_XDPRINTF_("%s: setup vt-d, page-walk level=%u\n", __func__, vtd_pagewalk_level);


	//move on to phase-2
	gp_s2_entry();
}

