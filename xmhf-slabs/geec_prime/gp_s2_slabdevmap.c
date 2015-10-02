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
#include <uapi_slabiotbl.h>
#include <xc_init.h>

//returns true if a given device vendor_id:device_id is in the slab device exclusion
//list
static bool _geec_prime_sda_populate_slabdevicemap_isdevinexcl(u32 slabid, u32 vendor_id, u32 device_id){
    u32 i;

    for(i=0; i < xmhfgeec_slab_info_table[slabid].excl_devices_count; i++){
        if(xmhfgeec_slab_info_table[slabid].excl_devices[i].vendor_id == vendor_id &&
           xmhfgeec_slab_info_table[slabid].excl_devices[i].device_id == device_id)
            return true;
    }

    return false;
}

static void _geec_prime_sda_populate_slabdevicemap(void){
    u32 i, j, k;

    _XDPRINTF_("%s: numentries_sysdev_mmioregions=%u\n", __func__,
               numentries_sysdev_memioregions);

    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
        _sda_slab_devicemap[i].device_count = 0;

        for(j=0; j < xmhfgeec_slab_info_table[i].incl_devices_count; j++){
            if( xmhfgeec_slab_info_table[i].incl_devices[j].vendor_id == 0xFFFF &&
               xmhfgeec_slab_info_table[i].incl_devices[j].device_id == 0xFFFF){
                for(k=0; k < numentries_sysdev_memioregions; k++){
                    if(!_geec_prime_sda_populate_slabdevicemap_isdevinexcl(i, sysdev_memioregions[k].vendor_id, sysdev_memioregions[k].device_id)){
                        if( _sda_slab_devicemap[i].device_count >= MAX_PLATFORM_DEVICES){
                            _XDPRINTF_("%s: Halting! device_count >= MAX_PLATFORM_DEVICES\n", __func__);
                            HALT();
                        }
                        _sda_slab_devicemap[i].sysdev_mmioregions_indices[_sda_slab_devicemap[i].device_count]=k;
                        _sda_slab_devicemap[i].device_count++;

                    }
                }
            }else{
                for(k=0; k < numentries_sysdev_memioregions; k++){
                    if( (sysdev_memioregions[k].vendor_id == xmhfgeec_slab_info_table[i].incl_devices[j].vendor_id) &&
                        (sysdev_memioregions[k].device_id == xmhfgeec_slab_info_table[i].incl_devices[j].device_id) &&
                        !_geec_prime_sda_populate_slabdevicemap_isdevinexcl(i, xmhfgeec_slab_info_table[i].incl_devices[j].vendor_id, xmhfgeec_slab_info_table[i].incl_devices[j].device_id)
                    ){
                        if( _sda_slab_devicemap[i].device_count >= MAX_PLATFORM_DEVICES){
                            _XDPRINTF_("%s: Halting! device_count >= MAX_PLATFORM_DEVICES\n", __func__);
                            HALT();
                        }
                        _sda_slab_devicemap[i].sysdev_mmioregions_indices[_sda_slab_devicemap[i].device_count]=k;
                        _sda_slab_devicemap[i].device_count++;

                    }
                }
            }
        }

        #if defined (__DEBUG_SERIAL__)
        //add device SERIAL0 to all the slabs if debugging is enabled
        for(k=0; k < numentries_sysdev_memioregions; k++){
            if( (sysdev_memioregions[k].vendor_id == PCI_VENDOR_ID_XMHFGEEC) &&
                (sysdev_memioregions[k].device_id == PCI_DEVICE_ID_XMHFGEEC_SERIAL0) ){
                if( _sda_slab_devicemap[i].device_count >= MAX_PLATFORM_DEVICES){
                    _XDPRINTF_("%s: Halting! device_count >= MAX_PLATFORM_DEVICES\n", __func__);
                    HALT();
                }
                _sda_slab_devicemap[i].sysdev_mmioregions_indices[_sda_slab_devicemap[i].device_count]=k;
                _sda_slab_devicemap[i].device_count++;

            }
        }

        #endif // defined

    }


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


}



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


static void _sda_enumerate_system_devices(void){
    u32 b, d, f, i;
	vtd_drhd_handle_t drhd_handle;



    //as a first step, add several non-PCI system devices to the
    //sysdev list using XMHF/GEEC psuedo-PCI vendor and device IDs
    //the following are the list of non-PCI system devices:
    //LAPIC at X86SMP_LAPIC_MEMORYADDRESS (0xFEE00000)
    //TPM at TPM_LOCALITY_BASE (0xfed40000)
    //TXT at TXT_PUB_CONFIG_REGS_BASE (0xfed30000) and TXT_PRIV_CONFIG_REGS_BASE (0xfed20000)
    //SERIAL0 (used for debugging only) at DEBUG_PORT
    //IOMMU as described by vtd_drhd[]


    //sanity check available sysdev entries for the above devices
    if( (numentries_sysdev_memioregions+vtd_drhd_maxhandle+1+1+1+1) >= MAX_PLATFORM_DEVICES){
        _XDPRINTF_("%s: Halting!. numentries_sysdev_memioregions >= MAX_PLATFORM_DEVICES(%u)\n",
                   __func__, MAX_PLATFORM_DEVICES);
        HALT();
    }

    //add LAPIC device
    sysdev_memioregions[numentries_sysdev_memioregions].b=PCI_BUS_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].d=PCI_DEVICE_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].f=0;
    sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=PCI_VENDOR_ID_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].device_id=PCI_DEVICE_ID_XMHFGEEC_LAPIC;
    sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_LAPIC;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=X86SMP_LAPIC_MEMORYADDRESS;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=X86SMP_LAPIC_MEMORYADDRESS + PAGE_SIZE_4K;
    for(i=1; i < PCI_CONF_MAX_BARS; i++){
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
    }
    numentries_sysdev_memioregions++;

    //add TPM
    sysdev_memioregions[numentries_sysdev_memioregions].b=PCI_BUS_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].d=PCI_DEVICE_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].f=0;
    sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=PCI_VENDOR_ID_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].device_id=PCI_DEVICE_ID_XMHFGEEC_TPM;
    sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_TPM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=TPM_LOCALITY_BASE;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=TPM_LOCALITY_BASE + PAGE_SIZE_4K;
    for(i=1; i < PCI_CONF_MAX_BARS; i++){
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
    }
    numentries_sysdev_memioregions++;

    //add TXT
    sysdev_memioregions[numentries_sysdev_memioregions].b=PCI_BUS_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].d=PCI_DEVICE_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].f=0;
    sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=PCI_VENDOR_ID_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].device_id=PCI_DEVICE_ID_XMHFGEEC_TXT;
    sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_TXT;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=TXT_PRIV_CONFIG_REGS_BASE;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=TXT_PRIV_CONFIG_REGS_BASE + PAGE_SIZE_4K;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1].addr_start=TXT_PUB_CONFIG_REGS_BASE;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1].addr_end=TXT_PUB_CONFIG_REGS_BASE + PAGE_SIZE_4K;
    for(i=2; i < PCI_CONF_MAX_BARS; i++){
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
    }
    numentries_sysdev_memioregions++;

#if defined (__DEBUG_SERIAL__)
    //add SERIAL0
    sysdev_memioregions[numentries_sysdev_memioregions].b=PCI_BUS_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].d=PCI_DEVICE_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].f=0;
    sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=PCI_VENDOR_ID_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].device_id=PCI_DEVICE_ID_XMHFGEEC_SERIAL0;
    sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_SERIAL0;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_IO;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=DEBUG_PORT;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=DEBUG_PORT+0x8;
    for(i=1; i < PCI_CONF_MAX_BARS; i++){
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
    }
    numentries_sysdev_memioregions++;
#endif

    //add IOMMU
	if(!xmhfhw_platform_x86pc_vtd_scanfor_drhd_units()){
        _XDPRINTF_("%s: unable to scan for DRHD units. halting!\n", __func__);
		HALT();
	}

    _XDPRINTF_("%s: Vt-d: maxhandle = %u, dmar table addr=0x%08x\n", __func__,
                (u32)vtd_drhd_maxhandle, (u32)vtd_dmar_table_physical_address);

    for(drhd_handle =0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
        sysdev_memioregions[numentries_sysdev_memioregions].b=PCI_BUS_XMHFGEEC;
        sysdev_memioregions[numentries_sysdev_memioregions].d=PCI_DEVICE_XMHFGEEC;
        sysdev_memioregions[numentries_sysdev_memioregions].f=drhd_handle;
        sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=PCI_VENDOR_ID_XMHFGEEC;
        sysdev_memioregions[numentries_sysdev_memioregions].device_id=PCI_DEVICE_ID_XMHFGEEC_IOMMU;
        sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_IOMMU;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=vtd_drhd[drhd_handle].regbaseaddr;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=vtd_drhd[drhd_handle].regbaseaddr + PAGE_SIZE_4K;
        for(i=1; i < PCI_CONF_MAX_BARS; i++){
            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
        }
        numentries_sysdev_memioregions++;
    }


    //enumerate and add rest of the system devices on the PCI bus
	for(b=0; b < PCI_BUS_MAX; b++){
		for(d=0; d < PCI_DEVICE_MAX; d++){
			for(f=0; f < PCI_FUNCTION_MAX; f++){
				u32 vendor_id, device_id;
				u32 bar_value, i;
				u8 hdr_type;
				u16 command;

				//read device and vendor ids, if no device then both will be 0xFFFF
				xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_VENDOR_ID, sizeof(u16), &vendor_id);
				xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_DEVICE_ID, sizeof(u16), &device_id);

				if(vendor_id == 0xFFFF && device_id == 0xFFFF)
					break;

                if(numentries_sysdev_memioregions >= MAX_PLATFORM_DEVICES){
                    _XDPRINTF_("%s: Halting!. numentries_sysdev_memioregions >= MAX_PLATFORM_DEVICES(%u)\n",
                               __func__, MAX_PLATFORM_DEVICES);
                    HALT();
                }

                xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_HEADER_TYPE, sizeof(u8), &hdr_type);
                xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(u16), &command);

                //_XDPRINTF_("Device %x:%x:%x(%x:%x) HDR=%x, CMD=%x\n",
                //       b, d, f, vendor_id, device_id, hdr_type, command);
                sysdev_memioregions[numentries_sysdev_memioregions].b=b;
                sysdev_memioregions[numentries_sysdev_memioregions].d=d;
                sysdev_memioregions[numentries_sysdev_memioregions].f=f;
                sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=vendor_id;
                sysdev_memioregions[numentries_sysdev_memioregions].device_id=device_id;

                if(hdr_type == 0x80 || hdr_type == 0x0)
                    sysdev_memioregions[numentries_sysdev_memioregions].dtype=SYSDEV_MEMIOREGIONS_DTYPE_GENERAL;
                else if (hdr_type == 0x81 || hdr_type == 0x1)
                    sysdev_memioregions[numentries_sysdev_memioregions].dtype=SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE;
                else
                    sysdev_memioregions[numentries_sysdev_memioregions].dtype=SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN;

                //disable decode
                xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(u16), (command & ~(0x3)) ) ;


                //size BARs
                for(i=0; i < PCI_CONF_MAX_BARS; i++){
                    if(i >= 2 && (hdr_type == 0x81 || hdr_type == 0x1)){
                        //for PCI-to-PCI bridge devices only BAR0 and BAR1 are valid BARs
                        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
                        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
                        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
                    }else{
                        //for general devices BAR0-BAR5 are valid BARs
                        u32 bar_size;
                        xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), &bar_value);
                        if(bar_value){
                            if(bar_value & 0x1){ //I/O
                                xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), 0xFFFFFFFFUL);
                                xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), &bar_size);
                                bar_size = bar_size & ~(0x1);
                                bar_size = ~(bar_size);
                                bar_size++;

                                //_XDPRINTF_("  BAR-%u, IO, range=%x to %x\n", i,
                                //           (u16)(bar_value & ~(0x1)), (u16)((bar_value & ~(0x1)) + bar_size) ) ;
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_IO;
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=(u16)(bar_value & ~(0x1));
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=(u16)((bar_value & ~(0x1)) + bar_size);

                           }else{
                                //memory
                                xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), 0xFFFFFFFFUL);
                                xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), &bar_size);
                                bar_size = bar_size & ~(0xF);
                                bar_size = ~(bar_size);
                                bar_size++;

                                //_XDPRINTF_("  BAR-%u, Mem, range=%x-%x\n", i,
                                //           (bar_value & ~(0xF)), (bar_value & ~(0xF)) + bar_size) ;
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=(bar_value & ~(0xF));
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=(bar_value & ~(0xF)) + bar_size;

                            }

                            xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), bar_value);
                        }else{
                            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
                            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
                            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
                        }
                    }
                }


                //restore command register
                xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(u16), command);
                numentries_sysdev_memioregions++;
            }
		}
	}


    //be verbose about the system devices and their MM(IO) extents
    {
        u32 i, j;
        for(i=0; i <numentries_sysdev_memioregions; i++){
            _XDPRINTF_("Device idx=%u, %x:%x:%x (vid:did=%x:%x, type=%x)...\n", i, sysdev_memioregions[i].b,
                       sysdev_memioregions[i].d, sysdev_memioregions[i].f, sysdev_memioregions[i].vendor_id,
                       sysdev_memioregions[i].device_id, sysdev_memioregions[i].dtype);
            for(j=0; j < PCI_CONF_MAX_BARS; j++){
                switch(sysdev_memioregions[i].memioextents[j].extent_type){
                    case _MEMIOREGIONS_EXTENTS_TYPE_IO:
                        _XDPRINTF_("  IO region: %x - %x\n", sysdev_memioregions[i].memioextents[j].addr_start,
                                        sysdev_memioregions[i].memioextents[j].addr_end);
                        break;

                    case _MEMIOREGIONS_EXTENTS_TYPE_MEM:
                        _XDPRINTF_("  MEM region: %x - %x\n", sysdev_memioregions[i].memioextents[j].addr_start,
                                        sysdev_memioregions[i].memioextents[j].addr_end);
                        break;

                    default:
                        break;
                }
            }
        }
    }

}
