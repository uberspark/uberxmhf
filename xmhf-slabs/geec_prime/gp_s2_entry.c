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

static u64 _xcsmp_ap_entry_lock = 1;
static u64 _ap_cr3=0;
void geec_prime_setup_slab_iotbl(void);
//void __xmhfhic_smp_cpu_x86_smpinitialize_commonstart(void);
void _geec_prime_setup_cpustate(void);


static void __xmhfhic_vmx_gathermemorytypes(void);
static void __xmhfhic_smp_cpu_x86_wakeupAPs(void);
static void __xmhfhic_smp_container_vmx_wakeupAPs(void);









void gp_s2_entry(void){

	//setup slab system device allocation and device page tables
	xmhfhic_arch_setup_slab_device_allocation();


	//gather memory types for EPT (for guest slabs)
	__xmhfhic_vmx_gathermemorytypes();
	_XDPRINTF_("%s: gathered EPT memory types\n", __func__);


	//setup (unverified) slab iotbl
	gp_s2_setupiotbl();


	//setup slab memory page tables
	//xmhfhic_arch_setup_slab_mem_page_tables();
	gp_s2_setupmempgtbl();


	//switch to prime page tables
	_XDPRINTF_("Proceeding to switch to GEEC_PRIME pagetables...\n");
	//CASM_FUNCCALL(write_cr3,(u32)xmhfgeec_slab_info_table[XMHFGEEC_SLAB_GEEC_PRIME].mempgtbl_cr3);
	CASM_FUNCCALL(write_cr3,(u32)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);
	_XDPRINTF_("Switched to GEEC_PRIME pagetables...\n");


	//setup base CPU data structures
	xmhfhic_arch_setup_base_cpu_data_structures();

	//save cpu MTRR state which we will later replicate on all APs
	xmhfhw_cpu_x86_save_mtrrs(&_mtrrs);

	//save page table base which we will later replicate on all APs
	_ap_cr3 = CASM_FUNCCALL(read_cr3,CASM_NOPARAM);

	//wake up APS
	if(xcbootinfo->cpuinfo_numentries > 1){
	  __xmhfhic_smp_container_vmx_wakeupAPs();
	}

	//fall through to common code
	_XDPRINTF_("%s: Relinquishing BSP thread and moving to common...\n", __func__);
	gp_s4_s6_entry();

	//we should never get here
	_XDPRINTF_("%s:%u: Must never get here. Halting\n", __func__, __LINE__);
	HALT();


}






























//////////////////////////////////////////////////////////////////////////////
//setup slab device allocation (sda)



//DMA Remapping Hardware Unit Definitions
static VTD_DRHD vtd_drhd[VTD_MAX_DRHD];
static u32 vtd_num_drhd=0;	//total number of DMAR h/w units
static bool vtd_drhd_scanned=false;	//set to true once DRHD units have been scanned in the system

static vtd_drhd_handle_t vtd_drhd_maxhandle=0;
static u32 vtd_dmar_table_physical_address=0;




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




    //enumerate system devices
    _sda_enumerate_system_devices();

    //initialize slab device mappings
    _geec_prime_sda_populate_slabdevicemap();

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
















































//---gather memory types for system physical memory------------------------------
static void __xmhfhic_vmx_gathermemorytypes(void){
 	u32 eax, ebx, ecx, edx;
	u32 index=0;
	u32 num_vmtrrs=0;	//number of variable length MTRRs supported by the CPU
	u64 msr_value;

	//0. sanity check
  	//check MTRR support
  	eax=0x00000001;
  	ecx=0x00000000;
    CASM_FUNCCALL(xmhfhw_cpu_cpuid,0x00000001, &eax, &ebx, &ecx, &edx);

  	if( !(edx & (u32)(1 << 12)) ){
  		_XDPRINTF_("\n%s: CPU does not support MTRRs!", __func__);
  		HALT();
  	}

  	//check MTRR caps
	msr_value = CASM_FUNCCALL(rdmsr64, IA32_MTRRCAP);
	eax = (u32)msr_value;
	edx = (u32)(msr_value >> 32);

	num_vmtrrs = (u8)eax;
  	_XDPRINTF_("\nIA32_MTRRCAP: VCNT=%u, FIX=%u, WC=%u, SMRR=%u",
  		num_vmtrrs, ((eax & (1 << 8)) >> 8),  ((eax & (1 << 10)) >> 10),
  			((eax & (1 << 11)) >> 11));
	//sanity check that fixed MTRRs are supported
  	HALT_ON_ERRORCOND( ((eax & (1 << 8)) >> 8) );
  	//ensure number of variable MTRRs are within the maximum supported
  	HALT_ON_ERRORCOND( (num_vmtrrs <= MAX_VARIABLE_MEMORYTYPE_ENTRIES) );


	#ifndef __XMHF_VERIFICATION__
	//1. clear memorytypes array
	memset((void *)&_vmx_ept_memorytypes, 0, sizeof(struct _memorytype) * MAX_MEMORYTYPE_ENTRIES);
	#endif

	//2. grab memory types using FIXED MTRRs
    //0x00000000-0x0007FFFF
	msr_value = CASM_FUNCCALL(rdmsr64, IA32_MTRR_FIX64K_00000);
	eax = (u32)msr_value;
	edx = (u32)(msr_value >> 32);

    _vmx_ept_memorytypes[index].startaddr = 0x00000000; _vmx_ept_memorytypes[index].endaddr = 0x0000FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x00010000; _vmx_ept_memorytypes[index].endaddr = 0x0001FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x00020000; _vmx_ept_memorytypes[index].endaddr = 0x0002FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x00030000; _vmx_ept_memorytypes[index].endaddr = 0x0003FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x00040000; _vmx_ept_memorytypes[index].endaddr = 0x0004FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x00050000; _vmx_ept_memorytypes[index].endaddr = 0x0005FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x00060000; _vmx_ept_memorytypes[index].endaddr = 0x0006FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x00070000; _vmx_ept_memorytypes[index].endaddr = 0x0007FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x00080000-0x0009FFFF
  	msr_value = CASM_FUNCCALL(rdmsr64, IA32_MTRR_FIX16K_80000);
	eax = (u32)msr_value;
	edx = (u32)(msr_value >> 32);


    _vmx_ept_memorytypes[index].startaddr = 0x00080000; _vmx_ept_memorytypes[index].endaddr = 0x00083FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x00084000; _vmx_ept_memorytypes[index].endaddr = 0x00087FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x00088000; _vmx_ept_memorytypes[index].endaddr = 0x0008BFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x0008C000; _vmx_ept_memorytypes[index].endaddr = 0x0008FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x00090000; _vmx_ept_memorytypes[index].endaddr = 0x00093FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x00094000; _vmx_ept_memorytypes[index].endaddr = 0x00097FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x00098000; _vmx_ept_memorytypes[index].endaddr = 0x0009BFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x0009C000; _vmx_ept_memorytypes[index].endaddr = 0x0009FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000A0000-0x000BFFFF
    	msr_value = CASM_FUNCCALL(rdmsr64, IA32_MTRR_FIX16K_A0000);
	eax = (u32)msr_value;
	edx = (u32)(msr_value >> 32);

    _vmx_ept_memorytypes[index].startaddr = 0x000A0000; _vmx_ept_memorytypes[index].endaddr = 0x000A3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000A4000; _vmx_ept_memorytypes[index].endaddr = 0x000A7FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000A8000; _vmx_ept_memorytypes[index].endaddr = 0x000ABFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000AC000; _vmx_ept_memorytypes[index].endaddr = 0x000AFFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000B0000; _vmx_ept_memorytypes[index].endaddr = 0x000B3FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000B4000; _vmx_ept_memorytypes[index].endaddr = 0x000B7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000B8000; _vmx_ept_memorytypes[index].endaddr = 0x000BBFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000BC000; _vmx_ept_memorytypes[index].endaddr = 0x000BFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000C0000-0x000C7FFF
       	msr_value = CASM_FUNCCALL(rdmsr64, IA32_MTRR_FIX4K_C0000);
	eax = (u32)msr_value;
	edx = (u32)(msr_value >> 32);

    _vmx_ept_memorytypes[index].startaddr = 0x000C0000; _vmx_ept_memorytypes[index].endaddr = 0x000C0FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000C1000; _vmx_ept_memorytypes[index].endaddr = 0x000C1FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000C2000; _vmx_ept_memorytypes[index].endaddr = 0x000C2FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000C3000; _vmx_ept_memorytypes[index].endaddr = 0x000C3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000C4000; _vmx_ept_memorytypes[index].endaddr = 0x000C4FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000C5000; _vmx_ept_memorytypes[index].endaddr = 0x000C5FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000C6000; _vmx_ept_memorytypes[index].endaddr = 0x000C6FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000C7000; _vmx_ept_memorytypes[index].endaddr = 0x000C7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000C8000-0x000C8FFF
       	msr_value = CASM_FUNCCALL(rdmsr64, IA32_MTRR_FIX4K_C8000);
	eax = (u32)msr_value;
	edx = (u32)(msr_value >> 32);

    _vmx_ept_memorytypes[index].startaddr = 0x000C8000; _vmx_ept_memorytypes[index].endaddr = 0x000C8FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000C9000; _vmx_ept_memorytypes[index].endaddr = 0x000C9FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000CA000; _vmx_ept_memorytypes[index].endaddr = 0x000CAFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000CB000; _vmx_ept_memorytypes[index].endaddr = 0x000CBFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000CC000; _vmx_ept_memorytypes[index].endaddr = 0x000CCFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000CD000; _vmx_ept_memorytypes[index].endaddr = 0x000CDFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000CE000; _vmx_ept_memorytypes[index].endaddr = 0x000CEFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000CF000; _vmx_ept_memorytypes[index].endaddr = 0x000CFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000D0000-0x000D7FFF
       	msr_value = CASM_FUNCCALL(rdmsr64, IA32_MTRR_FIX4K_D0000);
	eax = (u32)msr_value;
	edx = (u32)(msr_value >> 32);

    _vmx_ept_memorytypes[index].startaddr = 0x000D0000; _vmx_ept_memorytypes[index].endaddr = 0x000D0FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000D1000; _vmx_ept_memorytypes[index].endaddr = 0x000D1FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000D2000; _vmx_ept_memorytypes[index].endaddr = 0x000D2FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000D3000; _vmx_ept_memorytypes[index].endaddr = 0x000D3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000D4000; _vmx_ept_memorytypes[index].endaddr = 0x000D4FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000D5000; _vmx_ept_memorytypes[index].endaddr = 0x000D5FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000D6000; _vmx_ept_memorytypes[index].endaddr = 0x000D6FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000D7000; _vmx_ept_memorytypes[index].endaddr = 0x000D7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000D8000-0x000DFFFF
       	msr_value = CASM_FUNCCALL(rdmsr64, IA32_MTRR_FIX4K_D8000);
	eax = (u32)msr_value;
	edx = (u32)(msr_value >> 32);

    _vmx_ept_memorytypes[index].startaddr = 0x000D8000; _vmx_ept_memorytypes[index].endaddr = 0x000D8FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000D9000; _vmx_ept_memorytypes[index].endaddr = 0x000D9FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000DA000; _vmx_ept_memorytypes[index].endaddr = 0x000DAFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000DB000; _vmx_ept_memorytypes[index].endaddr = 0x000DBFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000DC000; _vmx_ept_memorytypes[index].endaddr = 0x000DCFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000DD000; _vmx_ept_memorytypes[index].endaddr = 0x000DDFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000DE000; _vmx_ept_memorytypes[index].endaddr = 0x000DEFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000DF000; _vmx_ept_memorytypes[index].endaddr = 0x000DFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000E0000-0x000E7FFF
       	msr_value = CASM_FUNCCALL(rdmsr64, IA32_MTRR_FIX4K_E0000);
	eax = (u32)msr_value;
	edx = (u32)(msr_value >> 32);

    _vmx_ept_memorytypes[index].startaddr = 0x000E0000; _vmx_ept_memorytypes[index].endaddr = 0x000E0FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000E1000; _vmx_ept_memorytypes[index].endaddr = 0x000E1FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000E2000; _vmx_ept_memorytypes[index].endaddr = 0x000E2FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000E3000; _vmx_ept_memorytypes[index].endaddr = 0x000E3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000E4000; _vmx_ept_memorytypes[index].endaddr = 0x000E4FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000E5000; _vmx_ept_memorytypes[index].endaddr = 0x000E5FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000E6000; _vmx_ept_memorytypes[index].endaddr = 0x000E6FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000E7000; _vmx_ept_memorytypes[index].endaddr = 0x000E7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000E8000-0x000EFFFF
       	msr_value = CASM_FUNCCALL(rdmsr64, IA32_MTRR_FIX4K_E8000);
	eax = (u32)msr_value;
	edx = (u32)(msr_value >> 32);

    _vmx_ept_memorytypes[index].startaddr = 0x000E8000; _vmx_ept_memorytypes[index].endaddr = 0x000E8FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000E9000; _vmx_ept_memorytypes[index].endaddr = 0x000E9FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000EA000; _vmx_ept_memorytypes[index].endaddr = 0x000EAFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000EB000; _vmx_ept_memorytypes[index].endaddr = 0x000EBFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000EC000; _vmx_ept_memorytypes[index].endaddr = 0x000ECFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000ED000; _vmx_ept_memorytypes[index].endaddr = 0x000EDFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000EE000; _vmx_ept_memorytypes[index].endaddr = 0x000EEFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000EF000; _vmx_ept_memorytypes[index].endaddr = 0x000EFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000F0000-0x000F7FFF
       	msr_value = CASM_FUNCCALL(rdmsr64, IA32_MTRR_FIX4K_F0000);
	eax = (u32)msr_value;
	edx = (u32)(msr_value >> 32);

    _vmx_ept_memorytypes[index].startaddr = 0x000F0000; _vmx_ept_memorytypes[index].endaddr = 0x000F0FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000F1000; _vmx_ept_memorytypes[index].endaddr = 0x000F1FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000F2000; _vmx_ept_memorytypes[index].endaddr = 0x000F2FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000F3000; _vmx_ept_memorytypes[index].endaddr = 0x000F3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000F4000; _vmx_ept_memorytypes[index].endaddr = 0x000F4FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000F5000; _vmx_ept_memorytypes[index].endaddr = 0x000F5FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000F6000; _vmx_ept_memorytypes[index].endaddr = 0x000F6FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000F7000; _vmx_ept_memorytypes[index].endaddr = 0x000F7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000F8000-0x000FFFFF
       	msr_value = CASM_FUNCCALL(rdmsr64, IA32_MTRR_FIX4K_F8000);
	eax = (u32)msr_value;
	edx = (u32)(msr_value >> 32);

    _vmx_ept_memorytypes[index].startaddr = 0x000F8000; _vmx_ept_memorytypes[index].endaddr = 0x000F8FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000F9000; _vmx_ept_memorytypes[index].endaddr = 0x000F9FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000FA000; _vmx_ept_memorytypes[index].endaddr = 0x000FAFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000FB000; _vmx_ept_memorytypes[index].endaddr = 0x000FBFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000FC000; _vmx_ept_memorytypes[index].endaddr = 0x000FCFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000FD000; _vmx_ept_memorytypes[index].endaddr = 0x000FDFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000FE000; _vmx_ept_memorytypes[index].endaddr = 0x000FEFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000FF000; _vmx_ept_memorytypes[index].endaddr = 0x000FFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);


	//3. grab memory types using variable length MTRRs
	{
		u64 paddrmask = 0x0000000FFFFFFFFFULL; //36-bits physical address, TODO: need to make this dynamic
		u64 vMTRR_base, vMTRR_mask;
		u32 msrval=IA32_MTRR_PHYSBASE0;
		u32 i;

		for(i=0; i < num_vmtrrs; i++){
			msr_value = CASM_FUNCCALL(rdmsr64, msrval);
			eax = (u32)msr_value;
			edx = (u32)(msr_value >> 32);

			vMTRR_base = ((u64)edx << 32) | (u64)eax;
			msrval++;
			msr_value = CASM_FUNCCALL(rdmsr64, msrval);
			eax = (u32)msr_value;
			edx = (u32)(msr_value >> 32);

			vMTRR_mask = ((u64)edx << 32) | (u64)eax;
			msrval++;
			if( (vMTRR_mask & ((u64)1 << 11)) ){
				_vmx_ept_memorytypes[index].startaddr = (vMTRR_base & (u64)0xFFFFFFFFFFFFF000ULL);
				_vmx_ept_memorytypes[index].endaddr = (vMTRR_base & (u64)0xFFFFFFFFFFFFF000ULL) +
					(u64) (~(vMTRR_mask & (u64)0xFFFFFFFFFFFFF000ULL) &
						paddrmask);
				_vmx_ept_memorytypes[index++].type = ((u32)vMTRR_base & (u32)0x000000FF);
			}else{
				_vmx_ept_memorytypes[index++].invalid = 1;
			}
		}
	}

	_XDPRINTF_("\n%s: gathered MTRR details, number of entries=%u", __func__, index);
	HALT_ON_ERRORCOND( index <= (MAX_MEMORYTYPE_ENTRIES+1) );

  //[debug: dump the contents of _vmx_ept_memorytypes]
  //{
  //  int i;
  //  for(i=0; i < MAX_MEMORYTYPE_ENTRIES; i++){
  //    _XDPRINTF_("\nrange  0x%016llx-0x%016llx (type=%u)",
  //      _vmx_ept_memorytypes[i].startaddr, _vmx_ept_memorytypes[i].endaddr, _vmx_ept_memorytypes[i].type);
  //  }
  //}


}




















































//////
// (SMP) CPU state setup code
//////




//////////////////////////////////////////////////////////////////////////////
// switch to smp




#if 0
static void __xmhfhic_smp_cpu_x86_savecpumtrrstate(void){
	xmhfhw_cpu_x86_save_mtrrs(&_mtrrs);
}
#endif // 0

#if 0
static void __xmhfhic_smp_cpu_x86_restorecpumtrrstate(void){
	xmhfhw_cpu_x86_restore_mtrrs(&_mtrrs);
}
#endif // 0

//wake up APs using the LAPIC by sending the INIT-SIPI-SIPI IPI sequence
static void __xmhfhic_smp_cpu_x86_wakeupAPs(void){
	u32 eax, edx;
	volatile u32 *icr;
	u64 msr_value;

	//read LAPIC base address from MSR
       	msr_value = CASM_FUNCCALL(rdmsr64, MSR_APIC_BASE);
	eax = (u32)msr_value;
	edx = (u32)(msr_value >> 32);

	HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G

	//construct the command register address (offset 0x300)
	icr = (u32 *) (((u32)eax & 0xFFFFF000UL) + 0x300);

	//our AP boot-strap code is at physical memory location 0x10000.
	//so use 0x10 as the vector (0x10000/0x1000 = 0x10)

	//send INIT
	*icr = 0x000c4500UL;

	xmhf_baseplatform_arch_x86_udelay(10000);

	//wait for command completion
	{
		u32 val;
		do{
		  val = *icr;
		}while( (val & 0x1000) );
	}

	//send SIPI (twice as per the MP protocol)
	{
		int i;
		for(i=0; i < 2; i++){
			*icr = 0x000c4610UL;
			xmhf_baseplatform_arch_x86_udelay(200);
			//wait for command completion
			{
			  u32 val;
			  do{
				val = *icr;
			  }while( (val & 0x1000) );
			}
		}
	}

}



//wake up application processors (cores) in the system
static void __xmhfhic_smp_container_vmx_wakeupAPs(void){
    static x86smp_apbootstrapdata_t apdata;

    apdata.ap_cr3 = CASM_FUNCCALL(read_cr3,CASM_NOPARAM);
    apdata.ap_cr4 = CASM_FUNCCALL(read_cr4,CASM_NOPARAM);
    apdata.ap_entrypoint = (u32)&gp_s3_apstacks;
    apdata.ap_gdtdesc_limit = sizeof(apdata.ap_gdt) - 1;
    //apdata.ap_gdtdesc_base = (X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_gdt);
    apdata.ap_gdtdesc_base = (X86SMP_APBOOTSTRAP_DATASEG << 4) + 48;
    apdata.ap_cs_selector = __CS_CPL0;
    apdata.ap_eip = (X86SMP_APBOOTSTRAP_CODESEG << 4);
    //apdata.cpuidtable = (u32)&__xmhfhic_x86vmx_cpuidtable;
    apdata.ap_gdt[0] = 0x0000000000000000ULL;
    apdata.ap_gdt[1] = 0x00cf9a000000ffffULL;
    apdata.ap_gdt[2] = 0x00cf92000000ffffULL;

    _XDPRINTF_("%s: sizeof(apdata)=%u bytes\n", __func__, sizeof(apdata));
    _XDPRINTF_("  apdata.ap_gdtdesc_limit at %08x\n", &apdata.ap_gdtdesc_limit);
    _XDPRINTF_("  apdata.ap_gdt at %08x\n", &apdata.ap_gdt);

    memcpy((void *)(X86SMP_APBOOTSTRAP_DATASEG << 4), (void *)&apdata, sizeof(apdata));

    memcpy((void *)(X86SMP_APBOOTSTRAP_CODESEG << 4), (void *)&gp_s3_entry, PAGE_SIZE_4K);

#if defined (__DRT__)
    {
        txt_heap_t *txt_heap;
        //os_mle_data_t *os_mle_data;
        mle_join_t *mle_join;
        //sinit_mle_data_t sinit_mle_data;
        os_sinit_data_t os_sinit_data;

        txt_heap = get_txt_heap();
        //os_mle_data = get_os_mle_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE));
        //xmhfhw_sysmemaccess_copy(&sinit_mle_data,
	//	get_sinit_mle_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE)),
	//	sizeof(sinit_mle_data_t));
        xmhfhw_sysmemaccess_copy(&os_sinit_data,
		get_os_sinit_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE)),
		sizeof(os_sinit_data_t));

        // enable SMIs on BSP before waking APs (which will enable them on APs)
        // because some SMM may take immediate SMI and hang if AP gets in first
        //_XDPRINTF_("Enabling SMIs on BSP\n");
        //__getsec_smctrl();

        //mle_join = (mle_join_t *)((u32)(X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_gdtdesc_limit));
        mle_join = (mle_join_t *)((u32)(X86SMP_APBOOTSTRAP_DATASEG << 4) + 16);

        _XDPRINTF_("\nBSP: mle_join.gdt_limit = %x", mle_join->gdt_limit);
        _XDPRINTF_("\nBSP: mle_join.gdt_base = %x", mle_join->gdt_base);
        _XDPRINTF_("\nBSP: mle_join.seg_sel = %x", mle_join->seg_sel);
        _XDPRINTF_("\nBSP: mle_join.entry_point = %x", mle_join->entry_point);

        write_priv_config_reg(TXTCR_MLE_JOIN, (uint64_t)(unsigned long)mle_join);

        if (os_sinit_data.capabilities & TXT_CAPS_T_RLP_WAKE_MONITOR) {
            _XDPRINTF_("\nBSP: joining RLPs to MLE with MONITOR wakeup");
            //_XDPRINTF_("\nBSP: rlp_wakeup_addr = 0x%x", sinit_mle_data.rlp_wakeup_addr);
            // *((uint32_t *)(unsigned long)(sinit_mle_data.rlp_wakeup_addr)) = 0x01;
	    xmhfhw_sysmemaccess_writeu32(
		(get_sinit_mle_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE)) + offsetof(sinit_mle_data_t, rlp_wakeup_addr) ),
					0x01);


        }else {
            _XDPRINTF_("\nBSP: joining RLPs to MLE with GETSEC[WAKEUP]");
            __getsec_wakeup();
            _XDPRINTF_("\nBSP: GETSEC[WAKEUP] completed");
        }
    }

#else //!__DRT__

    _XDPRINTF_("\nBSP: Using APIC to awaken APs...");
    __xmhfhic_smp_cpu_x86_wakeupAPs();
    _XDPRINTF_("\nBSP: APs should be awake.");

#endif


}



#if 0
//initialize SMP
static bool __xmhfhic_smp_arch_smpinitialize(void){
	u32 i;

    //save cpu MTRR state which we will later replicate on all APs
	#if !defined(__XMHF_VERIFICATION__)
	__xmhfhic_smp_cpu_x86_savecpumtrrstate();
    #endif

    //save page table base which we will later replicate on all APs
    _ap_cr3 = CASM_FUNCCALL(read_cr3,CASM_NOPARAM);

	//wake up APS
	if(xcbootinfo->cpuinfo_numentries > 1){
	  __xmhfhic_smp_container_vmx_wakeupAPs();
	}

	//fall through to common code
	_XDPRINTF_("%s: Relinquishing BSP thread and moving to common...\n", __func__);
	__xmhfhic_smp_cpu_x86_smpinitialize_commonstart();

	_XDPRINTF_("%s:%u: Must never get here. Halting\n", __func__, __LINE__);
	HALT();

}
#endif





#if 0
void xmhfhic_arch_switch_to_smp(void){
/*	//initialize cpu table and total platform CPUs
	{
	    u32 i, j;
	    for(i=0; i < MAX_X86_APIC_ID; i++)
           // __xmhfhic_x86vmx_cpuidtable[i] = 0xFFFFFFFFFFFFFFFFULL;
            __xmhfhic_x86vmx_cpuidtable[i] = 0xFFFFFFFFUL;

	    for(i=0; i < xcbootinfo->cpuinfo_numentries; i++){
            u64 value = i;

            if(xcbootinfo->cpuinfo_buffer[i].isbsp)
                //value |= 0x8000000000000000ULL;
                value |= 0x80000000UL;

            //XXX: TODO sanity check xcbootinfo->cpuinfo_buffer[i].lapic_id < MAX_X86_APIC_ID
            __xmhfhic_x86vmx_cpuidtable[xcbootinfo->cpuinfo_buffer[i].lapic_id] = value;
        }
	}*/

    __xmhfhic_smp_arch_smpinitialize();

}
#endif

#if 0
void xmhfhic_smp_entry(u32 cpuid){
    //bool isbsp = (cpuid & 0x80000000UL) ? true : false;
    bool isbsp = xmhfhw_lapic_isbsp();
    #if defined (__XMHF_VERIFICATION__)
    cpuid = 0;
    isbsp = true;
    #endif // defined


    //[debug] halt all APs
    //if(!isbsp){
    //    _XDPRINTF_("%s[%u,%u]: esp=%08x. AP Halting!\n",
    //        __func__, (u16)cpuid, isbsp, CASM_FUNCCALL(read_esp,));
    //    HALT();
    //}

    _XDPRINTF_("%s[%u,%u]: esp=%08x. Starting...\n",
            __func__, cpuid, isbsp, CASM_FUNCCALL(read_esp,CASM_NOPARAM));

    xmhf_hic_arch_setup_cpu_state((u16)cpuid);

    //_XDPRINTF_("%s[%u,%u]: Halting!\n", __func__, (u16)cpuid, isbsp);
    //HALT();


    //relinquish HIC initialization and move on to the first slab
    _XDPRINTF_("%s[%u]: proceeding to call init slab at %x\n", __func__, (u16)cpuid,
                xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_INIT].entrystub);

    //xmhfhic_arch_relinquish_control_to_init_slab(cpuid,
    //    xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_INIT].entrystub,
    //    xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_INIT].archdata.mempgtbl_cr3,
    //    xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_INIT].archdata.slabtos[(u32)cpuid]);

    {
        slab_params_t sp;

        memset(&sp, 0, sizeof(sp));
        sp.cpuid = cpuid;
        sp.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
        sp.dst_slabid = XMHFGEEC_SLAB_XC_INIT;
        XMHF_SLAB_CALLNEW(&sp);
    }


    _XDPRINTF_("%s[%u,%u]: Should never be here. Halting!\n", __func__, (u16)cpuid, isbsp);
    HALT();

}
#endif // 0


//////////////////////////////////////////////////////////////////////////////





/////////////////////////////////////////////////////////////////////
// setup base CPU data structures

//initialize GDT
static void __xmhfhic_x86vmx_initializeGDT(void){
		u32 i;

		for(i=0; i < xcbootinfo->cpuinfo_numentries; i++){
            TSSENTRY *t;
            u32 tss_idx = xcbootinfo->cpuinfo_buffer[i].lapic_id;
            u32 tss_base=(u32)&__xmhfhic_x86vmx_tss[tss_idx].tss_mainblock;

            //TSS descriptor
            t= (TSSENTRY *)&__xmhfhic_x86vmx_gdt_start[(__TRSEL/8)+(i*2)];
            t->attributes1= 0xE9;
            t->limit16_19attributes2= 0x0;
            t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
            t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
            t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);
            //t->limit0_15=0x67;
            //t->limit0_15=sizeof(tss_t)-1;
            t->limit0_15=(4*PAGE_SIZE_4K)-1;

            _XDPRINTF_("%s: setup TSS CPU idx=%u with base address=%x, iobitmap=%x\n, size=%u bytes", __func__,
                       tss_idx, tss_base, (u32)&__xmhfhic_x86vmx_tss[tss_idx].tss_iobitmap, t->limit0_15);

		}

}

//initialize IDT
static void __xmhfhic_x86vmx_initializeIDT(void){
	u32 i;

	for(i=0; i < EMHF_XCPHANDLER_MAXEXCEPTIONS; i++){
		__xmhfhic_x86vmx_idt_start[i].isrLow= (u16)xmhfgeec_slab_info_table[XMHFGEEC_SLAB_GEEC_SENTINEL].slab_memoffset_entries[GEEC_SENTINEL_MEMOFFSETS_EXCEPTIONHANDLERS_IDX+i];
		__xmhfhic_x86vmx_idt_start[i].isrHigh= (u16) ( xmhfgeec_slab_info_table[XMHFGEEC_SLAB_GEEC_SENTINEL].slab_memoffset_entries[GEEC_SENTINEL_MEMOFFSETS_EXCEPTIONHANDLERS_IDX+i] >> 16 );
		__xmhfhic_x86vmx_idt_start[i].isrSelector = __CS_CPL0;
		__xmhfhic_x86vmx_idt_start[i].count=0x0;
		__xmhfhic_x86vmx_idt_start[i].type=0xEE;	//32-bit interrupt gate
                                //present=1, DPL=11b, system=0, type=1110b
        //__xmhfhic_x86vmx_idt_start[i].offset3263=0;
        //__xmhfhic_x86vmx_idt_start[i].reserved=0;
	}

}


//initialize TSS
static void __xmhfhic_x86vmx_initializeTSS(void){
		u32 i;

		//initialize TSS descriptors for all CPUs
		for(i=0; i < xcbootinfo->cpuinfo_numentries; i++){
            u32 tss_idx = xcbootinfo->cpuinfo_buffer[i].lapic_id;

            memset(&__xmhfhic_x86vmx_tss[tss_idx], 0, sizeof(__xmhfhic_x86vmx_tss[tss_idx]));
            tss_t *tss= (tss_t *)__xmhfhic_x86vmx_tss[tss_idx].tss_mainblock;
            tss->esp0 = (u32) ( &__xmhfhic_x86vmx_tss_stack[tss_idx] + sizeof(__xmhfhic_x86vmx_tss_stack[0]) );
            tss->ss0 = __DS_CPL0;
            tss->iotbl_addr = (u32)&__xmhfhic_x86vmx_tss[tss_idx].tss_iobitmap - (u32)&__xmhfhic_x86vmx_tss[tss_idx].tss_mainblock;
            _XDPRINTF_("%s: tss_idx=%u, iotbl_addr=%x\n", __func__, tss_idx,
                       tss->iotbl_addr);
		}
}


void xmhfhic_arch_setup_base_cpu_data_structures(void){

    //initialize GDT
    #if !defined(__XMHF_VERIFICATION__)
    __xmhfhic_x86vmx_initializeGDT();
    #endif

    //initialize IDT
    __xmhfhic_x86vmx_initializeIDT();

    //initialize TSS
    __xmhfhic_x86vmx_initializeTSS();

}






































//
///////
//void _geec_prime_setup_cpustate(void){


//    //we should never get here
//    _XDPRINTF_("Should never be here. Halting!\n");
//    HALT();
//
//}
































#if 0

    //debug
    _XDPRINTF_("Halting!\n");
    _XDPRINTF_("XMHF Tester Finished!\n");
    HALT();


void print_mtrrs(const mtrr_state_t *saved_state)
{
    //int i;

    //_XDPRINTF_("mtrr_def_type: e = %d, fe = %d, type = %x\n",
    //       saved_state->mtrr_def_type.e, saved_state->mtrr_def_type.fe,
    //       saved_state->mtrr_def_type.type );
    //_XDPRINTF_("mtrrs:\n");
    //_XDPRINTF_("\t\tbase\tmask\ttype\tv\n");
    //for ( i = 0; i < saved_state->num_var_mtrrs; i++ ) {
    //    _XDPRINTF_("\t\t%6.6x\t%6.6x\t%2.2x\t%d\n",
    //           saved_state->mtrr_physbases[i].base,
    //           saved_state->mtrr_physmasks[i].mask,
    //           saved_state->mtrr_physbases[i].type,
    //           saved_state->mtrr_physmasks[i].v );
    //}
}


#endif // 0
