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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec_prime.h>


//scan for IOMMU and halt if not present
//global variables set:
//vtd_drhd[] (struct representing a DRHD unit)
//vtd_num_drhd (number of DRHD units detected)
//vtd_dmar_table_physical_address (physical address of the DMAR table)

#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
uint32_t check_esp, check_eip = CASM_RET_EIP;

void hwm_vdriver_writeesp(uint32_t oldval, uint32_t newval){
	//@assert (newval >= ((uint32_t)&_init_bsp_cpustack + 4)) && (newval <= ((uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
}

void main(void){
	//populate hardware model stack and program counter
	hwm_cpu_gprs_esp = (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
	hwm_cpu_gprs_eip = check_eip;
	check_esp = hwm_cpu_gprs_esp; // pointing to top-of-stack

	//execute harness
	gp_s1_scaniommu();

	//@assert (vtd_drhd_maxhandle == 2);
	//@assert (vtd_drhd_scanned == true);
	//@assert (vtd_drhd[0].regbaseaddr ==0x00000000fed90000ULL);
	//@assert (vtd_drhd[0].iotlb_regaddr == 0x00000000fed90108ULL);
	//@assert (vtd_drhd[0].iva_regaddr == 0x00000000fed90100ULL);
	//@assert (vtd_drhd[1].regbaseaddr ==0x00000000fed91000ULL);
	//@assert (vtd_drhd[1].iotlb_regaddr == 0x00000000fed91108ULL);
	//@assert (vtd_drhd[1].iva_regaddr == 0x00000000fed91100ULL);

	//@assert hwm_cpu_gprs_esp == check_esp;
	//@assert hwm_cpu_gprs_eip == check_eip;
}
#endif

void gp_s1_scaniommu(void){
	ACPI_RSDP rsdp = {0};
	ACPI_RSDT rsdt = {0};
	uint32_t num_rsdtentries=0;
	uint32_t rsdtentries[ACPI_MAX_RSDT_ENTRIES];
	uint32_t status;
	VTD_DMAR dmar = {0};
	uint32_t i, dmarfound;
	uint32_t remappingstructuresaddrphys;

	//set maxhandle to 0 to start with. if we have any errors before
	//we finalize maxhandle we can just bail out
	vtd_drhd_maxhandle=0;

	//get ACPI RSDP
	status=uberspark_uobjrtl_hw__generic_x86_32_intel__acpi_getRSDP(&rsdp);
	if(status == 0){
		_XDPRINTF_("%s:%u unable to get ACPI RSDP. Halting!\n", __func__, __LINE__);
                CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
	}


#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_SERIAL__)
	_XDPRINTF_("rdsp.signature=%016llx\n", rsdp.signature);
	_XDPRINTF_("rdsp.checksum=%02x\n", rsdp.checksum);
	_XDPRINTF_("rdsp.oemid=%02x %02x %02x %02x %02x %02x\n",
		rsdp.oemid[0], rsdp.oemid[1], rsdp.oemid[2],
		rsdp.oemid[3], rsdp.oemid[4], rsdp.oemid[5]);
	_XDPRINTF_("rdsp.revision=%02x\n", rsdp.revision);
	_XDPRINTF_("rdsp.rsdtaddress=%08x\n", rsdp.rsdtaddress);
	_XDPRINTF_("rdsp.length=%08x\n", rsdp.length);
	_XDPRINTF_("rdsp.xsdtaddress=%016llx\n", rsdp.xsdtaddress);
	_XDPRINTF_("rdsp.xchecksum=%02x\n", rsdp.xchecksum);
	_XDPRINTF_("rdsp.rsvd0=%02x %02x %02x\n",
		rsdp.oemid[0], rsdp.oemid[1], rsdp.oemid[2]);
#endif //__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_SERIAL__


	//grab ACPI RSDT
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmem_copy_sys2obj, (uint8_t *)&rsdt, (uint8_t *)rsdp.rsdtaddress, sizeof(ACPI_RSDT));
	_XDPRINTF_("%s:%u RSDT at %08x, len=%u bytes, hdrlen=%u bytes\n",
		__func__, __LINE__, rsdp.rsdtaddress, rsdt.length, sizeof(ACPI_RSDT));


	#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_SERIAL__)
	_XDPRINTF_("rsdt.signature=%016llx\n", rsdt.signature);
	_XDPRINTF_("rsdt.length=%08x\n", rsdt.length);
	_XDPRINTF_("rsdt.revision=%02x\n", rsdt.revision);
	_XDPRINTF_("rsdt.checksum=%02x\n", rsdt.checksum);
	_XDPRINTF_("rsdt.oemid=%02x %02x %02x %02x %02x %02x\n",
		rsdt.oemid[0], rsdt.oemid[1], rsdt.oemid[2],
		rsdt.oemid[3], rsdt.oemid[4], rsdt.oemid[5]);
	_XDPRINTF_("rsdt.oemtableid=%016llx\n", rsdt.oemtableid);
	_XDPRINTF_("rsdt.oemrevision=%08x\n", rsdt.oemrevision);
	_XDPRINTF_("rsdt.creatorid=%08x\n", rsdt.creatorid);
	_XDPRINTF_("rsdt.creatorrevision=%08x\n", rsdt.creatorrevision);
	#endif //__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_SERIAL__




	//get the RSDT entry list
	num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT))/ sizeof(uint32_t);
	if(num_rsdtentries >= ACPI_MAX_RSDT_ENTRIES){
		_XDPRINTF_("%s:%u num_rsdtentries(%u) > ACPI_MAX_RSDT_ENTRIES (%u). Halting!\n",
			__func__, __LINE__, num_rsdtentries, ACPI_MAX_RSDT_ENTRIES);
                CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
	}

	_XDPRINTF_("%s:%u RSDT entry list at %08x, len=%u", __func__, __LINE__,
		(rsdp.rsdtaddress + sizeof(ACPI_RSDT)), num_rsdtentries);



	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmem_copy_sys2obj, (uint8_t *)&rsdtentries, (uint8_t *)(rsdp.rsdtaddress + sizeof(ACPI_RSDT)),
			sizeof(uint32_t)*num_rsdtentries);


	//find the VT-d DMAR table in the list (if any)
	for(i=0; i< num_rsdtentries; i++){
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmem_copy_sys2obj, (uint8_t *)&dmar, (uint8_t *)rsdtentries[i], sizeof(VTD_DMAR));
		if(dmar.signature == VTD_DMAR_SIGNATURE){
		  dmarfound=1;
			#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_SERIAL__)
			_XDPRINTF_("dmar.signature=%016llx\n", dmar.signature);
			_XDPRINTF_("dmar.length=%08x\n", dmar.length);
			_XDPRINTF_("dmar.revision=%02x\n", dmar.revision);
			_XDPRINTF_("dmar.checksum=%02x\n", dmar.checksum);
			_XDPRINTF_("dmar.oemid=%02x %02x %02x %02x %02x %02x\n",
				dmar.oemid[0], dmar.oemid[1], dmar.oemid[2],
				dmar.oemid[3], dmar.oemid[4], dmar.oemid[5]);
			_XDPRINTF_("dmar.oemtableid=%016llx\n", dmar.oemtableid);
			_XDPRINTF_("dmar.oemrevision=%08x\n", dmar.oemrevision);
			_XDPRINTF_("dmar.creatorid=%08x\n", dmar.creatorid);
			_XDPRINTF_("dmar.creatorrevision=%08x\n", dmar.creatorrevision);
			_XDPRINTF_("dmar.hostaddresswidth=%02x\n", dmar.hostaddresswidth);
			_XDPRINTF_("dmar.flags=%02x\n", dmar.flags);
			_XDPRINTF_("dmar.rsvd0=%02x %02x %02x %02x %02x %02x %02x %02x %02x %02x\n",
				dmar.oemid[0], dmar.oemid[1], dmar.oemid[2],
				dmar.oemid[3], dmar.oemid[4], dmar.oemid[5],
				dmar.oemid[6], dmar.oemid[7], dmar.oemid[8],
				dmar.oemid[9]);
			#endif //__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_SERIAL__

		  break;
		}
	}




	//if no DMAR table, bail out
	if(!dmarfound){
		_XDPRINTF_("%s:%u Error No DMAR table. Halting!", __func__, __LINE__);
                CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
	}

	vtd_dmar_table_physical_address = rsdtentries[i]; //DMAR table physical memory address;
	_XDPRINTF_("%s:%u DMAR at %08x", __func__, __LINE__, vtd_dmar_table_physical_address);




	//detect DRHDs in the DMAR table
	i=0;
	remappingstructuresaddrphys=vtd_dmar_table_physical_address+sizeof(VTD_DMAR);

	while(i < (dmar.length-sizeof(VTD_DMAR))){
		uint16_t type, length;
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmem_copy_sys2obj,(uint8_t *)&type, (uint8_t *)(remappingstructuresaddrphys+i), sizeof(uint16_t));
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmem_copy_sys2obj,(uint8_t *)&length, (uint8_t *)(remappingstructuresaddrphys+i+sizeof(uint16_t)), sizeof(uint16_t));

		switch(type){
			case  0:  //DRHD
				if(vtd_num_drhd >= VTD_MAX_DRHD){
					_XDPRINTF_("%s:%u vtd_num_drhd (%u) > VTD_MAX_DRHD (%u). Halting!", __func__,
						__LINE__, vtd_num_drhd, VTD_MAX_DRHD);
					CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
				}
				CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmem_copy_sys2obj, (uint8_t *)&vtd_drhd[vtd_num_drhd], (uint8_t *)(remappingstructuresaddrphys+i), length);
				vtd_num_drhd++;
				i+=(uint32_t)length;
				break;

			default:	//unknown type, we skip this
				i += (uint32_t)length;
				break;
		}
	}
    _XDPRINTF_("%s:%u total DRHDs detected= %u units\n", __func__, __LINE__, vtd_num_drhd);



    //populate IVA and IOTLB register addresses within all the DRHD unit
    //structures
    for(i=0; i < vtd_num_drhd; i++){
        VTD_ECAP_REG ecap;

        unpack_VTD_ECAP_REG(&ecap, uberspark_uobjrtl_hw__generic_x86_32_intel__vtd_reg_read(&vtd_drhd[i], VTD_ECAP_REG_OFF));
        vtd_drhd[i].iotlb_regaddr= vtd_drhd[i].regbaseaddr+(ecap.iro*16)+0x8;
        vtd_drhd[i].iva_regaddr= vtd_drhd[i].regbaseaddr+(ecap.iro*16);
    }


#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_SERIAL__)
	//[DEBUG]: be a little verbose about what we found
	_XDPRINTF_("%s: DMAR Devices:\n", __func__);
	for(i=0; i < vtd_num_drhd; i++){
		VTD_CAP_REG cap;
		VTD_ECAP_REG ecap;
		_XDPRINTF_("	Device %u type=%04x, length=%04x, flags=%02x, rsvdz0=%02x\n", i,
					vtd_drhd[i].type, vtd_drhd[i].length, vtd_drhd[i].flags, vtd_drhd[i].rsvdz0);
		_XDPRINTF_("	Device %u on PCI seg %04x; base=0x%016llx\n", i,
					vtd_drhd[i].pcisegment, vtd_drhd[i].regbaseaddr);
		unpack_VTD_CAP_REG(&cap, uberspark_uobjrtl_hw__generic_x86_32_intel__vtd_reg_read(&vtd_drhd[i], VTD_CAP_REG_OFF));
		_XDPRINTF_("		cap=0x%016llx\n", pack_VTD_CAP_REG(&cap));
		//ecap.value = uberspark_uobjrtl_hw__generic_x86_32_intel__vtd_reg_read(&vtd_drhd[i], VTD_ECAP_REG_OFF);
		unpack_VTD_ECAP_REG(&ecap, uberspark_uobjrtl_hw__generic_x86_32_intel__vtd_reg_read(&vtd_drhd[i], VTD_ECAP_REG_OFF));
		_XDPRINTF_("		ecap=0x%016llx\n", (uint64_t)pack_VTD_ECAP_REG(&ecap));
		_XDPRINTF_("	iotlb_regaddr=%08x, iva_regaddr=%08x\n",
					vtd_drhd[i].iotlb_regaddr, vtd_drhd[i].iva_regaddr);

	}
#endif // __UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_SERIAL__

	vtd_drhd_maxhandle = vtd_num_drhd;
	vtd_drhd_scanned = true;

	_XDPRINTF_("%s: Vt-d: maxhandle = %u, dmar table addr=0x%08x\n", __func__,
		(uint32_t)vtd_drhd_maxhandle, (uint32_t)vtd_dmar_table_physical_address);

}
