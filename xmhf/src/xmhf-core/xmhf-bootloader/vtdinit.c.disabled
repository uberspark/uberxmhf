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

/**
 * vtdinit.c
 * 
 * initialize vt-d PMRs for DMA protection of SL+runtime
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


#include <xmhf.h> 

//maximum number of RSDT entries we support
#define	ACPI_MAX_RSDT_ENTRIES		(256)

//DMA Remapping Hardware Unit Definitions
static VTD_DRHD vtd_drhd[VTD_MAX_DRHD];
static u32 vtd_num_drhd=0;	//total number of DMAR h/w units

//------------------------------------------------------------------------------
//vt-d register access function
static void _vtd_reg(VTD_DRHD *dmardevice, u32 access, u32 reg, void *value){
  u32 regtype=VTD_REG_32BITS, regaddr=0;  

	//obtain register type and base address
  switch(reg){
    //32-bit registers
    case  VTD_PMEN_REG_OFF:
    case  VTD_PLMBASE_REG_OFF:
    case  VTD_PLMLIMIT_REG_OFF:
      regtype=VTD_REG_32BITS;
      regaddr=dmardevice->regbaseaddr+reg;
      break;
    
    //64-bit registers
    case  VTD_CAP_REG_OFF:
    case  VTD_ECAP_REG_OFF:
    case VTD_PHMBASE_REG_OFF:
    case VTD_PHMLIMIT_REG_OFF:
      regtype=VTD_REG_64BITS;
      regaddr=dmardevice->regbaseaddr+reg;
      break;
  
    default:
      printf("\n%s: Halt, Unsupported register=%08x", __FUNCTION__, reg);
      HALT();
      break;
  }

  //perform the actual read or write request
	switch(regtype){
    case VTD_REG_32BITS:{	//32-bit r/w
      if(access == VTD_REG_READ)
        *((u32 *)value)= *((u32 *)regaddr);
      else
		*((u32 *)regaddr) = *((u32 *)value);
        
      break;
    }
    
    case VTD_REG_64BITS:{	//64-bit r/w
      if(access == VTD_REG_READ)
        *((u64 *)value)= *((u64 *)regaddr);
      else
        *((u64 *)regaddr) = *((u64 *)value);
    
      break;
    }
  
    default:
     printf("\n%s: Halt, Unsupported access width=%08x", __FUNCTION__, regtype);
     HALT();
  }

  return;
}


static bool vtdinit_drhd_initialize(VTD_DRHD *drhd, u32 membase_2Maligned __attribute__((unused)), u32 size_2Maligned __attribute__((unused))){	
	VTD_CAP_REG cap;
	VTD_PMEN_REG pmen;
	VTD_PLMBASE_REG plmbase;
	VTD_PLMLIMIT_REG plmlimit;
	VTD_PHMBASE_REG phmbase;
	VTD_PHMLIMIT_REG phmlimit;
  
	//sanity check
	HALT_ON_ERRORCOND(drhd != NULL);

	//verify required capabilities
	{
		printf("\nVerifying DRHD capabilities...");
	
		//read CAP register
		_vtd_reg(drhd, VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);
		
		if(! (cap.bits.plmr && cap.bits.phmr) ){
			printf("\nWarning:	PL/HMR unsupported. Halting!");
			HALT();
		}
		
		printf("\nDRHD unit has all required capabilities");
	}
	
	
	//disable PMEN
	 pmen.bits.epm=0;
	 _vtd_reg(drhd, VTD_REG_WRITE, VTD_PMEN_REG_OFF, (void *)&pmen.value);
    
    //load PLMBASE
    plmbase.value= __TARGET_BASE_SL;
     _vtd_reg(drhd, VTD_REG_WRITE, VTD_PLMBASE_REG_OFF, (void *)&plmbase.value);
    //load PLMLIMIT
    plmlimit.value=__TARGET_BASE_SL + __TARGET_SIZE_SL;
     _vtd_reg(drhd, VTD_REG_WRITE, VTD_PLMLIMIT_REG_OFF, (void *)&plmlimit.value);
    //load PHMBASE
    phmbase.value=(__TARGET_BASE_SL + __TARGET_SIZE_SL);
     _vtd_reg(drhd, VTD_REG_WRITE, VTD_PHMBASE_REG_OFF, (void *)&phmbase.value);
    //load PHMLIMIT
    phmlimit.value= (__TARGET_BASE_SL + __TARGET_SIZE_SL) + (size_2Maligned - __TARGET_SIZE_SL);
    _vtd_reg(drhd, VTD_REG_WRITE, VTD_PHMLIMIT_REG_OFF, (void *)&phmlimit.value);

	//enable PMEN
    pmen.bits.epm=1;
	_vtd_reg(drhd, VTD_REG_WRITE, VTD_PMEN_REG_OFF, (void *)&pmen.value);


	//debug dump
	 _vtd_reg(drhd, VTD_REG_READ, VTD_PLMBASE_REG_OFF, (void *)&plmbase.value);
     _vtd_reg(drhd, VTD_REG_READ, VTD_PLMLIMIT_REG_OFF, (void *)&plmlimit.value);
	 _vtd_reg(drhd, VTD_REG_READ, VTD_PHMBASE_REG_OFF, (void *)&phmbase.value);
     _vtd_reg(drhd, VTD_REG_READ, VTD_PHMLIMIT_REG_OFF, (void *)&phmlimit.value);
	_vtd_reg(drhd, VTD_REG_READ, VTD_PMEN_REG_OFF, (void *)&pmen.value);
	printf("\n%s: PMEN=%08x, PLMBASE=%08x, PLMLIMIT=%08x", __FUNCTION__, pmen.value, plmbase.value, plmlimit.value);
	printf("\n%s: PHMBASE=%016llx, PLMLIMIT=%016llx", __FUNCTION__, phmbase.value, phmlimit.value);


	return true;
}


//protect a given physical range of memory (membase to membase+size)
//using VT-d PMRs
//return true if everything went fine, else false
bool vtdinit_dmaprotect(u32 membase __attribute__((unused)), u32 size __attribute__ ((unused))){
	ACPI_RSDP rsdp;
	ACPI_RSDT rsdt;
	u32 num_rsdtentries;
	u32 rsdtentries[ACPI_MAX_RSDT_ENTRIES];
	u32 status;
	VTD_DMAR dmar;
	u32 i, dmarfound;
	u32 dmaraddrphys, remappingstructuresaddrphys;
	
	printf("\n%s: size=%08x", __FUNCTION__, size);
	
	//zero out rsdp and rsdt structures
	memset(&rsdp, 0, sizeof(ACPI_RSDP));
	memset(&rsdt, 0, sizeof(ACPI_RSDT));

	//get ACPI RSDP
	status=xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp);
	HALT_ON_ERRORCOND(status != 0);	//we need a valid RSDP to proceed
	printf("\n%s: RSDP at %08x", __FUNCTION__, status);
  
	//grab ACPI RSDT
	//xmhf_baseplatform_arch_flat_copy((u8 *)&rsdt, (u8 *)rsdp.rsdtaddress, sizeof(ACPI_RSDT));
	memcpy((u8 *)&rsdt, (u8 *)rsdp.rsdtaddress, sizeof(ACPI_RSDT));
	printf("\n%s: RSDT at %08x, len=%u bytes, hdrlen=%u bytes", 
		__FUNCTION__, rsdp.rsdtaddress, rsdt.length, sizeof(ACPI_RSDT));
	
	//get the RSDT entry list
	num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT))/ sizeof(u32);
	HALT_ON_ERRORCOND(num_rsdtentries < ACPI_MAX_RSDT_ENTRIES);
	memcpy((u8 *)&rsdtentries, (u8 *)(rsdp.rsdtaddress + sizeof(ACPI_RSDT)),
			sizeof(u32)*num_rsdtentries);			
	printf("\n%s: RSDT entry list at %08x, len=%u", __FUNCTION__,
		(rsdp.rsdtaddress + sizeof(ACPI_RSDT)), num_rsdtentries);

	//find the VT-d DMAR table in the list (if any)
	for(i=0; i< num_rsdtentries; i++){
		memcpy((u8 *)&dmar, (u8 *)rsdtentries[i], sizeof(VTD_DMAR));  
		if(dmar.signature == VTD_DMAR_SIGNATURE){
		  dmarfound=1;
		  break;
		}
	}     	
  
	//if no DMAR table, bail out
	if(!dmarfound)
		return false;  

	dmaraddrphys = rsdtentries[i]; //DMAR table physical memory address;
	printf("\n%s: DMAR at %08x", __FUNCTION__, dmaraddrphys);

	//detect DRHDs in the DMAR table
	i=0;
	remappingstructuresaddrphys=dmaraddrphys+sizeof(VTD_DMAR);
	printf("\n%s: remapping structures at %08x", __FUNCTION__, remappingstructuresaddrphys);
  
	while(i < (dmar.length-sizeof(VTD_DMAR))){
		u16 type, length;
		memcpy((u8 *)&type, (u8 *)(remappingstructuresaddrphys+i), sizeof(u16));
		memcpy((u8 *)&length, (u8 *)(remappingstructuresaddrphys+i+sizeof(u16)), sizeof(u16));     

		switch(type){
			case  0:  //DRHD
				printf("\nDRHD at %08x, len=%u bytes", (u32)(remappingstructuresaddrphys+i), length);
				HALT_ON_ERRORCOND(vtd_num_drhd < VTD_MAX_DRHD);
				memcpy((u8 *)&vtd_drhd[vtd_num_drhd], (u8 *)(remappingstructuresaddrphys+i), length);
				vtd_num_drhd++;
				i+=(u32)length;
				break;

			default:	//unknown type, we skip this
				i += (u32)length;
				break;
		}
	}
    printf("\n%s: total DRHDs detected= %u units", __FUNCTION__, vtd_num_drhd);

	//be a little verbose about what we found
	printf("\n%s: DMAR Devices:", __FUNCTION__);
	for(i=0; i < vtd_num_drhd; i++){
		VTD_CAP_REG cap;    
		VTD_ECAP_REG ecap;
		printf("\n	Device %u on PCI seg %04x; base=0x%016llx", i, 
					vtd_drhd[i].pcisegment, vtd_drhd[i].regbaseaddr);
		_vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);
		printf("\n		cap=0x%016llx", (u64)cap.value);
		_vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&ecap.value);
		printf("\n		ecap=0x%016llx", (u64)ecap.value);
	}

	//initialize all DRHD units
	for(i=0; i < vtd_num_drhd; i++){
		printf("\n%s: initializing DRHD unit %u...", __FUNCTION__, i);
		if(!vtdinit_drhd_initialize(&vtd_drhd[i], PAGE_ALIGN_2M(membase), PAGE_ALIGN_UP2M(size)) )
			return false;
	}

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup 
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	//xmhf_baseplatform_arch_flat_writeu32(dmaraddrphys, 0UL);

	//success
	printf("\n%s: success, leaving...", __FUNCTION__);

	return true;
}

