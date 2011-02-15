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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

// vmx_eap.c
// VMX external access protection (DMA protection)
// author: amit vasudevan (amitvasudevan@acm.org)

#include <target.h>

//maximum number of RSDT entries we support
#define	ACPI_MAX_RSDT_ENTRIES		(256)

//==============================================================================
// local (static) variables and function definitions
//==============================================================================

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
    case  VTD_VER_REG_OFF:
    case  VTD_GCMD_REG_OFF:
    case  VTD_GSTS_REG_OFF:
    case  VTD_FSTS_REG_OFF:
    case  VTD_FECTL_REG_OFF:
    case  VTD_PMEN_REG_OFF:
      regtype=VTD_REG_32BITS;
      regaddr=dmardevice->regbaseaddr+reg;
      break;
    
    //64-bit registers
    case  VTD_CAP_REG_OFF:
    case  VTD_ECAP_REG_OFF:
    case  VTD_RTADDR_REG_OFF:
    case  VTD_CCMD_REG_OFF:
      regtype=VTD_REG_64BITS;
      regaddr=dmardevice->regbaseaddr+reg;
      break;
      
    case  VTD_IOTLB_REG_OFF:{
      VTD_ECAP_REG  t_vtd_ecap_reg;
      regtype=VTD_REG_64BITS;
      _vtd_reg(dmardevice, VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&t_vtd_ecap_reg.value);
      regaddr=dmardevice->regbaseaddr+(t_vtd_ecap_reg.bits.iro*16)+0x8;
      break;
    }
      
    case  VTD_IVA_REG_OFF:{
      VTD_ECAP_REG  t_vtd_ecap_reg;
      regtype=VTD_REG_64BITS;
      _vtd_reg(dmardevice, VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&t_vtd_ecap_reg.value);
      regaddr=dmardevice->regbaseaddr+(t_vtd_ecap_reg.bits.iro*16);
      break;
    }
    
    default:
      printf("\n%s: Halt, Unsupported register=%08x", __FUNCTION__, reg);
      HALT();
      break;
  }

  //perform the actual read or write request
	switch(regtype){
    case VTD_REG_32BITS:{	//32-bit r/w
      if(access == VTD_REG_READ)
        *((u32 *)value)= flat_readu32(regaddr);
      else
        flat_writeu32(regaddr, *((u32 *)value));
        
      break;
    }
    
    case VTD_REG_64BITS:{	//64-bit r/w
      if(access == VTD_REG_READ)
        *((u64 *)value)=flat_readu64(regaddr);
      else
        flat_writeu64(regaddr, *((u64 *)value));
    
      break;
    }
  
    default:
     printf("\n%s: Halt, Unsupported access width=%08x", __FUNCTION__, regtype);
     HALT();
  }

  return;
}



//initialize VMX EAP a.k.a VT-d
//returns 1 if all went well, else 0
u32 vmx_eap_initialize(void){
	ACPI_RSDP rsdp;
	ACPI_RSDT rsdt;
	u32 num_rsdtentries;
	u32 rsdtentries[ACPI_MAX_RSDT_ENTRIES];
	u32 status;
	VTD_DMAR dmar;
	u32 i, dmarfound;
	u32 dmaraddrphys, remappingstructuresaddrphys;
	
	
	//zero out rsdp and rsdt structures
	memset(&rsdp, 0, sizeof(ACPI_RSDP));
	memset(&rsdt, 0, sizeof(ACPI_RSDT));

  //get ACPI RSDP
  status=acpi_getRSDP(&rsdp);
  ASSERT(status != 0);	//we need a valid RSDP to proceed
  printf("\n%s: RSDP at %08x", __FUNCTION__, status);
  
	//grab ACPI RSDT
	flat_copy((u8 *)&rsdt, (u8 *)rsdp.rsdtaddress, sizeof(ACPI_RSDT));
	printf("\n%s: RSDT at %08x, len=%u bytes, hdrlen=%u bytes", 
		__FUNCTION__, rsdp.rsdtaddress, rsdt.length, sizeof(ACPI_RSDT));
	
	//get the RSDT entry list
	num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT))/ sizeof(u32);
	ASSERT(num_rsdtentries < ACPI_MAX_RSDT_ENTRIES);
	flat_copy((u8 *)&rsdtentries, (u8 *)(rsdp.rsdtaddress + sizeof(ACPI_RSDT)),
			sizeof(u32)*num_rsdtentries);			
  printf("\n%s: RSDT entry list at %08x, len=%u", __FUNCTION__,
		(rsdp.rsdtaddress + sizeof(ACPI_RSDT)), num_rsdtentries);


	//find the VT-d DMAR table in the list (if any)
  for(i=0; i< num_rsdtentries; i++){
  	flat_copy((u8 *)&dmar, (u8 *)rsdtentries[i], sizeof(VTD_DMAR));  
    if(dmar.signature == VTD_DMAR_SIGNATURE){
      dmarfound=1;
      break;
    }
  }     	
  
  //if no DMAR table, bail out
	if(!dmarfound)
    return 0;  

	dmaraddrphys = rsdtentries[i]; //DMAR table physical memory address;
  printf("\n%s: DMAR at %08x", __FUNCTION__, dmaraddrphys);
  
  i=0;
  remappingstructuresaddrphys=dmaraddrphys+sizeof(VTD_DMAR);
  printf("\n%s: remapping structures at %08x", __FUNCTION__, remappingstructuresaddrphys);
  
  while(i < (dmar.length-sizeof(VTD_DMAR))){
    u16 type, length;
		flat_copy((u8 *)&type, (u8 *)(remappingstructuresaddrphys+i), sizeof(u16));
		flat_copy((u8 *)&length, (u8 *)(remappingstructuresaddrphys+i+sizeof(u16)), sizeof(u16));     

    switch(type){
      case  0:  //DRHD
        printf("\nDRHD at %08x, len=%u bytes", (u32)(remappingstructuresaddrphys+i), length);
        ASSERT(vtd_num_drhd < VTD_MAX_DRHD);
				flat_copy((u8 *)&vtd_drhd[vtd_num_drhd], (u8 *)(remappingstructuresaddrphys+i), length);
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
  printf("\n%s: DMAR Devices:");
  for(i=0; i < vtd_num_drhd; i++){
    VTD_CAP_REG cap;    
    VTD_ECAP_REG ecap;
    printf("\n	Device %u on PCI seg %04x; base=0x%016LX", i, 
				vtd_drhd[i].pcisegment, vtd_drhd[i].regbaseaddr);
    _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);
    printf("\n		cap=0x%016LX", (u64)cap.value);
    _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&ecap.value);
    printf("\n		ecap=0x%016LX", (u64)ecap.value);
  }

	return 1;

}

