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

	return 1;

}

