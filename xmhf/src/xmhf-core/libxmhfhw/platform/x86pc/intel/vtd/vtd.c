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

// EMHF DMA protection component implementation for x86 VMX
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h> 

//maximum number of RSDT entries we support
#define	ACPI_MAX_RSDT_ENTRIES		(256)

//==============================================================================
// local (static) variables and function definitions
//==============================================================================

//DMA Remapping Hardware Unit Definitions
static VTD_DRHD vtd_drhd[VTD_MAX_DRHD];
static u32 vtd_num_drhd=0;	//total number of DMAR h/w units
static u32 vtd_dmar_table_physical_address; //DMAR table physical memory address
static u8 vtd_ret_table[PAGE_SIZE_4K]; //4KB Vt-d Root-Entry table

/*//VT-d 3-level DMA protection page table data structure addresses
static u32 l_vtd_pdpt_paddr=0;
static u32 l_vtd_pdpt_vaddr=0;
static u32 l_vtd_pdts_paddr=0;
static u32 l_vtd_pdts_vaddr=0;
static u32 l_vtd_pts_paddr=0;
static u32 l_vtd_pts_vaddr=0;



//------------------------------------------------------------------------------
//setup VT-d DMA protection page tables
static void _vtd_setuppagetables(u32 vtd_pdpt_paddr, u32 vtd_pdpt_vaddr,
	u32 vtd_pdts_paddr, u32 vtd_pdts_vaddr,
	u32 vtd_pts_paddr, u32 vtd_pts_vaddr){
  
	u32 pdptphysaddr, pdtphysaddr, ptphysaddr;
  u32 i,j,k;
  pdpt_t pdpt;
  pdt_t pdt;
  pt_t pt;
  u32 physaddr=0;
  
  pdptphysaddr=vtd_pdpt_paddr;
  pdtphysaddr=vtd_pdts_paddr;
  ptphysaddr=vtd_pts_paddr;
  
  //ensure PDPT, PDTs and PTs are all page-aligned
  HALT_ON_ERRORCOND( !(pdptphysaddr & 0x00000FFFUL) && !(pdtphysaddr & 0x00000FFFUL) && !((ptphysaddr & 0x00000FFFUL)) );

	//initialize our local variables 
	l_vtd_pdpt_paddr = vtd_pdpt_paddr;
	l_vtd_pdpt_vaddr = vtd_pdpt_vaddr;
	l_vtd_pdts_paddr = vtd_pdts_paddr;
	l_vtd_pdts_vaddr = vtd_pdts_vaddr;
	l_vtd_pts_paddr = vtd_pts_paddr;
	l_vtd_pts_vaddr = vtd_pts_vaddr;
	
  
  //setup pdpt, pdt and pt
  //initially set the entire 4GB as DMA read/write capable
  pdpt=(pdpt_t)vtd_pdpt_vaddr;
  for(i=0; i< PAE_PTRS_PER_PDPT; i++){
    pdpt[i]=(u64)(pdtphysaddr + (i * PAGE_SIZE_4K));  
    pdpt[i] |= ((u64)VTD_READ | (u64)VTD_WRITE);
    
    pdt=(pdt_t)(vtd_pdts_vaddr + (i * PAGE_SIZE_4K));
    for(j=0; j < PAE_PTRS_PER_PDT; j++){
      pdt[j]=(u64)(ptphysaddr + (i * PAGE_SIZE_4K * 512)+ (j * PAGE_SIZE_4K));
      pdt[j] |= ((u64)VTD_READ | (u64)VTD_WRITE);
    
      pt=(pt_t)(vtd_pts_vaddr + (i * PAGE_SIZE_4K * 512)+ (j * PAGE_SIZE_4K));
      for(k=0; k < PAE_PTRS_PER_PT; k++){
        pt[k]=(u64)physaddr;
        pt[k] |= ((u64)VTD_READ | (u64)VTD_WRITE);
        physaddr+=PAGE_SIZE_4K;
      }
    }
  }
}




//------------------------------------------------------------------------------
//set VT-d RET and CET tables
//we have 1 root entry table (RET) of 4kb, each root entry (RE) is 128-bits
//which gives us 256 entries in the RET, each corresponding to a PCI bus num.
//(0-255)
//each RE points to a context entry table (CET) of 4kb, each context entry (CE)
//is 128-bits which gives us 256 entries in the CET, accounting for 32 devices
//with 8 functions each as per the PCI spec.
//each CE points to a PDPT type paging structure. 
//in our implementation, every CE will point to a single PDPT type paging
//structure for the whole system
static void _vtd_setupRETCET(u32 vtd_pdpt_paddr, u32 vtd_ret_paddr, u32 vtd_ret_vaddr,	u32 vtd_cet_paddr, u32 vtd_cet_vaddr){
  u32 retphysaddr, cetphysaddr;
  u32 i, j;
  u64 *value;
  
  retphysaddr=vtd_ret_paddr;
  (void)retphysaddr;
  cetphysaddr=vtd_cet_paddr;

	//sanity check that pdpt base address is page-aligned
	HALT_ON_ERRORCOND( !(vtd_pdpt_paddr & 0x00000FFFUL) );
	
  //initialize RET  
  for(i=0; i < PCI_BUS_MAX; i++){
    value=(u64 *)(vtd_ret_vaddr + (i * 16));
    *(value+1)=(u64)0x0ULL;
    *value=(u64) (cetphysaddr +(i * PAGE_SIZE_4K));
    
    //sanity check that CET is page aligned
    HALT_ON_ERRORCOND( !(*value & 0x0000000000000FFFULL) );

		//set it to present
    *value |= 0x1ULL;
  }    

  //initialize CET
  for(i=0; i < PCI_BUS_MAX; i++){
    for(j=0; j < PCI_BUS_MAX; j++){
      value= (u64 *)(vtd_cet_vaddr + (i * PAGE_SIZE_4K) + (j * 16));
      *(value+1)=(u64)0x0000000000000101ULL; //domain:1, aw=39 bits, 3 level pt
      *value=vtd_pdpt_paddr;
      *value |= 0x1ULL; //present, enable fault recording/processing, multilevel pt translation           
    }
  }

}



//------------------------------------------------------------------------------
//set VT-d RET and CET tables for VT-d bootstrapping
//we have 1 root entry table (RET) of 4kb, each root entry (RE) is 128-bits
//which gives us 256 entries in the RET, each corresponding to a PCI bus num.
//(0-255)
//each RE points to a context entry table (CET) of 4kb, each context entry (CE)
//is 128-bits which gives us 256 entries in the CET, accounting for 32 devices
//with 8 functions each as per the PCI spec.
//each CE points to a PDPT type paging structure. 
//we ensure that every entry in the RET is 0 which means that the DRHD will
//not allow any DMA requests for PCI bus 0-255 (Sec 3.3.2, IVTD Spec. v1.2)
//we zero out the CET just for sanity 
static void _vtd_setupRETCET_bootstrap(u32 vtd_ret_paddr, u32 vtd_ret_vaddr, u32 vtd_cet_paddr, u32 vtd_cet_vaddr){
  
	//sanity check that RET and CET are page-aligned
	HALT_ON_ERRORCOND( !(vtd_ret_paddr & 0x00000FFFUL) && !(vtd_cet_paddr & 0x00000FFFUL) );
	
	//zero out CET, we dont require it for bootstrapping
	memset((void *)vtd_cet_vaddr, 0, PAGE_SIZE_4K);
	
	//zero out RET, effectively preventing DMA reads and writes in the system
	memset((void *)vtd_ret_vaddr, 0, PAGE_SIZE_4K);
}
*/

//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//initialize a DRHD unit
//note that the VT-d documentation does not describe the precise sequence of
//steps that need to be followed to initialize a DRHD unit!. we use our
//common sense instead...:p
//static void _vtd_drhd_initialize(VTD_DRHD *drhd, u32 vtd_ret_paddr){
/*static bool _vtd_drhd_initialize(VTD_DRHD *drhd, u32 membase_2Maligned, u32 size_2Maligned){	
	VTD_GCMD_REG gcmd;
  VTD_GSTS_REG gsts;
  VTD_FECTL_REG fectl;
  VTD_CAP_REG cap;
  VTD_RTADDR_REG rtaddr;
  VTD_CCMD_REG ccmd;
  VTD_IOTLB_REG iotlb;
  VTD_PMEN_REG pmen;
  VTD_PLMBASE_REG plmbase;
  VTD_PLMLIMIT_REG plmlimit;
  
	//sanity check
	HALT_ON_ERRORCOND(drhd != NULL);

	//verify required capabilities
	{
		printf("\nVerifying DRHD capabilities...");
	
		//read CAP register
		_vtd_reg(drhd, VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);
		
		if(!cap.bits.plmr){
			printf("\nWarning:	PLMR unsupported. Halting!");
			return false;
		}
		
		printf("\nDRHD unit has all required capabilities");
	}
	
	//read protected memory enable register (PMEN) to sanity check
	//that PMEN is enabled (due to SENTER)
	{
		printf("\nSanity checking PMEN is enabled...");

		//read PMEN register
		_vtd_reg(drhd, VTD_REG_READ, VTD_PMEN_REG_OFF, (void *)&pmen.value);
		
		if(!pmen.bits.prs){
			printf("\n  Fatal: PMEN is disabled. Halting!");
			return false;
		}
		
		printf("\nPMEN sanity check passed");
	}
	
	//sanity check protected low memory base register (PLMBASE)
	{
		printf("\nSanity checking PLMBASE...");

		//read PLMBASE register
		_vtd_reg(drhd, VTD_REG_READ, VTD_PLMBASE_REG_OFF, (void *)&plmbase.value);
		
		if(plmbase.value != membase_2Maligned){
			printf("\n Fatal: PLMBASE (%08x) does not contain expected value (%08x)", plmbase.value, membase_2Maligned);
			return false;
		}

		printf("\nPLMBASE sanity check passed");
	}
	
	//sanity check protected low memory limit register (PLMLIMIT)
	
	{
		printf("\nSanity checking PLMLIMIT...");

		//read PLMLIMIT register
		_vtd_reg(drhd, VTD_REG_READ, VTD_PLMLIMIT_REG_OFF, (void *)&plmlimit.value);
		
		if(plmlimit.value != (membase_2Maligned+__TARGET_SIZE_SL)){
			printf("\n Fatal: PLMLIMIT (%08x) does not contain expected value (%08x)", plmlimit.value, (membase_2Maligned+size_2Maligned));
			return false;
		}

		printf("\nPLMLIMIT sanity check passed");
	}
	
	
	return true;
	//HALT();
	
	
	//1. verify required capabilities
	//more specifically...
	//	verify supported MGAW to ensure our host address width is supported (32-bits)
  //	verify supported AGAW, must support 39-bits for 3 level page-table walk
  //	verify max domain id support (we use domain 1)
  printf("\n	Verifying required capabilities...");
  {
  	//read CAP register
		_vtd_reg(drhd, VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);
    
    //if MGAW is less than 32-bits bail out
		if(cap.bits.mgaw < 31){
      printf("\n	GAW < 31 (%u) unsupported. Halting!", cap.bits.mgaw);
      HALT();
    }
    
    //we use 3 level page-tables, so AGAW must support 39-bits
		if(!(cap.bits.sagaw & 0x2)){
      printf("\n	AGAW does not support 3-level page-table. Halting!");
      HALT();
    }

		//sanity check number of domains (if unsupported we bail out)
    HALT_ON_ERRORCOND(cap.bits.nd != 0x7);
    
  }
	printf("Done.");


	//check VT-d snoop control capabilities
	{
		VTD_ECAP_REG ecap;
		//read ECAP register
		_vtd_reg(drhd, VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&ecap.value);
		
		if(ecap.bits.sc)
			printf("\n	VT-d hardware Snoop Control (SC) capabilities present");
		else
			printf("\n	VT-d hardware Snoop Control (SC) unavailable");

		if(ecap.bits.c)
			printf("\n	VT-d hardware access to remapping structures COHERENT");
		else
			printf("\n	VT-d hardware access to remapping structures NON-COHERENT");
	}
	
  //3. setup fault logging
  printf("\n	Setting Fault-reporting to NON-INTERRUPT mode...");
  {
   	//read FECTL
	  fectl.value=0;
    _vtd_reg(drhd, VTD_REG_READ, VTD_FECTL_REG_OFF, (void *)&fectl.value);
    
		//set interrupt mask bit and write
		fectl.bits.im=1;
    _vtd_reg(drhd, VTD_REG_WRITE, VTD_FECTL_REG_OFF, (void *)&fectl.value);
    
		//check to see if the im bit actually stuck
		_vtd_reg(drhd, VTD_REG_READ, VTD_FECTL_REG_OFF, (void *)&fectl.value);
    
    if(!fectl.bits.im){
      printf("\n	Failed to set fault-reporting. Halting!");
      HALT();
    }
  }
  printf("Done.");

	//4. setup RET (root-entry)
  printf("\n	Setting up RET...");
  {
    //setup RTADDR with base of RET 
		rtaddr.value=(u64)vtd_ret_paddr;
    _vtd_reg(drhd, VTD_REG_WRITE, VTD_RTADDR_REG_OFF, (void *)&rtaddr.value);
    
    //read RTADDR and verify the base address
		rtaddr.value=0;
    _vtd_reg(drhd, VTD_REG_READ, VTD_RTADDR_REG_OFF, (void *)&rtaddr.value);
    if(rtaddr.value != (u64)vtd_ret_paddr){
      printf("\n	Failed to set RTADDR. Halting!");
      HALT();
    }
    
    //latch RET address by using GCMD.SRTP
    gcmd.value=0;
    gcmd.bits.srtp=1;
    _vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);
    
    //ensure the RET address was latched by the h/w
		_vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
    
    if(!gsts.bits.rtps){
      printf("\n	Failed to latch RTADDR. Halting!");
      HALT();
    }
  }
  printf("Done.");


  //5. invalidate CET cache
  printf("\n	Invalidating CET cache...");
	{
		//wait for context cache invalidation request to send
	#ifndef __XMHF_VERIFICATION__
    do{
      _vtd_reg(drhd, VTD_REG_READ, VTD_CCMD_REG_OFF, (void *)&ccmd.value);
    }while(ccmd.bits.icc);    
    #endif

		//initialize CCMD to perform a global invalidation       
    ccmd.value=0;
    ccmd.bits.cirg=1; //global invalidation
    ccmd.bits.icc=1;  //invalidate context cache
    
    //perform the invalidation
    _vtd_reg(drhd, VTD_REG_WRITE, VTD_CCMD_REG_OFF, (void *)&ccmd.value);

		//wait for context cache invalidation completion status
    #ifndef __XMHF_VERIFICATION__
    do{
      _vtd_reg(drhd, VTD_REG_READ, VTD_CCMD_REG_OFF, (void *)&ccmd.value);
    }while(ccmd.bits.icc);    
	#endif

		//if all went well CCMD CAIG = CCMD CIRG (i.e., actual = requested invalidation granularity)
    if(ccmd.bits.caig != 0x1){
      printf("\n	Invalidatation of CET failed. Halting! (%u)", ccmd.bits.caig);
      HALT();
    }
  }
  printf("Done.");


	//6. invalidate IOTLB
  printf("\n	Invalidating IOTLB...");
  {
    //initialize IOTLB to perform a global invalidation
		iotlb.value=0;
    iotlb.bits.iirg=1; //global invalidation
    iotlb.bits.ivt=1;	 //invalidate
    
    //perform the invalidation
		_vtd_reg(drhd, VTD_REG_WRITE, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);
    
	#ifndef __XMHF_VERIFICATION__
    //wait for the invalidation to complete
    do{
      _vtd_reg(drhd, VTD_REG_READ, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);
    }while(iotlb.bits.ivt);    
    #endif
    
    //if all went well IOTLB IAIG = IOTLB IIRG (i.e., actual = requested invalidation granularity)
		if(iotlb.bits.iaig != 0x1){
      printf("\n	Invalidation of IOTLB failed. Halting! (%u)", iotlb.bits.iaig);
      HALT();
    }
  }
	printf("Done.");


	//7. disable options we dont support
  printf("\n	Disabling unsupported options...");
  {
    //disable advanced fault logging (AFL)
		gcmd.value=0;
    gcmd.bits.eafl=0;
    _vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);
    _vtd_reg(drhd, VTD_REG_WRITE, VTD_GSTS_REG_OFF, (void *)&gsts.value);
    if(gsts.bits.afls){
      printf("\n	Could not disable AFL. Halting!");
      HALT();
    }

    //disabled queued invalidation (QI)
    gcmd.value=0;
    gcmd.bits.qie=0;
    _vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);
    _vtd_reg(drhd, VTD_REG_WRITE, VTD_GSTS_REG_OFF, (void *)&gsts.value);
    if(gsts.bits.qies){
      printf("\n	Could not disable QI. Halting!");
      HALT();
    }
    
    //disable interrupt remapping (IR)
    gcmd.value=0;
    gcmd.bits.ire=0;
    _vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);
    _vtd_reg(drhd, VTD_REG_WRITE, VTD_GSTS_REG_OFF, (void *)&gsts.value);
    if(gsts.bits.ires){
      printf("\n	Could not disable IR. Halting!");
      HALT();
    }
	}
	printf("Done.");

	
  //8. enable device
  printf("\n	Enabling device...");
  {
      //enable translation
			gcmd.value=0;
      gcmd.bits.te=1;
	   #ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
	   assert(gcmd.bits.te == 1);
	   #endif
	   
      _vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);
      
			//wait for translation enabled status to go green...
			_vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
	#ifndef __XMHF_VERIFICATION__
      while(!gsts.bits.tes){
        _vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
      }
     #endif
  }
  printf("Done.");

  
  //9. disable protected memory regions (PMR) if available
  printf("\n	Checking and disabling PMR...");
	{
    VTD_PMEN_REG pmen;
    _vtd_reg(drhd, VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);
    
    //PMR caps present, so disable it as we dont support that
		if(cap.bits.plmr || cap.bits.phmr){
      _vtd_reg(drhd, VTD_REG_READ, VTD_PMEN_REG_OFF, (void *)&pmen.value);
      pmen.bits.epm=0;	//disable PMR
      _vtd_reg(drhd, VTD_REG_WRITE, VTD_PMEN_REG_OFF, (void *)&pmen.value);
      #ifndef __XMHF_VERIFICATION__
      //wait for PMR disabled...
			do{
        _vtd_reg(drhd, VTD_REG_READ, VTD_PMEN_REG_OFF, (void *)&pmen.value);
      }while(pmen.bits.prs);
      #endif
  	}
	}
	printf("Done.");


}*/


//------------------------------------------------------------------------------
/*

//==============================================================================
//global (exported) functions

#define PAE_get_pdptindex(x) ((x) >> 30)
#define PAE_get_pdtindex(x) (((x) << 2) >> 23)
#define PAE_get_ptindex(x) ( ((x) << 11) >> 23 )
#define PAE_get_pdtaddress(x) ( (u32) ( (u64)(x) & (u64)0x3FFFFFFFFFFFF000ULL ))
#define PAE_get_ptaddress(x) ( (u32) ( (u64)(x) & (u64)0x3FFFFFFFFFFFF000ULL ))

*/
#if !defined (__DMAP__)
void vmx_eap_zap(void){
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
	status=xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp);
	HALT_ON_ERRORCOND(status != 0);	//we need a valid RSDP to proceed
	printf("\n%s: RSDP at %08x", __FUNCTION__, status);

	//grab ACPI RSDT
	xmhf_baseplatform_arch_flat_copy((u8 *)&rsdt, (u8 *)rsdp.rsdtaddress, sizeof(ACPI_RSDT));
	printf("\n%s: RSDT at %08x, len=%u bytes, hdrlen=%u bytes", 
		__FUNCTION__, rsdp.rsdtaddress, rsdt.length, sizeof(ACPI_RSDT));

	//get the RSDT entry list
	num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT))/ sizeof(u32);
	HALT_ON_ERRORCOND(num_rsdtentries < ACPI_MAX_RSDT_ENTRIES);
	xmhf_baseplatform_arch_flat_copy((u8 *)&rsdtentries, (u8 *)(rsdp.rsdtaddress + sizeof(ACPI_RSDT)),
			sizeof(u32)*num_rsdtentries);			
	printf("\n%s: RSDT entry list at %08x, len=%u", __FUNCTION__,
		(rsdp.rsdtaddress + sizeof(ACPI_RSDT)), num_rsdtentries);


	//find the VT-d DMAR table in the list (if any)
	for(i=0; i< num_rsdtentries; i++){
		xmhf_baseplatform_arch_flat_copy((u8 *)&dmar, (u8 *)rsdtentries[i], sizeof(VTD_DMAR));  
		if(dmar.signature == VTD_DMAR_SIGNATURE){
		  dmarfound=1;
		  break;
		}
	}     	

	//if no DMAR table, bail out
	if(!dmarfound)
		return;  

	dmaraddrphys = rsdtentries[i]; //DMAR table physical memory address;
	printf("\n%s: DMAR at %08x", __FUNCTION__, dmaraddrphys);

	i=0;
	remappingstructuresaddrphys=dmaraddrphys+sizeof(VTD_DMAR);
	printf("\n%s: remapping structures at %08x", __FUNCTION__, remappingstructuresaddrphys);

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup 
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	xmhf_baseplatform_arch_flat_writeu32(dmaraddrphys, 0UL);


	//success
	printf("\n%s: success, leaving...", __FUNCTION__);
}
#endif	//__DMAP__

/*
//initialize VMX EAP a.k.a VT-d
//returns 1 if all went well, else 0
//if input parameter bootstrap is 1 then we perform minimal translation
//structure initialization, else we do the full DMA translation structure
//initialization at a page-granularity
u32 vmx_eap_initialize(u32 vtd_pdpt_paddr, u32 vtd_pdpt_vaddr,
		u32 vtd_pdts_paddr, u32 vtd_pdts_vaddr,
		u32 vtd_pts_paddr, u32 vtd_pts_vaddr,
		u32 vtd_ret_paddr, u32 vtd_ret_vaddr,
		u32 vtd_cet_paddr, u32 vtd_cet_vaddr, u32 isbootstrap){

	ACPI_RSDP rsdp;
	ACPI_RSDT rsdt;
	u32 num_rsdtentries;
	u32 rsdtentries[ACPI_MAX_RSDT_ENTRIES];
	u32 status;
	VTD_DMAR dmar;
	u32 i, dmarfound;
	u32 dmaraddrphys, remappingstructuresaddrphys;
	
#ifndef __XMHF_VERIFICATION__	
	//zero out rsdp and rsdt structures
	memset(&rsdp, 0, sizeof(ACPI_RSDP));
	memset(&rsdt, 0, sizeof(ACPI_RSDT));

  //get ACPI RSDP
  status=xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp);
  HALT_ON_ERRORCOND(status != 0);	//we need a valid RSDP to proceed
  printf("\n%s: RSDP at %08x", __FUNCTION__, status);
  
	//grab ACPI RSDT
	xmhf_baseplatform_arch_flat_copy((u8 *)&rsdt, (u8 *)rsdp.rsdtaddress, sizeof(ACPI_RSDT));
	printf("\n%s: RSDT at %08x, len=%u bytes, hdrlen=%u bytes", 
		__FUNCTION__, rsdp.rsdtaddress, rsdt.length, sizeof(ACPI_RSDT));
	
	//get the RSDT entry list
	num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT))/ sizeof(u32);
	HALT_ON_ERRORCOND(num_rsdtentries < ACPI_MAX_RSDT_ENTRIES);
	xmhf_baseplatform_arch_flat_copy((u8 *)&rsdtentries, (u8 *)(rsdp.rsdtaddress + sizeof(ACPI_RSDT)),
			sizeof(u32)*num_rsdtentries);			
  printf("\n%s: RSDT entry list at %08x, len=%u", __FUNCTION__,
		(rsdp.rsdtaddress + sizeof(ACPI_RSDT)), num_rsdtentries);


	//find the VT-d DMAR table in the list (if any)
  for(i=0; i< num_rsdtentries; i++){
  	xmhf_baseplatform_arch_flat_copy((u8 *)&dmar, (u8 *)rsdtentries[i], sizeof(VTD_DMAR));  
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
		xmhf_baseplatform_arch_flat_copy((u8 *)&type, (u8 *)(remappingstructuresaddrphys+i), sizeof(u16));
		xmhf_baseplatform_arch_flat_copy((u8 *)&length, (u8 *)(remappingstructuresaddrphys+i+sizeof(u16)), sizeof(u16));     

    switch(type){
      case  0:  //DRHD
        printf("\nDRHD at %08x, len=%u bytes", (u32)(remappingstructuresaddrphys+i), length);
        HALT_ON_ERRORCOND(vtd_num_drhd < VTD_MAX_DRHD);
				xmhf_baseplatform_arch_flat_copy((u8 *)&vtd_drhd[vtd_num_drhd], (u8 *)(remappingstructuresaddrphys+i), length);
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


  //initialize VT-d page tables (not done if we are bootstrapping)
	if(!isbootstrap){
		_vtd_setuppagetables(vtd_pdpt_paddr, vtd_pdpt_vaddr, vtd_pdts_paddr, vtd_pdts_vaddr, vtd_pts_paddr, vtd_pts_vaddr);
		printf("\n%s: setup VT-d page tables (pdpt=%08x, pdts=%08x, pts=%08x).", __FUNCTION__, vtd_pdpt_paddr, vtd_pdts_paddr, vtd_pts_paddr);
	}	
		
	//initialize VT-d RET and CET
	if(!isbootstrap){
		_vtd_setupRETCET(vtd_pdpt_paddr, vtd_ret_paddr, vtd_ret_vaddr, vtd_cet_paddr, vtd_cet_vaddr);
		printf("\n%s: setup VT-d RET (%08x) and CET (%08x).", __FUNCTION__, vtd_ret_paddr, vtd_cet_paddr);
	}else{
		//bootstrapping
		_vtd_setupRETCET_bootstrap(vtd_ret_paddr, vtd_ret_vaddr, vtd_cet_paddr, vtd_cet_vaddr);
		printf("\n%s: setup VT-d RET (%08x) and CET (%08x) for bootstrap.", __FUNCTION__, vtd_ret_paddr, vtd_cet_paddr);
	}

#endif //__XMHF_VERIFICATION__


#ifndef __XMHF_VERIFICATION__
 	//initialize all DRHD units
  for(i=0; i < vtd_num_drhd; i++){
  	printf("\n%s: initializing DRHD unit %u...", __FUNCTION__, i);
  	//_vtd_drhd_initialize(&vtd_drhd[i], vtd_ret_paddr);
  }
#else
  	printf("\n%s: initializing DRHD unit %u...", __FUNCTION__, i);
  	//_vtd_drhd_initialize(&vtd_drhd[0], vtd_ret_paddr);
#endif

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup 
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	if(!isbootstrap)
		xmhf_baseplatform_arch_flat_writeu32(dmaraddrphys, 0UL);


	//success
	printf("\n%s: success, leaving...", __FUNCTION__);

	return 1;
}

////////////////////////////////////////////////////////////////////////
// GLOBALS


//"normal" DMA protection initialization to setup required
//structures for DMA protection
//return 1 on success 0 on failure
u32 xmhf_dmaprot_arch_x86vmx_initialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size){
	//Vt-d bootstrap has minimal DMA translation setup and protects entire
	//system memory. Relax this by instantiating a complete DMA translation
	//structure at a page granularity and protecting only the SL and Runtime
	u32 vmx_eap_vtd_pdpt_paddr, vmx_eap_vtd_pdpt_vaddr;
	u32 vmx_eap_vtd_pdts_paddr, vmx_eap_vtd_pdts_vaddr;
	u32 vmx_eap_vtd_pts_paddr, vmx_eap_vtd_pts_vaddr;
	u32 vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr;
	u32 vmx_eap_vtd_cet_paddr, vmx_eap_vtd_cet_vaddr;

	HALT_ON_ERRORCOND(protectedbuffer_size >= (PAGE_SIZE_4K + (PAGE_SIZE_4K * PAE_PTRS_PER_PDPT) 
					+ (PAGE_SIZE_4K * PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT) + PAGE_SIZE_4K +
					(PAGE_SIZE_4K * PCI_BUS_MAX)) );
	
	vmx_eap_vtd_pdpt_paddr = protectedbuffer_paddr; 
	vmx_eap_vtd_pdpt_vaddr = protectedbuffer_vaddr; 
	vmx_eap_vtd_pdts_paddr = vmx_eap_vtd_pdpt_paddr + PAGE_SIZE_4K; 
	vmx_eap_vtd_pdts_vaddr = vmx_eap_vtd_pdpt_vaddr + PAGE_SIZE_4K;
	vmx_eap_vtd_pts_paddr = vmx_eap_vtd_pdts_paddr + (PAGE_SIZE_4K * PAE_PTRS_PER_PDPT); 
	vmx_eap_vtd_pts_vaddr = vmx_eap_vtd_pdts_vaddr + (PAGE_SIZE_4K * PAE_PTRS_PER_PDPT); 
	vmx_eap_vtd_ret_paddr = vmx_eap_vtd_pts_paddr +	(PAGE_SIZE_4K * PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT); 
	vmx_eap_vtd_ret_vaddr = vmx_eap_vtd_pts_vaddr + (PAGE_SIZE_4K * PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT);  
	vmx_eap_vtd_cet_paddr = vmx_eap_vtd_ret_paddr + PAGE_SIZE_4K; 
	vmx_eap_vtd_cet_vaddr = vmx_eap_vtd_ret_vaddr + PAGE_SIZE_4K; 
			
	return vmx_eap_initialize(vmx_eap_vtd_pdpt_paddr, vmx_eap_vtd_pdpt_vaddr, vmx_eap_vtd_pdts_paddr, vmx_eap_vtd_pdts_vaddr, vmx_eap_vtd_pts_paddr, vmx_eap_vtd_pts_vaddr, vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr, vmx_eap_vtd_cet_paddr, vmx_eap_vtd_cet_vaddr, 0);
}

//DMA protect a given region of memory, start_paddr is
//assumed to be page aligned physical memory address
void xmhf_dmaprot_arch_x86vmx_protect(u32 start_paddr, u32 size){
  pt_t pt;
  u32 vaddr, end_paddr;
  u32 pdptindex, pdtindex, ptindex;
  
  //compute page aligned end
  end_paddr = PAGE_ALIGN_4K(start_paddr + size);
  
  //sanity check
  HALT_ON_ERRORCOND( (l_vtd_pdpt_paddr != 0) && (l_vtd_pdpt_vaddr != 0) );
  HALT_ON_ERRORCOND( (l_vtd_pdts_paddr != 0) && (l_vtd_pdts_vaddr != 0) );
  HALT_ON_ERRORCOND( (l_vtd_pts_paddr != 0) && (l_vtd_pts_vaddr != 0) );
  
  #ifndef __XMHF_VERIFICATION__
  for(vaddr=start_paddr; vaddr <= end_paddr; vaddr+=PAGE_SIZE_4K){
  
		//compute pdpt, pdt and pt indices
  	pdptindex= PAE_get_pdptindex(vaddr);
	  pdtindex= PAE_get_pdtindex(vaddr);
	  ptindex=PAE_get_ptindex(vaddr);
    
    //get the page-table for this physical page
	  pt=(pt_t) (l_vtd_pts_vaddr + (pdptindex * PAGE_SIZE_4K * 512)+ (pdtindex * PAGE_SIZE_4K));
	  
	  //protect the physical page
    //pt[ptindex] &= 0xFFFFFFFFFFFFFFFCULL;  
  	pt[ptindex] &= ~((u64)VTD_READ | (u64)VTD_WRITE);
  
  }
  #endif
  
  //flush the caches
_vtd_invalidatecaches();  

}

*/

////////////////////////////////////////////////////////////////////////
// local helper functions

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
    case  VTD_PLMBASE_REG_OFF:
    case  VTD_PLMLIMIT_REG_OFF:
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
      #ifndef __XMHF_VERIFICATION__
      _vtd_reg(dmardevice, VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&t_vtd_ecap_reg.value);
      #endif
      regaddr=dmardevice->regbaseaddr+(t_vtd_ecap_reg.bits.iro*16)+0x8;
      break;
    }
      
    case  VTD_IVA_REG_OFF:{
      VTD_ECAP_REG  t_vtd_ecap_reg;
      regtype=VTD_REG_64BITS;
      #ifndef __XMHF_VERIFICATION__
      _vtd_reg(dmardevice, VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&t_vtd_ecap_reg.value);
      #endif
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
        *((u32 *)value)= xmhf_baseplatform_arch_flat_readu32(regaddr);
      else
        xmhf_baseplatform_arch_flat_writeu32(regaddr, *((u32 *)value));
        
      break;
    }
    
    case VTD_REG_64BITS:{	//64-bit r/w
      if(access == VTD_REG_READ)
        *((u64 *)value)=xmhf_baseplatform_arch_flat_readu64(regaddr);
      else
        xmhf_baseplatform_arch_flat_writeu64(regaddr, *((u64 *)value));
    
      break;
    }
  
    default:
     printf("\n%s: Halt, Unsupported access width=%08x", __FUNCTION__, regtype);
     HALT();
  }

  return;
}


//scan for available DRHD units on the platform and populate the 
//global variables set:
//vtd_drhd[] (struct representing a DRHD unit) 
//vtd_num_drhd (number of DRHD units detected)
//vtd_dmar_table_physical_address (physical address of the DMAR table)
//returns: true if all is fine else false
static bool _vtd_scanfor_drhd_units(void){
	ACPI_RSDP rsdp;
	ACPI_RSDT rsdt;
	u32 num_rsdtentries;
	u32 rsdtentries[ACPI_MAX_RSDT_ENTRIES];
	u32 status;
	VTD_DMAR dmar;
	u32 i, dmarfound;
	u32 remappingstructuresaddrphys;

	//zero out rsdp and rsdt structures
	//memset(&rsdp, 0, sizeof(ACPI_RSDP));
	//memset(&rsdt, 0, sizeof(ACPI_RSDT));

	//get ACPI RSDP
	status=xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp);
	//HALT_ON_ERRORCOND(status != 0);	//we need a valid RSDP to proceed
	if(status == 0)
		return false;
		
	printf("\n%s: RSDP at %08x", __FUNCTION__, status);
  
	//grab ACPI RSDT
	xmhf_baseplatform_arch_flat_copy((u8 *)&rsdt, (u8 *)rsdp.rsdtaddress, sizeof(ACPI_RSDT));
	printf("\n%s: RSDT at %08x, len=%u bytes, hdrlen=%u bytes", 
		__FUNCTION__, rsdp.rsdtaddress, rsdt.length, sizeof(ACPI_RSDT));
	
	//get the RSDT entry list
	num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT))/ sizeof(u32);
	//HALT_ON_ERRORCOND(num_rsdtentries < ACPI_MAX_RSDT_ENTRIES);
	if(num_rsdtentries >= ACPI_MAX_RSDT_ENTRIES){
			printf("\n%s: Error num_rsdtentries(%u) > ACPI_MAX_RSDT_ENTRIES (%u)", __FUNCTION__, num_rsdtentries, ACPI_MAX_RSDT_ENTRIES);
			return false;
	}
		
	xmhf_baseplatform_arch_flat_copy((u8 *)&rsdtentries, (u8 *)(rsdp.rsdtaddress + sizeof(ACPI_RSDT)),
			sizeof(u32)*num_rsdtentries);			
	printf("\n%s: RSDT entry list at %08x, len=%u", __FUNCTION__,
		(rsdp.rsdtaddress + sizeof(ACPI_RSDT)), num_rsdtentries);

	//find the VT-d DMAR table in the list (if any)
	for(i=0; i< num_rsdtentries; i++){
		xmhf_baseplatform_arch_flat_copy((u8 *)&dmar, (u8 *)rsdtentries[i], sizeof(VTD_DMAR));  
		if(dmar.signature == VTD_DMAR_SIGNATURE){
		  dmarfound=1;
		  break;
		}
	}     	
  
	//if no DMAR table, bail out
	if(!dmarfound){
		printf("\n%s: Error No DMAR table", __FUNCTION__);
		return false;  
	}
	
	vtd_dmar_table_physical_address = rsdtentries[i]; //DMAR table physical memory address;
	printf("\n%s: DMAR at %08x", __FUNCTION__, vtd_dmar_table_physical_address);

	//detect DRHDs in the DMAR table
	i=0;
	remappingstructuresaddrphys=vtd_dmar_table_physical_address+sizeof(VTD_DMAR);
	printf("\n%s: remapping structures at %08x", __FUNCTION__, remappingstructuresaddrphys);
  
	while(i < (dmar.length-sizeof(VTD_DMAR))){
		u16 type, length;
		xmhf_baseplatform_arch_flat_copy((u8 *)&type, (u8 *)(remappingstructuresaddrphys+i), sizeof(u16));
		xmhf_baseplatform_arch_flat_copy((u8 *)&length, (u8 *)(remappingstructuresaddrphys+i+sizeof(u16)), sizeof(u16));     

		switch(type){
			case  0:  //DRHD
				printf("\nDRHD at %08x, len=%u bytes", (u32)(remappingstructuresaddrphys+i), length);
				if(vtd_num_drhd >= VTD_MAX_DRHD){
						printf("\n%s: Error vtd_num_drhd (%u) > VTD_MAX_DRHD (%u)", __FUNCTION__, vtd_num_drhd, VTD_MAX_DRHD);
						return false;
				}
				xmhf_baseplatform_arch_flat_copy((u8 *)&vtd_drhd[vtd_num_drhd], (u8 *)(remappingstructuresaddrphys+i), length);
				vtd_num_drhd++;
				i+=(u32)length;
				break;

			default:	//unknown type, we skip this
				i += (u32)length;
				break;
		}
	}
    printf("\n%s: total DRHDs detected= %u units", __FUNCTION__, vtd_num_drhd);

	//[DEBUG]: be a little verbose about what we found
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
	
	return true;
}

//initialize a given DRHD unit to meet our requirements
static bool _vtd_drhd_initialize(VTD_DRHD *drhd){
	VTD_GCMD_REG gcmd;
	VTD_GSTS_REG gsts;
	VTD_FECTL_REG fectl;
	VTD_CAP_REG cap;
  
	//sanity check
	HALT_ON_ERRORCOND(drhd != NULL);

	//verify required capabilities
	{
		printf("\nVerifying DRHD capabilities...");

		//read CAP register
		_vtd_reg(drhd, VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);
		
		if(! (cap.bits.plmr && cap.bits.phmr) ){
			printf("\n%s: Error: PLMR unsupported", __FUNCTION__);
			return false;
		}
		
		printf("\nDRHD unit has all required capabilities");
	}
	
	//setup fault logging
	printf("\nSetting DRHD Fault-reporting to NON-INTERRUPT mode...");
	{
		//read FECTL
		  fectl.value=0;
		_vtd_reg(drhd, VTD_REG_READ, VTD_FECTL_REG_OFF, (void *)&fectl.value);

		//set interrupt mask bit and write
		fectl.bits.im=1;
		_vtd_reg(drhd, VTD_REG_WRITE, VTD_FECTL_REG_OFF, (void *)&fectl.value);

		//check to see if the IM bit actually stuck
		_vtd_reg(drhd, VTD_REG_READ, VTD_FECTL_REG_OFF, (void *)&fectl.value);

		if(!fectl.bits.im){
		  printf("\n%s: Error: Failed to set fault-reporting.", __FUNCTION__);
		  return false;
		}
	}
	printf("\nDRHD Fault-reporting set to NON-INTERRUPT mode.");
	
	return true;
}


//invalidate DRHD caches
//note: we do global invalidation currently
//returns: true if all went well, else false
static bool _vtd_drhd_invalidatecaches(VTD_DRHD *drhd){
	VTD_CCMD_REG ccmd;
	VTD_IOTLB_REG iotlb;

	//invalidate CET cache
  	//wait for context cache invalidation request to send
    do{
      _vtd_reg(drhd, VTD_REG_READ, VTD_CCMD_REG_OFF, (void *)&ccmd.value);
    }while(ccmd.bits.icc);    

	//initialize CCMD to perform a global invalidation       
    ccmd.value=0;
    ccmd.bits.cirg=1; //global invalidation
    ccmd.bits.icc=1;  //invalidate context cache
    
    //perform the invalidation
    _vtd_reg(drhd, VTD_REG_WRITE, VTD_CCMD_REG_OFF, (void *)&ccmd.value);

	//wait for context cache invalidation completion status
    do{
      _vtd_reg(drhd, VTD_REG_READ, VTD_CCMD_REG_OFF, (void *)&ccmd.value);
    }while(ccmd.bits.icc);    
	
	//if all went well CCMD CAIG = CCMD CIRG (i.e., actual = requested invalidation granularity)
	if(ccmd.bits.caig != 0x1){
		printf("\n%s: Error: Invalidatation of CET failed (%u)", __FUNCTION__, ccmd.bits.caig);
		return false;
	}

	//invalidate IOTLB
    //initialize IOTLB to perform a global invalidation
	iotlb.value=0;
    iotlb.bits.iirg=1; //global invalidation
    iotlb.bits.ivt=1;	 //invalidate
    
    //perform the invalidation
	_vtd_reg(drhd, VTD_REG_WRITE, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);
    
    //wait for the invalidation to complete
    do{
      _vtd_reg(drhd, VTD_REG_READ, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);
    }while(iotlb.bits.ivt);    
        
    //if all went well IOTLB IAIG = IOTLB IIRG (i.e., actual = requested invalidation granularity)
	if(iotlb.bits.iaig != 0x1){
		printf("\n%s: Error: Invalidation of IOTLB failed (%u)", __FUNCTION__, iotlb.bits.iaig);
		return false;
    }
  
	return true;
}



//setup blanket (full system) DMA protection using VT-d translation
//VT-d translation has 1 root entry table (RET) of 4kb
//each root entry (RE) is 128-bits which gives us 256 entries in the 
//RET, each corresponding to a PCI bus num. (0-255)
//each RE points to a context entry table (CET) of 4kb
//each context entry (CE) is 128-bits which gives us 256 entries in 
//the CET, accounting for 32 devices with 8 functions each as per the 
//PCI spec.
//each CE points to a PDPT type paging structure for  device
//we just employ the RET and ensure that every entry in the RET is 0 
//which means that the DRHD will
//not allow any DMA requests for PCI bus 0-255 
//(Sec 3.3.2, VT-d Spec. v1.2)
//return: true if everthing went well, else false
static bool _vtd_drhd_blanket_dmaprot_via_translation(VTD_DRHD *drhd){
	VTD_RTADDR_REG rtaddr;
	VTD_GCMD_REG gcmd;
	VTD_GSTS_REG gsts;
	
	//zero out RET, effectively preventing DMA reads and writes in the system
	memset((void *)&vtd_ret_table, 0, sizeof(vtd_ret_table));
	
	//setup DRHD RET (root-entry)
	printf("\nSetting up DRHD RET...");
	{
		//setup RTADDR with base of RET 
		rtaddr.value=(u64)&vtd_ret_table;
		_vtd_reg(drhd, VTD_REG_WRITE, VTD_RTADDR_REG_OFF, (void *)&rtaddr.value);
    
		//latch RET address by using GCMD.SRTP
		gcmd.value=0;
		gcmd.bits.srtp=1;
		_vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);
    
		//ensure the RET address was latched by the h/w
		_vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
    
		if(!gsts.bits.rtps){
			printf("\n%s: Error	Failed to latch RTADDR");
			return false;
		}
	}
	printf("\nDRHD RET initialized.");
	
	//invalidate caches
	if(!_vtd_drhd_invalidatecaches(drhd))
		return false;


	//turn on translation
	printf("\nEnabling VT-d translation...");
	{
		gcmd.value=0;
		gcmd.bits.te=1;
		#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
		assert(gcmd.bits.te == 1);
		#endif

		_vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);

		//wait for translation enabled status to go green...
		_vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
		while(!gsts.bits.tes){
			_vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
		}
	}
	printf("\nVT-d translation enabled.");

	return true;
}



////////////////////////////////////////////////////////////////////////
// globals (exported) interfaces

//protect a given physical range of memory (membase to membase+size)
//using VT-d PMRs
//return true if everything went fine, else false
bool vtd_dmaprotect(u32 membase, u32 size){
	u32 i;
	
#ifndef __XMHF_VERIFICATION__	

	printf("\n%s: size=%08x", __FUNCTION__, size);
	
	//scan for available DRHD units in the platform
	if(!_vtd_scanfor_drhd_units())
		return false;
	
	//initialize all DRHD units
	for(i=0; i < vtd_num_drhd; i++){
		printf("\n%s: Setting up DRHD unit %u...", __FUNCTION__, i);
		
		
		if(!_vtd_drhd_initialize(&vtd_drhd[i]) )
			return false;
	
		if(!_vtd_drhd_blanket_dmaprot_via_translation(&vtd_drhd[i]))
			return false;
	}

#endif //__XMHF_VERIFICATION__

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup 
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	xmhf_baseplatform_arch_flat_writeu32(vtd_dmar_table_physical_address, 0UL);

	//success
	printf("\n%s: success, leaving...", __FUNCTION__);

	return true;
}
