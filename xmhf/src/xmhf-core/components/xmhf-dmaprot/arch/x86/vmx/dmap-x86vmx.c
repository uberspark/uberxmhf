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

//VT-d 3-level DMA protection page table data structure addresses
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
  ASSERT( !(pdptphysaddr & 0x00000FFFUL) && !(pdtphysaddr & 0x00000FFFUL) && !((ptphysaddr & 0x00000FFFUL)) );

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
static void _vtd_setupRETCET(u32 vtd_pdpt_paddr, 
		u32 vtd_ret_paddr, u32 vtd_ret_vaddr,
		u32 vtd_cet_paddr, u32 vtd_cet_vaddr){
  
	u32 retphysaddr, cetphysaddr;
  u32 i, j;
  u64 *value;
  
  retphysaddr=vtd_ret_paddr;
  (void)retphysaddr;
  cetphysaddr=vtd_cet_paddr;

	//sanity check that pdpt base address is page-aligned
	ASSERT( !(vtd_pdpt_paddr & 0x00000FFFUL) );
	
  //initialize RET  
  for(i=0; i < PCI_BUS_MAX; i++){
    value=(u64 *)(vtd_ret_vaddr + (i * 16));
    *(value+1)=(u64)0x0ULL;
    *value=(u64) (cetphysaddr +(i * PAGE_SIZE_4K));
    
    //sanity check that CET is page aligned
    ASSERT( !(*value & 0x0000000000000FFFULL) );

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
static void _vtd_setupRETCET_bootstrap( 
		u32 vtd_ret_paddr, u32 vtd_ret_vaddr,
		u32 vtd_cet_paddr, u32 vtd_cet_vaddr){
  
	//sanity check that RET and CET are page-aligned
	ASSERT( !(vtd_ret_paddr & 0x00000FFFUL) && !(vtd_cet_paddr & 0x00000FFFUL) );
	
	//zero out CET, we dont require it for bootstrapping
	memset((void *)vtd_cet_vaddr, 0, PAGE_SIZE_4K);
	
	//zero out RET, effectively preventing DMA reads and writes in the system
	memset((void *)vtd_ret_vaddr, 0, PAGE_SIZE_4K);
}


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
        *((u32 *)value)= emhf_baseplatform_arch_flat_readu32(regaddr);
      else
        emhf_baseplatform_arch_flat_writeu32(regaddr, *((u32 *)value));
        
      break;
    }
    
    case VTD_REG_64BITS:{	//64-bit r/w
      if(access == VTD_REG_READ)
        *((u64 *)value)=emhf_baseplatform_arch_flat_readu64(regaddr);
      else
        emhf_baseplatform_arch_flat_writeu64(regaddr, *((u64 *)value));
    
      break;
    }
  
    default:
     printf("\n%s: Halt, Unsupported access width=%08x", __FUNCTION__, regtype);
     HALT();
  }

  return;
}

//------------------------------------------------------------------------------
//initialize a DRHD unit
//note that the VT-d documentation does not describe the precise sequence of
//steps that need to be followed to initialize a DRHD unit!. we use our
//common sense instead...:p
static void _vtd_drhd_initialize(VTD_DRHD *drhd, u32 vtd_ret_paddr){
	VTD_GCMD_REG gcmd;
  VTD_GSTS_REG gsts;
  VTD_FECTL_REG fectl;
  VTD_CAP_REG cap;
  VTD_RTADDR_REG rtaddr;
  VTD_CCMD_REG ccmd;
  VTD_IOTLB_REG iotlb;
  
  //sanity check
	ASSERT(drhd != NULL);


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
    ASSERT(cap.bits.nd != 0x7);
    
    #if 0	//unfortunately this support is not mainstream yet, unsupported on HP8540p-corei5
    //check for super-page support (at least 2M page mapping support)
    printf("\n	SPS=%x", cap.bits.sps);
		if(!(cap.bits.sps & 0x1)){
			printf("\n	SPS does not support 2M page size. Halting!");
			HALT();
		}
		#endif
    
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
	
	  
  //2. disable device
  /*disabling DRHD is optional as the steps below initialize required
    registers irrespective of their reset state. however, some machines
    e.g., HP 8100 and on Lenovo x201 (bug #116) actually freeze if we
    try to disable DRHD. so we just omit this step*/
	/*
	printf("\n	Disabling DRHD...");
  {
		gcmd.value=0;	//disable translation
	  ASSERT( gcmd.bits.te == 0);	
	  _vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);
	  _vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
	    
	  //translation enabled status must be cleared on success
	  if(gsts.bits.tes){
	    printf("\n	Disable op. failed. Halting!");
	    HALT();
	  }
	}
  printf("Done.");
  */
  

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
    
    //wait for the invalidation to complete
    do{
      _vtd_reg(drhd, VTD_REG_READ, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);
    }while(iotlb.bits.ivt);    
    
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
      _vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);
      
			//wait for translation enabled status to go green...
			_vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
      while(!gsts.bits.tes){
        _vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
      }
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
      //wait for PMR disabled...
			do{
        _vtd_reg(drhd, VTD_REG_READ, VTD_PMEN_REG_OFF, (void *)&pmen.value);
      }while(pmen.bits.prs);
  	}
	}
	printf("Done.");

}


//------------------------------------------------------------------------------
//vt-d invalidate cachess note: we do global invalidation currently
static void _vtd_invalidatecaches(void){
  u32 i;
  VTD_CCMD_REG ccmd;
  VTD_IOTLB_REG iotlb;
  
  
  for(i=0; i < vtd_num_drhd; i++){
    //1. invalidate CET cache
  	//wait for context cache invalidation request to send
    do{
      _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_CCMD_REG_OFF, (void *)&ccmd.value);
    }while(ccmd.bits.icc);    

		//initialize CCMD to perform a global invalidation       
    ccmd.value=0;
    ccmd.bits.cirg=1; //global invalidation
    ccmd.bits.icc=1;  //invalidate context cache
    
    //perform the invalidation
    _vtd_reg(&vtd_drhd[i], VTD_REG_WRITE, VTD_CCMD_REG_OFF, (void *)&ccmd.value);

		//wait for context cache invalidation completion status
    do{
      _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_CCMD_REG_OFF, (void *)&ccmd.value);
    }while(ccmd.bits.icc);    

		//if all went well CCMD CAIG = CCMD CIRG (i.e., actual = requested invalidation granularity)
    if(ccmd.bits.caig != 0x1){
      printf("\n	Invalidatation of CET failed. Halting! (%u)", ccmd.bits.caig);
      HALT();
    }

		//2. invalidate IOTLB
    //initialize IOTLB to perform a global invalidation
		iotlb.value=0;
    iotlb.bits.iirg=1; //global invalidation
    iotlb.bits.ivt=1;	 //invalidate
    
    //perform the invalidation
		_vtd_reg(&vtd_drhd[i], VTD_REG_WRITE, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);
    
    //wait for the invalidation to complete
    do{
      _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);
    }while(iotlb.bits.ivt);    
    
    //if all went well IOTLB IAIG = IOTLB IIRG (i.e., actual = requested invalidation granularity)
		if(iotlb.bits.iaig != 0x1){
      printf("\n	Invalidation of IOTLB failed. Halting! (%u)", iotlb.bits.iaig);
      HALT();
    }
  }

}


//==============================================================================
//global (exported) functions

#define PAE_get_pdptindex(x) ((x) >> 30)
#define PAE_get_pdtindex(x) (((x) << 2) >> 23)
#define PAE_get_ptindex(x) ( ((x) << 11) >> 23 )
#define PAE_get_pdtaddress(x) ( (u32) ( (u64)(x) & (u64)0x3FFFFFFFFFFFF000ULL ))
#define PAE_get_ptaddress(x) ( (u32) ( (u64)(x) & (u64)0x3FFFFFFFFFFFF000ULL ))


#if !defined (__DRTM_DMA_PROTECTION__)
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
	status=emhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp);
	ASSERT(status != 0);	//we need a valid RSDP to proceed
	printf("\n%s: RSDP at %08x", __FUNCTION__, status);

	//grab ACPI RSDT
	emhf_baseplatform_arch_flat_copy((u8 *)&rsdt, (u8 *)rsdp.rsdtaddress, sizeof(ACPI_RSDT));
	printf("\n%s: RSDT at %08x, len=%u bytes, hdrlen=%u bytes", 
		__FUNCTION__, rsdp.rsdtaddress, rsdt.length, sizeof(ACPI_RSDT));

	//get the RSDT entry list
	num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT))/ sizeof(u32);
	ASSERT(num_rsdtentries < ACPI_MAX_RSDT_ENTRIES);
	emhf_baseplatform_arch_flat_copy((u8 *)&rsdtentries, (u8 *)(rsdp.rsdtaddress + sizeof(ACPI_RSDT)),
			sizeof(u32)*num_rsdtentries);			
	printf("\n%s: RSDT entry list at %08x, len=%u", __FUNCTION__,
		(rsdp.rsdtaddress + sizeof(ACPI_RSDT)), num_rsdtentries);


	//find the VT-d DMAR table in the list (if any)
	for(i=0; i< num_rsdtentries; i++){
		emhf_baseplatform_arch_flat_copy((u8 *)&dmar, (u8 *)rsdtentries[i], sizeof(VTD_DMAR));  
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
	emhf_baseplatform_arch_flat_writeu32(dmaraddrphys, 0UL);


	//success
	printf("\n%s: success, leaving...", __FUNCTION__);
}
#endif

//initialize VMX EAP a.k.a VT-d
//returns 1 if all went well, else 0
//if input parameter bootstrap is 1 then we perform minimal translation
//structure initialization, else we do the full DMA translation structure
//initialization at a page-granularity
static u32 vmx_eap_initialize(u32 vtd_pdpt_paddr, u32 vtd_pdpt_vaddr,
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
	
	
	//zero out rsdp and rsdt structures
	memset(&rsdp, 0, sizeof(ACPI_RSDP));
	memset(&rsdt, 0, sizeof(ACPI_RSDT));

  //get ACPI RSDP
  status=emhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp);
  ASSERT(status != 0);	//we need a valid RSDP to proceed
  printf("\n%s: RSDP at %08x", __FUNCTION__, status);
  
	//grab ACPI RSDT
	emhf_baseplatform_arch_flat_copy((u8 *)&rsdt, (u8 *)rsdp.rsdtaddress, sizeof(ACPI_RSDT));
	printf("\n%s: RSDT at %08x, len=%u bytes, hdrlen=%u bytes", 
		__FUNCTION__, rsdp.rsdtaddress, rsdt.length, sizeof(ACPI_RSDT));
	
	//get the RSDT entry list
	num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT))/ sizeof(u32);
	ASSERT(num_rsdtentries < ACPI_MAX_RSDT_ENTRIES);
	emhf_baseplatform_arch_flat_copy((u8 *)&rsdtentries, (u8 *)(rsdp.rsdtaddress + sizeof(ACPI_RSDT)),
			sizeof(u32)*num_rsdtentries);			
  printf("\n%s: RSDT entry list at %08x, len=%u", __FUNCTION__,
		(rsdp.rsdtaddress + sizeof(ACPI_RSDT)), num_rsdtentries);


	//find the VT-d DMAR table in the list (if any)
  for(i=0; i< num_rsdtentries; i++){
  	emhf_baseplatform_arch_flat_copy((u8 *)&dmar, (u8 *)rsdtentries[i], sizeof(VTD_DMAR));  
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
		emhf_baseplatform_arch_flat_copy((u8 *)&type, (u8 *)(remappingstructuresaddrphys+i), sizeof(u16));
		emhf_baseplatform_arch_flat_copy((u8 *)&length, (u8 *)(remappingstructuresaddrphys+i+sizeof(u16)), sizeof(u16));     

    switch(type){
      case  0:  //DRHD
        printf("\nDRHD at %08x, len=%u bytes", (u32)(remappingstructuresaddrphys+i), length);
        ASSERT(vtd_num_drhd < VTD_MAX_DRHD);
				emhf_baseplatform_arch_flat_copy((u8 *)&vtd_drhd[vtd_num_drhd], (u8 *)(remappingstructuresaddrphys+i), length);
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
    printf("\n	Device %u on PCI seg %04x; base=0x%016LX", i, 
				vtd_drhd[i].pcisegment, vtd_drhd[i].regbaseaddr);
    _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);
    printf("\n		cap=0x%016LX", (u64)cap.value);
    _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&ecap.value);
    printf("\n		ecap=0x%016LX", (u64)ecap.value);
  }


  //initialize VT-d page tables (not done if we are bootstrapping)
	if(!isbootstrap){
		_vtd_setuppagetables(vtd_pdpt_paddr, vtd_pdpt_vaddr,
			vtd_pdts_paddr, vtd_pdts_vaddr,
			vtd_pts_paddr, vtd_pts_vaddr);
		printf("\n%s: setup VT-d page tables (pdpt=%08x, pdts=%08x, pts=%08x).", 
			__FUNCTION__, vtd_pdpt_paddr, vtd_pdts_paddr, vtd_pts_paddr);
	}	
		
	//initialize VT-d RET and CET
	if(!isbootstrap){
		_vtd_setupRETCET(vtd_pdpt_paddr, 
			vtd_ret_paddr, vtd_ret_vaddr,
			vtd_cet_paddr, vtd_cet_vaddr);
		printf("\n%s: setup VT-d RET (%08x) and CET (%08x).", 
			__FUNCTION__, vtd_ret_paddr, vtd_cet_paddr);
	}else{
		//bootstrapping
		_vtd_setupRETCET_bootstrap(
			vtd_ret_paddr, vtd_ret_vaddr,
			vtd_cet_paddr, vtd_cet_vaddr);
		printf("\n%s: setup VT-d RET (%08x) and CET (%08x) for bootstrap.", 
			__FUNCTION__, vtd_ret_paddr, vtd_cet_paddr);
	}

 	//initialize all DRHD units
  for(i=0; i < vtd_num_drhd; i++){
  	printf("\n%s: initializing DRHD unit %u...", __FUNCTION__, i);
  	_vtd_drhd_initialize(&vtd_drhd[i], vtd_ret_paddr);
  }

  //zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup 
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	if(!isbootstrap)
		emhf_baseplatform_arch_flat_writeu32(dmaraddrphys, 0UL);


	//success
	printf("\n%s: success, leaving...", __FUNCTION__);
	return 1;
}

////////////////////////////////////////////////////////////////////////
// GLOBALS

//"early" DMA protection initialization to setup minimal
//structures to protect a range of physical memory
//return 1 on success 0 on failure
u32 emhf_dmaprot_arch_x86vmx_earlyinitialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size,
	u64 memregionbase_paddr, u32 memregion_size){
	u32 vmx_eap_vtd_pdpt_paddr, vmx_eap_vtd_pdpt_vaddr;
	u32 vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr;
	u32 vmx_eap_vtd_cet_paddr, vmx_eap_vtd_cet_vaddr;

	(void)memregionbase_paddr;
	(void)memregion_size;
	
	printf("\nSL: Bootstrapping VMX DMA protection...");
			
	//we use 3 pages for Vt-d bootstrapping
	ASSERT(protectedbuffer_size >= (3*PAGE_SIZE_4K));
		
	vmx_eap_vtd_pdpt_paddr = protectedbuffer_paddr; 
	vmx_eap_vtd_pdpt_vaddr = protectedbuffer_vaddr; 
	vmx_eap_vtd_ret_paddr = protectedbuffer_paddr + PAGE_SIZE_4K; 
	vmx_eap_vtd_ret_vaddr = protectedbuffer_vaddr + PAGE_SIZE_4K; 
	vmx_eap_vtd_cet_paddr = protectedbuffer_paddr + (2*PAGE_SIZE_4K); 
	vmx_eap_vtd_cet_vaddr = protectedbuffer_vaddr + (2*PAGE_SIZE_4K); 
			
	return vmx_eap_initialize(vmx_eap_vtd_pdpt_paddr, vmx_eap_vtd_pdpt_vaddr,
					0, 0,
					0, 0,
					vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr,
					vmx_eap_vtd_cet_paddr, vmx_eap_vtd_cet_vaddr, 1);
}

//"normal" DMA protection initialization to setup required
//structures for DMA protection
//return 1 on success 0 on failure
u32 emhf_dmaprot_arch_x86vmx_initialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size){
	//Vt-d bootstrap has minimal DMA translation setup and protects entire
	//system memory. Relax this by instantiating a complete DMA translation
	//structure at a page granularity and protecting only the SL and Runtime
	u32 vmx_eap_vtd_pdpt_paddr, vmx_eap_vtd_pdpt_vaddr;
	u32 vmx_eap_vtd_pdts_paddr, vmx_eap_vtd_pdts_vaddr;
	u32 vmx_eap_vtd_pts_paddr, vmx_eap_vtd_pts_vaddr;
	u32 vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr;
	u32 vmx_eap_vtd_cet_paddr, vmx_eap_vtd_cet_vaddr;

	ASSERT(protectedbuffer_size >= (PAGE_SIZE_4K + (PAGE_SIZE_4K * PAE_PTRS_PER_PDPT) 
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
			
	return vmx_eap_initialize(vmx_eap_vtd_pdpt_paddr, vmx_eap_vtd_pdpt_vaddr,
					vmx_eap_vtd_pdts_paddr, vmx_eap_vtd_pdts_vaddr,
					vmx_eap_vtd_pts_paddr, vmx_eap_vtd_pts_vaddr,
					vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr,
					vmx_eap_vtd_cet_paddr, vmx_eap_vtd_cet_vaddr, 0);
}

//DMA protect a given region of memory, start_paddr is
//assumed to be page aligned physical memory address
void emhf_dmaprot_arch_x86vmx_protect(u32 start_paddr, u32 size){
  pt_t pt;
  u32 vaddr, end_paddr;
u32 pdptindex, pdtindex, ptindex;
  
  //compute page aligned end
  end_paddr = PAGE_ALIGN_4K(start_paddr + size);
  
  //sanity check
  ASSERT( (l_vtd_pdpt_paddr != 0) && (l_vtd_pdpt_vaddr != 0) );
  ASSERT( (l_vtd_pdts_paddr != 0) && (l_vtd_pdts_vaddr != 0) );
  ASSERT( (l_vtd_pts_paddr != 0) && (l_vtd_pts_vaddr != 0) );
  
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
  
  //flush the caches
	_vtd_invalidatecaches();  

}
