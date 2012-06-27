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

// EMHF DMA protection component implementation for x86 SVM
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h> 

//static variables 
//SVM EAP container structure, contains the DEV registers and the DEV bitmap 
static struct _svm_eap _svm_eap __attribute__(( section(".data") ));

//SVM DEV Bitmap. Currently covers 0-4GB physical memory range. Should
//be fine since our hypervisor is loaded within this range.
//u8	dev_bitmap[131072];


//forward declarations for some static (local) functions
static void svm_eap_dev_write(u32 function, u32 index, u32 value);
static u32 svm_eap_dev_read(u32 function, u32 index);

//initialize SVM EAP a.k.a DEV
//returns 1 if all went well, else 0
//inputs: physical and virtual addresses of the DEV bitmap area
static u32 svm_eap_initialize(u32 dev_bitmap_paddr, u32 dev_bitmap_vaddr){
	u32 mc_capabilities_pointer;
	u32 mc_caplist_nextptr;
	u32 mc_caplist_id;
	u32 found_dev=0;
	
	//clear the SVM EAP container structure members including the DEV
	//bitmap
	memset((void *)&_svm_eap, 0, sizeof(struct _svm_eap));

	//ensure dev_bitmap_paddr is PAGE_ALIGNED
	ASSERT( (dev_bitmap_paddr & 0xFFF) == 0 );

	
	//we first need to detect the DEV capability block
	//the DEV capability block is in the PCI configuration space 
	//(15.24.4, AMD Dev. Vol2)
	//more precisely it is a part of the Miscellaneous Control	
	//HyperTransport Configuration space. (3.6, AMD BKDG)
	//HyperTransport device configuration space is 
 	//accessed by using bus 0, devices 24 to 31, where device 24 corresponds 
 	//to node 0 and device 31 corresponds to node 7. (2.11, AMD BKDG 10h family)
 	//note: node 0 corresponds to 0th physical CPU package. So, if we have
 	//four logical cores on the same physical die, the HT device is on
 	//bus 0 as device 24 for all the cores. well at least to my knowledge...
 	//Miscellaneous Control is function 3 (3.6, AMD BKDG)

	//step-1: we read capabilities pointer (PCI_CONF_HDR_IDX_CAPABILITIES_POINTER)
	//in b:d.f 0:24.3. If its 0, then DEV support is not available
		emhf_baseplatform_arch_x86_pci_type1_read(DEV_PCI_BUS, DEV_PCI_DEVICE, DEV_PCI_FUNCTION, PCI_CONF_HDR_IDX_CAPABILITIES_POINTER, sizeof(u32), &mc_capabilities_pointer);
		if(mc_capabilities_pointer == 0)
			return 0;	//DEV support unavailable
	
		ASSERT ( (u8)(mc_capabilities_pointer) == 0xF0 ); //p. 286, AMD BKDG
	
	  //traverse the capabilities list as per the PCI spec.
	  mc_caplist_nextptr = (u32)(u8)mc_capabilities_pointer;
	  
	  do{
		  //get the ID of this capability block
		  emhf_baseplatform_arch_x86_pci_type1_read(DEV_PCI_BUS, DEV_PCI_DEVICE, DEV_PCI_FUNCTION, mc_caplist_nextptr, sizeof(u8), &mc_caplist_id);
		  
			//check if this is a DEV capability ID block
			if((u8)mc_caplist_id == PCI_CAPABILITIES_POINTER_ID_DEV){
				found_dev = 1;
				break;
			}
		  
		  //get the index of the next capability block
			emhf_baseplatform_arch_x86_pci_type1_read(DEV_PCI_BUS, DEV_PCI_DEVICE, DEV_PCI_FUNCTION, mc_caplist_nextptr, sizeof(u8), &mc_caplist_nextptr);
		}while(mc_caplist_nextptr != 0);
	

  	//did we find a DEV capability block above? if no simply return
  	if(!found_dev)
  		return 0;
  		
  	//okay, we found a DEV capability block at index mc_caplist_nextptr
		printf("\n%s: found DEV capability block at index %04x", __FUNCTION__, mc_caplist_nextptr);
		
		//now obtain the PCI configuration space indices for DEV header, fn/idx
		//and data registers and store them in the SVM EAP container structure
		_svm_eap.dev_hdr_reg = mc_caplist_nextptr;
		_svm_eap.dev_fnidx_reg = mc_caplist_nextptr + sizeof(u32);
		_svm_eap.dev_data_reg = mc_caplist_nextptr + (2 * sizeof(u32));
		
		
		//print it out for now...
		printf("\n%s: dev_hdr_reg at %02x:%02x.%1x(%04x)", __FUNCTION__, DEV_PCI_BUS, DEV_PCI_DEVICE, DEV_PCI_FUNCTION, _svm_eap.dev_hdr_reg);
		printf("\n%s: dev_fnidx_reg at %02x:%02x.%1x(%04x)", __FUNCTION__, DEV_PCI_BUS, DEV_PCI_DEVICE, DEV_PCI_FUNCTION, _svm_eap.dev_fnidx_reg);
		printf("\n%s: dev_data_reg at %02x:%02x.%1x(%04x)", __FUNCTION__, DEV_PCI_BUS, DEV_PCI_DEVICE, DEV_PCI_FUNCTION, _svm_eap.dev_data_reg);
		
		
		//setup DEV
		{
			dev_cap_t dev_cap;
  		dev_map_t dev_map;
  		dev_base_lo_t dev_base_lo;
  		dev_base_hi_t dev_base_hi;
  		dev_cr_t dev_cr;
  		u32 i;

			//0. populate the DEV bitmap physical address in the EAP structure
			_svm_eap.dev_bitmap_vaddr = dev_bitmap_vaddr;
			printf("\n	DEV: bitmap at v:p addr %08x:%08x", _svm_eap.dev_bitmap_vaddr,
					dev_bitmap_paddr);

  		//1. read the DEV revision, and the number of maps and domains supported 
  		dev_cap.bytes = svm_eap_dev_read(DEV_CAP, 0);
  		printf("\n	DEV:rev=%u, n_doms=%u, n_maps=%u", dev_cap.fields.rev, dev_cap.fields.n_doms, dev_cap.fields.n_maps);
  		
			//2. disable all the DEV maps. AMD manuals do not mention anything about
			//the reset state of the map registers
  		dev_map.fields.valid0 = 0;
  		dev_map.fields.valid1 = 0;
  		for (i = 0; i < dev_cap.fields.n_maps; i++)
    		svm_eap_dev_write(DEV_MAP, i, dev_map.bytes);
			printf("\n	DEV: cleared map registers.");
			
			//3. set the DEV_BASE_HI and DEV_BASE_LO registers of domain 0 
  		dev_base_hi.bytes = 0; //our DEV bitmap is within 4GB physical 
		  svm_eap_dev_write(DEV_BASE_HI, 0, dev_base_hi.bytes);
  		dev_base_lo.fields.valid = 1; 		//valid
  		dev_base_lo.fields.protect = 0;		
  		dev_base_lo.fields.size = 0;      //4GB
  		dev_base_lo.fields.resv = 0;
  		dev_base_lo.fields.base_addr = (u32)dev_bitmap_paddr >> 12;
  		svm_eap_dev_write(DEV_BASE_LO, 0, dev_base_lo.bytes);
  		printf("\n	DEV: set DEV_BASE_LO and DEV_BASE_HI.");

			//4. invalidate the DEV_BASE_HIGH and DEV_BASE_LOW registers of all other
   		//domains.
		  dev_base_lo.fields.valid = 0;
  		dev_base_lo.fields.base_addr = 0;
  		for (i = 1; i < dev_cap.fields.n_doms; i ++){
    		svm_eap_dev_write(DEV_BASE_HI, i, dev_base_hi.bytes);
    		svm_eap_dev_write(DEV_BASE_LO, i, dev_base_lo.bytes);
  		}
      printf("\n	DEV: invalidated other domains.");
      
      
      //5. enable DEV protections 
  		dev_cr.fields.deven = 1;
  		dev_cr.fields.iodis = 1;
  		dev_cr.fields.mceen = 0;
  		dev_cr.fields.devinv = 0;
  		dev_cr.fields.sldev = 1; 
  		dev_cr.fields.walkprobe = 0;
  		dev_cr.fields.resv0 = 0;
  		dev_cr.fields.resv1 = 0;
  		svm_eap_dev_write(DEV_CR, 0, dev_cr.bytes);
			printf("\n	DEV: enabled protections.");
      	
		}

		
		return 1;  	
}


//------------------------------------------------------------------------------
//early initialization of SVM EAP a.k.a DEV
//returns 1 if all went well, else 0
//inputs: physical and virtual addresses of a buffer that is
//already DMA protected, starting address and size (in bytes) 
//of the physical memory region to be DMA protected 
//Note: this function exists since we need to bootstrap DEV
//protections early on. We cannot afford to have the entire DEV bitmap
//(128K) within the SL, so we use a DMA-protected buffer 
//(capable of DMA protecting a contiguous physical memory range)
//that lies within the initially DMA-protected SL region to protect 
//the runtime physical memory.
//The runtime then re-initializes DEV once it gets control after a 
//successful integrity check.
static u32 svm_eap_early_initialize(u32 protected_buffer_paddr, 
			u32 protected_buffer_vaddr, u32 memregion_paddr_start, 
				u32 memregion_size){
	u32 dev_bitmap_paddr = 0;
		

	printf("\n%s: protected buffer, paddr=%08x, vaddr=%08x", __FUNCTION__, 
		protected_buffer_paddr, protected_buffer_vaddr);

	//sanity check: the protected buffer MUST be page aligned
	ASSERT( !(protected_buffer_paddr & 0x00000FFF) &&
					!(protected_buffer_vaddr & 0x00000FFF) );	


	//compute DEV bitmap base address depending on the physical base address
	//of the protected buffer and the physical base address of the memory
	//region
	//Note: we assume the protected buffer size to be 8K on AMD 
	//sanity check: memregion size cannot be greater than 128MB
	ASSERT( memregion_size < (PAGE_SIZE_4K * 8 * PAGE_SIZE_4K) );
	
	{
		u32 memregion_paligned_paddr_start;
		u32 memregion_pfn=0;
		u32 devbitmap_bytes_before=0;
		u32 offset=0; //this is the offset of the memory page corresponding to SL physical base
								  //within the 8K protected DEV buffer 
		
		//compute page-aligned base address of memory region
		memregion_paligned_paddr_start = PAGE_ALIGN_4K(memregion_paddr_start);
		
		//compute pfn of memregion
		memregion_pfn = memregion_paligned_paddr_start / PAGE_SIZE_4K;
			
	  //thus, there are memregion_pfn pages that need to be accounted for
	  //until we hit our protected buffer in the DEV bitmap
	  //each page is 1 bit in the bitmap, so compute number of bytes of
	  //DEV bitmap we need before our protected buffer
	  devbitmap_bytes_before =  memregion_pfn / 8; //8-bits in a byte
	  
	  //the physical base address of the DEV bitmap will be our protected
	  //buffer physical base minus devbitmap_bytes_before
	  //Note: we dont care about other parts of the DEV bitmap except for
	  //our protected buffer which is assumed to be protected...
	  dev_bitmap_paddr = protected_buffer_paddr - devbitmap_bytes_before;
	  printf("\nSL:%s dev_bitmap_paddr=%08x", __FUNCTION__, dev_bitmap_paddr);
	  
	  //DEV bitmap base MUST be page aligned, however dev_bitmap_paddr
		//can violate this, so make sure we page align it and account for the
		//"offset" within the 8K protected DEV buffer
		if(dev_bitmap_paddr & 0x00000FFFUL){
			offset = PAGE_SIZE_4K - (dev_bitmap_paddr & 0x00000FFFUL);	//offset is always less than 4K 
	  	dev_bitmap_paddr += offset;	 //page-align dev_bitmap_paddr
	  	printf("\nSL:%s dev_bitmap_paddr page-aligned to %08x", __FUNCTION__, dev_bitmap_paddr);
	  }
	  
	  //sanity check: dev_bitmap_paddr MUST be page aligned
	  ASSERT(!(dev_bitmap_paddr & 0x00000FFF));
	  
	  //now make sure the protected buffer (4K in our case) is set to all 1's
		//effectively preventing DMA reads and writes from memregion_paligned_paddr_start
		//to memregion_paligned_paddr_start + 128M
		memset((void *)((u32)protected_buffer_vaddr+(u32)offset), 0xFF, PAGE_SIZE_4K);
	}
	
	
	//setup DEV 
	return svm_eap_initialize(dev_bitmap_paddr, dev_bitmap_paddr);
}



//DEV "read" function
//inputs: function (DEV function), index (DEV functions DEV_BASE_LO,
//DEV_BASE_HI and DEV_MAP have multiple instances, the index selects
//the appropriate instance in such cases; 0 for all other functions),
static u32 svm_eap_dev_read(u32 function, u32 index){
	u32 value;

	//sanity check on DEV registers
	ASSERT(_svm_eap.dev_hdr_reg != 0 && _svm_eap.dev_fnidx_reg !=0 && _svm_eap.dev_data_reg != 0);

	//step-1: write function and index to dev_fnidx_reg
	//format of dev_fnidx_reg is in AMD Dev. Vol2 (p. 407)
	emhf_baseplatform_arch_x86_pci_type1_write(DEV_PCI_BUS, DEV_PCI_DEVICE, DEV_PCI_FUNCTION,
		_svm_eap.dev_fnidx_reg, sizeof(u32), (u32)(((function & 0xff) << 8) + (index & 0xff)) );

	//step-2: read 32-bit value from dev_data_reg
	emhf_baseplatform_arch_x86_pci_type1_read(DEV_PCI_BUS, DEV_PCI_DEVICE, DEV_PCI_FUNCTION,
		_svm_eap.dev_data_reg, sizeof(u32), &value);
  
  return value;
}

//DEV "write" function
//inputs: function (DEV function), index (DEV functions DEV_BASE_LO,
//DEV_BASE_HI and DEV_MAP have multiple instances, the index selects
//the appropriate instance in such cases; 0 for all other functions),
//and value (value to be written to the DEV function)
static void svm_eap_dev_write(u32 function, u32 index, u32 value){
	
	//sanity check on DEV registers
	ASSERT(_svm_eap.dev_hdr_reg != 0 && _svm_eap.dev_fnidx_reg !=0 && _svm_eap.dev_data_reg != 0);

	//step-1: write function and index to dev_fnidx_reg
	//format of dev_fnidx_reg is in AMD Dev. Vol2 (p. 407)
	emhf_baseplatform_arch_x86_pci_type1_write(DEV_PCI_BUS, DEV_PCI_DEVICE, DEV_PCI_FUNCTION,
		_svm_eap.dev_fnidx_reg, sizeof(u32), (u32)(((function & 0xff) << 8) + (index & 0xff)) );

	//step-2: write 32-bit value to dev_data_reg
	emhf_baseplatform_arch_x86_pci_type1_write(DEV_PCI_BUS, DEV_PCI_DEVICE, DEV_PCI_FUNCTION,
		_svm_eap.dev_data_reg, sizeof(u32), value);
}

//------------------------------------------------------------------------------
//SVM DEV function implementation

//helper functions to set and clear page protections in the DEV bitmap
//passed as a bit vector to these functions
static void svm_eap_dev_set_page_protection(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

	//sanity check
	ASSERT ( bit_vector != NULL );

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] |= (1 << bit_offset);

  return;
}

/*static void svm_eap_dev_clear_page_protection(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

 	//sanity check
	ASSERT ( bit_vector != NULL );

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] &= ~(1 << bit_offset);

  return;
}*/


//invalidate DEV cache
static void svm_eap_dev_invalidate_cache(void){
  dev_cr_t dev_cr;

  dev_cr.bytes = svm_eap_dev_read(DEV_CR, 0);	//read current DEV_CR value
  dev_cr.fields.devinv = 1;										//clear DEV cache
  dev_cr.fields.deven = 1;										//ensure DEV is enabled
  svm_eap_dev_write(DEV_CR, 0, dev_cr.bytes);	//write modified DEV_CR to invalidate caches

  //wait until DEV h/w completes invalidation, seems like this may
  //not be fast enough for us to skip the wait!
  do{
		dev_cr.bytes = svm_eap_dev_read(DEV_CR, 0);	//read DEV_CR value
	}while(dev_cr.fields.devinv == 1);	//h/w clears the devinv bit when done

  return;
}

/*
//clear DEV protection for a range of physical pages
//input: paddr is the address of the first page and size
//is the size of the memory region (rounded to a page) in bytes
static void svm_eap_dev_unprotect(u32 paddr, u32 size){
	u32 paligned_paddr_start, paligned_paddr_end, i;
	
	//compute page-aligned physical start and end addresses
	paligned_paddr_start = PAGE_ALIGN_4K(paddr);
	paligned_paddr_end = PAGE_ALIGN_4K((paddr+size));
	
	//protect pages from paligned_paddr_start through paligned_paddr_end inclusive
	for(i=paligned_paddr_start; i <= paligned_paddr_end; i+= PAGE_SIZE_4K){
		svm_eap_dev_clear_page_protection(i >> PAGE_SHIFT_4K, (u8 *)_svm_eap.dev_bitmap_vaddr);
		svm_eap_dev_invalidate_cache();	//flush DEV cache
	}
}*/


////////////////////////////////////////////////////////////////////////
// GLOBALS

//"early" DMA protection initialization to setup minimal
//structures to protect a range of physical memory
//return 1 on success 0 on failure
u32 emhf_dmaprot_arch_x86svm_earlyinitialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size,
	u64 memregionbase_paddr, u32 memregion_size){

	//sanity check: protected DEV buffer MUST be page-aligned
	ASSERT(!(protectedbuffer_paddr & 0x00000FFF));
	ASSERT(!(protectedbuffer_vaddr & 0x00000FFF));
	ASSERT(protectedbuffer_size >= (PAGE_SIZE_4K * 2));
	
	printf("\nSL: initializing SVM DMA protection...");

	return svm_eap_early_initialize(protectedbuffer_paddr, protectedbuffer_vaddr,
					memregionbase_paddr, memregion_size);
}

//"normal" DMA protection initialization to setup required
//structures for DMA protection
//return 1 on success 0 on failure
u32 emhf_dmaprot_arch_x86svm_initialize(u64 protectedbuffer_paddr,
	u32 protectedbuffer_vaddr, u32 protectedbuffer_size){

	ASSERT(protectedbuffer_size >= 131072);	//we need 128K 

	return svm_eap_initialize(protectedbuffer_paddr, protectedbuffer_vaddr);
}

//DMA protect a given region of memory, start_paddr is
//assumed to be page aligned physical memory address
void emhf_dmaprot_arch_x86svm_protect(u32 start_paddr, u32 size){
	u32 paligned_paddr_start, paligned_paddr_end, i;
	
	//compute page-aligned physical start and end addresses
	paligned_paddr_start = PAGE_ALIGN_4K(start_paddr);
	paligned_paddr_end = PAGE_ALIGN_4K((start_paddr+size));
	
	//protect pages from paligned_paddr_start through paligned_paddr_end inclusive
	for(i=paligned_paddr_start; i <= paligned_paddr_end; i+= PAGE_SIZE_4K){
		svm_eap_dev_set_page_protection(i >> PAGE_SHIFT_4K, (u8 *)_svm_eap.dev_bitmap_vaddr);
		svm_eap_dev_invalidate_cache();	//flush DEV cache
	}
}
