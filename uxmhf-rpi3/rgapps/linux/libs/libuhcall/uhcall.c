/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

/*
 * uhcall -- guest interface for micro hypervisor hypercall
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>

#include <uhcall.h>

//////
// va_to_pa: virtual to physical address mapping
// return true on success, false on error
//////
bool uhcall_va2pa(void *vaddr, uint64_t *paddr) {
	FILE *pagemap;
	uint32_t offset;
	uint64_t page_frame_number = 0;

	//sanity check incoming parameters
	if (paddr == NULL)
		return false;

	// open the pagemap file for the current process
	pagemap = fopen("/proc/self/pagemap", "rb");
	if(pagemap == NULL)
		return false;	//unable to open pagemap file

	// seek to the page that vaddr is on
   offset = ((uint32_t)vaddr / getpagesize()) * UHCALL_PM_LENGTH;
   if(fseek(pagemap, (uint32_t)offset, SEEK_SET) != 0)
      return false; //Failed to seek pagemap to proper location

   // The page frame number is in bits 0-54 so read the
   // 8 bytes and clear evrything but 0-54
   fread(&page_frame_number, UHCALL_PM_LENGTH, 1, pagemap);

   if (page_frame_number & (1ULL << 63)) { // page present ?
	   *paddr = page_frame_number & ((1ULL << 54) - 1); // pfn mask
	   *paddr = *paddr * getpagesize();
	   fclose(pagemap);
	   return true;
   }else{
	   fclose(pagemap);
	   return false;
   }

#if 0
   page_frame_number &= 0x7FFFFFFFFFFFFFULL;

   fclose(pagemap);

   *paddr = (page_frame_number << UHCALL_PM_PAGE_SHIFT);
   return true;
#endif
}


//////
// uhcall micro-hypervisor hypercall interface
// return true on success, false on error
//////
bool uhcall(uint32_t uhcall_function, void *uhcall_buffer, uint32_t uhcall_buffer_len){
	int ret, fd;
	uhcallkmod_param_t uhcallp;
	uint64_t uhcall_buffer_paddr;
	
	//if uhcall_buffer is NULL then uhcall_buffer_len should be 0
	//for a NULL hypercall test
	if(uhcall_buffer == NULL && uhcall_buffer_len != 0){
	    printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
		return false;
	}

	//if uhcall_buffer is not NULL then base address of uhcall_buffer + uhcall_buffer_len
	//cannot exceed a page size
	if(uhcall_buffer != NULL){
		if ( (((uint32_t)uhcall_buffer % UHCALL_PM_PAGE_SIZE) + uhcall_buffer_len) > UHCALL_PM_PAGE_SIZE ){
		    printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
			return false;
		}
	}

#if 0
    //get buffer physical address
    if(!uhcall_va2pa(uhcall_buffer, &uhcall_buffer_paddr) ){
	    printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
    	return false;
    }


    //printf("%s: uhcall_buffer_paddr=0x%08x\n", __FUNCTION__, (uint32_t)uhcall_buffer_paddr);
#endif

	//open uhcallkmod device
	fd = open("/dev/uhcallkmod", O_RDWR);
	if (fd < 0){
	    printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
		return false; //Failed to open /dev/uhcallkmod
	}


#if 1
	//lock uhcall_buffer in memory
    if(mlock(uhcall_buffer, uhcall_buffer_len) == -1){
    //if(mlock(uhcall_buffer, 4096) == -1){
		printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
    	return false; //nFailed to lock page in memory
    }
#endif
	//populate uhcallkmod_param_t
	uhcallp.uhcall_function=uhcall_function;
	//uhcallp.uhcall_buffer=(uint32_t)uhcall_buffer;
	//	uhcallp.uhcall_buffer=(void *)(uint32_t)uhcall_buffer_paddr;
	uhcallp.uhcall_buffer=(void *)(uint32_t)uhcall_buffer;	
	uhcallp.uhcall_buffer_len=uhcall_buffer_len;

	//printf("%s: uhcall_function=%u, uhcall_buffer=0x%08x, uhcall_buffer_len=%u\n", __FUNCTION__,
	//		uhcallp.uhcall_function, uhcallp.uhcall_buffer, uhcallp.uhcall_buffer_len);

	//issue the hypercall
	ret = write(fd, &uhcallp, sizeof(uhcallp));
	if (ret < 0){
	    printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
		return false;	//error in issuing hypercall
	}

#if 1
	//unlock uhcall_buffer page
	if(munlock(uhcall_buffer, uhcall_buffer_len) == -1){
	//if(munlock(uhcall_buffer, 4096) == -1){
		printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
		return false; //Failed to unlock page in memory
	}
#endif
	if ( close(fd) < 0 ){
	    printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
		return false;	//error in closing uhcallkmod device
	}

	//hypercall succeeded
	return true;
}
