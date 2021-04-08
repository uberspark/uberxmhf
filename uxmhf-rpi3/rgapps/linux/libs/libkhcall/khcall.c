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
 * khcall -- guest interface for micro hypervisor hypercall
 *
 * author: amit vasudevan (amitvasudevan@acm.org), 
 *         matt mccormack (matthew.mccormack@live.com)
 */

#include <linux/types.h>
#include <linux/string.h>
#include <linux/kernel.h>
#include <linux/numa.h>
#include <linux/gfp.h>
#include <linux/mm.h>
#include <linux/highmem.h>

#include <khcall.h>

static void khcall_hvc(uint32_t khcall_function, void *khcall_buffer, uint32_t khcall_buffer_len);

//////
// khcall micro-hypervisor hypercall interface
// return true on success, false on error
//////
bool khcall(uint32_t khcall_function, void *khcall_buffer, uint32_t khcall_buffer_len){
        void *khcall_kbuff;
	uint64_t khcall_kbuff_paddr;
	struct page *k_page;
	
	//if khcall_buffer is NULL then khcall_buffer_len should be 0
	//for a NULL hypercall test
	if(khcall_buffer == NULL && khcall_buffer_len != 0){
	  printk("%s: error: line %u\n", __FUNCTION__, __LINE__);
	  return false;
	}

	//if khcall_buffer is not NULL then base address of khcall_buffer + khcall_buffer_len
	//cannot exceed a page size 
	if(khcall_buffer != NULL){
	  if ((((uint32_t)khcall_buffer % KHCALL_PM_PAGE_SIZE) + khcall_buffer_len) > KHCALL_PM_PAGE_SIZE){
	    printk("%s: error: line %u\n", __FUNCTION__, __LINE__);
	    return false;
	  }
	}

	// allocate kernel page
	k_page = alloc_page(GFP_KERNEL | __GFP_ZERO);
	khcall_kbuff = (void *)page_address(k_page);

	// copy hypercall buffer into kernel page
	memcpy(khcall_kbuff, khcall_buffer, khcall_buffer_len);

	// get kernel page physcial address
	khcall_kbuff_paddr = page_to_phys(k_page);
	
	//issue the hypercall
	khcall_hvc(khcall_function, (uint32_t)khcall_kbuff_paddr, khcall_buffer_len);

	// copy kernel page back to hypercall buffer
	memcpy(khcall_buffer, khcall_kbuff, khcall_buffer_len);

	// free kernel page
	__free_page(k_page);

	//hypercall succeeded
	return true;
}

static void khcall_hvc(uint32_t khcall_function, void *khcall_buffer, uint32_t khcall_buffer_len) {
    asm volatile
    ( " mov r0, %[in_0]\r\n"
      " mov r1, %[in_1]\r\n"
      " mov r2, %[in_2]\r\n"
      ".long 0xE1400071 \r\n"
      : 
      : [in_0] "r" (khcall_function), [in_1] "r" (khcall_buffer), [in_2] "r" (khcall_buffer_len)
      : "r0", "r1", "r2"
      );
}


void khcall_fast(uint32_t khcall_function, uint32_t param1, uint32_t param2) { 
    asm volatile
    ( " mov r0, %[in_0]\r\n"
      " mov r1, %[in_1]\r\n"
      " mov r2, %[in_2]\r\n"
      ".long 0xE1400070 \r\n"
        : 
        : [in_0] "r" (khcall_function), [in_1] "r" (param1), [in_2] "r" (param2)
        : "r0", "r1", "r2" ); 
}
