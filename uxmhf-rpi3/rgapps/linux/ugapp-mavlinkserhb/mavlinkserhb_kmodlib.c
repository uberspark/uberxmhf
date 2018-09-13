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

#include <linux/init.h>           // macros used to mark up functions e.g. __init __exit
#include <linux/module.h>         // core header for loading LKMs into the kernel
#include <linux/device.h>         // header to support the kernel Driver Model
#include <linux/kernel.h>         // contains types, macros, functions for the kernel
#include <linux/fs.h>             // header for the Linux file system support
#include <linux/mm.h>             // header for the Linux memory management support
#include <linux/highmem.h>             // header for the Linux memory management support
#include <asm/uaccess.h>          // required for the copy to user function
#include <asm/io.h>          // required for the copy to user function

#include "../../../include/mavlinkserhb.h"


void __hvc(u32 uhcall_function, void *uhcall_buffer,
		u32 uhcall_buffer_len){

	asm volatile
		(	" mov r0, %[in_0]\r\n"
			" mov r1, %[in_1]\r\n"
			" mov r2, %[in_2]\r\n"
			".long 0xE1400071 \r\n"
				: // outputs
				: [in_0] "r" (uhcall_function), [in_1] "r" (uhcall_buffer), [in_2] "r" (uhcall_buffer_len)  // inouts
	           : "r0", "r1", "r2" //clobber
	    );
}


void mavlinkserhb_initialize(void){

	uapp_mavlinkserhb_param_t *mlhbsp;
	struct page *mlhbsp_page;
	u32 mlhbsp_paddr;

	mlhbsp_page = alloc_page(GFP_KERNEL | __GFP_ZERO);

	if(!mlhbsp_page){
		return false;
	}

	mlhbsp = (uapp_mavlinkserhb_param_t *)page_address(mlhbsp_page);

	mlhbsp->uhcall_fn = UAPP_MAVLINKSERHB_UHCALL_INITIALIZE;

	mlhbsp_paddr = page_to_phys(mlhbsp_page);
	__hvc(UAPP_MAVLINKSERHB_UHCALL, mlhbsp_paddr, sizeof(uapp_mavlinkserhb_param_t));

	if(!mlhbsp->status){
		__free_page(mlhbsp_page);
		return false;
	}

	__free_page(mlhbsp_page);
	return;
}



bool mavlinkserhb_send(u8 *buffer, u32 buf_len){

	uapp_mavlinkserhb_param_t *mlhbsp;
	struct page *mlhbsp_page;
	u32 mlhbsp_paddr;
	struct page *buffer_page;
	u32 buffer_page_paddr;

	//sanity check length
	if(buf_len > 4096)
		return false;

	//allocate parameter page
	mlhbsp_page = alloc_page(GFP_KERNEL | __GFP_ZERO);

	if(!mlhbsp_page){
		return false;
	}

	mlhbsp = (uapp_mavlinkserhb_param_t *)page_address(mlhbsp_page);

	//allocate buffer physical page
	buffer_page = alloc_page(GFP_KERNEL | __GFP_ZERO);

	if(!buffer_page){
		return false;
	}

	buffer_page_paddr = page_to_phys(buffer_page);

	//copy over buffer contents to buffer physical page
	memcpy(page_address(buffer_page), buffer, buf_len);

	//issue send hypercall
	mlhbsp->uhcall_fn = UAPP_MAVLINKSERHB_UHCALL_SEND;
	mlhbsp->iparam_1 = buffer_page_paddr;
	mlhbsp->iparam_2 = buf_len;

	mlhbsp_paddr = page_to_phys(mlhbsp_page);
	__hvc(UAPP_MAVLINKSERHB_UHCALL, mlhbsp_paddr, sizeof(uapp_mavlinkserhb_param_t));

	if(!mlhbsp->status){
		__free_page(mlhbsp_page);
		__free_page(buffer_page);
		return false;
	}

	__free_page(mlhbsp_page);
	__free_page(buffer_page);
	return true;
}




