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
	ARM 8 stage-2 page table translation uapi
	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/debug.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/guestos.h>
//#include <uberspark/include/uberspark.h>

extern u64 l3_ldesc_table[L1_LDESC_TABLE_ENTRIES * L2_LDESC_TABLE_MAXENTRIES * L3_LDESC_TABLE_MAXENTRIES];

void uapi_s2pgtbl_setprot(u32 address, u64 protection){
	u32 index;

	if ( !((address >= UXMHF_CORE_START_ADDR) &&
			  (address < UXMHF_CORE_END_ADDR)) ){
		index = address/PAGE_SIZE_4K;
		l3_ldesc_table[index] = ldesc_make_s2_l3e_page(address, protection);
	}

}

u64 uapi_s2pgtbl_getprot(u32 address){
	u32 index;
	u64 result=0;

	if ( !((address >= UXMHF_CORE_START_ADDR) &&
			  (address < UXMHF_CORE_END_ADDR)) ){
		index = address/PAGE_SIZE_4K;
		result = ldesc_get_s2_l3e_page_attrs(l3_ldesc_table[index]);
	}else{
		result=0;
	}

	return result;
}


