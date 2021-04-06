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
	uhcalltest hypapp
	guest hypercall test 
	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/debug.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/i2c-ioaccess.h>

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uhcalltest.h>
//#include <uberspark/include/uberspark.h>

#define MAX_LVL1_ENTRIES	4096
#define MAX_LVL2_ENTRIES	256

#define SIZEOF_LVL1_ENTRY_MAP	(1024*1024)	//each lvl1 entry maps to 1MB of memory
#define SIZEOF_LVL2_ENTRY_MAP	(1024*1024)	//each lvl1 entry maps to 1MB of memory


/*
bool va2pa(uint32_t va, u32 *pa){
	u32 par;
	u8 *ch;

	//_XDPRINTFSMP_("%s: ENTER: va=0x%08x\n", __func__, va);

	//sysreg_tlbiallh();
#if 0
	sysreg_ats12nsour(va);
	par = sysreg_read_par();
#endif

	sysreg_ats1cpr(va);
	par = sysreg_read_par();

	//_XDPRINTFSMP_("%s: PAR=0x%08x\n", __func__, par);

	if(par & 0x1)
		return false; 	//_XDPRINTFSMP_("%s: Fault in address translation. Halting!\n", __func__);

	par &= 0xFFFFF000UL;

	//_XDPRINTFSMP_("%s: PAR after pruning=0x%08x\n", __func__, par);

	*pa = par;

	//_XDPRINTFSMP_("%s: EXIT: pa=0x%08x\n", __func__, *pa);

	return true;
}
*/


//return true if handled the hypercall, false if not
bool uapp_i2c_ioaccess_handlehcall(u32 i2c_ioaccess_function, void *i2c_ioaccess_buffer, u32 i2c_ioaccess_buffer_len){
	i2c_ioaccess_param_t *uhctp;
	uint32_t i;
	//u32 uhcall_buffer_paddr;

	if(i2c_ioaccess_function != UAPP_I2C_IOACCESS_FUNCTION_TEST)
		return false;

	//_XDPRINTFSMP_("%s: hcall: uhcall_function=0x%08x, uhcall_buffer=0x%08x, uhcall_buffer_len=0x%08x\n", __func__,
	//		uhcall_function, uhcall_buffer, uhcall_buffer_len);

	//if(!va2pa((uint32_t)uhcall_buffer, &uhcall_buffer_paddr))
	//	return false;
	
	//uhctp = (uhcalltest_param_t *)uhcall_buffer_paddr;
	uhctp = (i2c_ioaccess_param_t *)i2c_ioaccess_buffer;

	return true;
}
