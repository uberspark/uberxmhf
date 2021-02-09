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

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uhcalltest.h>
//#include <uberspark/include/uberspark.h>

#define MAX_LVL1_ENTRIES	4096
#define MAX_LVL2_ENTRIES	256

#define SIZEOF_LVL1_ENTRY_MAP	(1024*1024)	//each lvl1 entry maps to 1MB of memory
#define SIZEOF_LVL2_ENTRY_MAP	(1024*1024)	//each lvl1 entry maps to 1MB of memory

/*
uint32_t va2pa(uint32_t va){
	u32 ttbcr;
	u32 ttbr0;
	u32 ttbr1;
	u32 pdbr;
	u32 *lvl1tbl;	//4096 entries
	u32 i;
	u32 lvl1tbl_index;
	u32 lvl2tbl_index;
	u32 lvl1tbl_entry;
	u32 lvl2tbl_entry;
	u32 *lvl2tbl;

	_XDPRINTFSMP_("%s: ENTER: va=0x%08x\n", __func__, va);

	ttbcr = sysreg_read_ttbcr();
	_XDPRINTFSMP_("%s: ttbcr=0x%08x\n", __func__, ttbcr);

	ttbr0 = sysreg_read_ttbr0();
	_XDPRINTFSMP_("%s: ttbr0=0x%08x\n", __func__, ttbr0);

	ttbr1 = sysreg_read_ttbr1();
	_XDPRINTFSMP_("%s: ttbr1=0x%08x\n", __func__, ttbr1);


	pdbr = ttbr0 & 0xFFFFFF80UL;	//strip lower 7 bits
	_XDPRINTFSMP_("%s: pdbr=0x%08x\n", __func__, pdbr);

	lvl1tbl_index = va/SIZEOF_LVL1_ENTRY_MAP;
	lvl2tbl_index = (va % SIZEOF_LVL1_ENTRY_MAP) / 4096;

	lvl1tbl = (u32 *)pdbr;

	_XDPRINTFSMP_("%s: lvl1tbl=0x%08x\n", __func__, lvl1tbl);

	lvl1tbl_entry = lvl1tbl[lvl1tbl_index];

	_XDPRINTFSMP_("%s: lvl1tbl_index=%u, lvl1tbl entry=0x%08x\n", __func__,
			lvl1tbl_index, lvl1tbl_entry);

	if( (lvl1tbl_entry & 0x00000003UL) != 0x1){
		_XDPRINTFSMP_("%s: unhandled lvl1tbl_entry. Halting!\n", __func__);
		HALT();
	}

	lvl2tbl = (u32 *) (u32)( lvl1tbl_entry & 0xFFFFFE00UL);

	_XDPRINTFSMP_("%s: lvl2tbl=0x%08x\n", __func__, lvl2tbl);

	lvl2tbl_entry = lvl2tbl[lvl2tbl_index];

	_XDPRINTFSMP_("%s: lvl2tbl_index=%u, lvl2tbl entry=0x%08x\n", __func__,
			lvl2tbl_index, lvl2tbl_entry);

	_XDPRINTFSMP_("%s: WiP\n", __func__);
}
*/


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



//return true if handled the hypercall, false if not
bool uapp_uhcalltest_handlehcall(u32 uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len){
	uhcalltest_param_t *uhctp;
	uint32_t i;
	//u32 uhcall_buffer_paddr;

	if(uhcall_function != UAPP_UHCALLTEST_FUNCTION_TEST)
		return false;

	//_XDPRINTFSMP_("%s: hcall: uhcall_function=0x%08x, uhcall_buffer=0x%08x, uhcall_buffer_len=0x%08x\n", __func__,
	//		uhcall_function, uhcall_buffer, uhcall_buffer_len);

	//if(!va2pa((uint32_t)uhcall_buffer, &uhcall_buffer_paddr))
	//	return false;
	
	//uhctp = (uhcalltest_param_t *)uhcall_buffer_paddr;
	uhctp = (uhcalltest_param_t *)uhcall_buffer;

#if 1
   _XDPRINTFSMP_("dumping in[]...\n");
   for(i=0; i < 16; i++)
	   _XDPRINTFSMP_("%c", uhctp->in[i]);
   _XDPRINTFSMP_("\ndumped uhctp->in[]\n");
#endif

   uberspark_uobjrtl_crt__memcpy(&uhctp->out, &uhctp->in, 16);

#if 1
   _XDPRINTFSMP_("dumping out[]...\n");
   for(i=0; i < 16; i++)
	   _XDPRINTFSMP_("%c", uhctp->out[i]);
   _XDPRINTFSMP_("\ndumped uhctp->out[]\n");
#endif

	return true;
}
