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
	i2c-ioaccess uapp
	low-level i2c driver uapp (i2c-bcm2708) 
	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/debug.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/i2c-ioaccess.h>

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/i2c-ioaccess.h>

// this is from BCM ARM peripherals data-sheet and initial debugging
// of i2c-bcm2708 which seems to use this base. The data sheet talks about
// two more BSC master units at different addresses
// TBD: take this in via a hypercall that is called during kernel module
// initialization (presumably during ioremap)
#define I2C_BSC_BASE 0x3f804000

/* translate virtual address to physical address with offsets preserved */
bool uapp_va2pa_withoff(uint32_t va, u32 *pa){
  u32 par;
  u32 offset;

  CASM_FUNCCALL(sysreg_ats1cpr, va);
  par=CASM_FUNCCALL(sysreg_read_par, CASM_NOPARAM);

  if(par & 0x1)
    return false;

 offset = (u32)va & 0x00000FFFUL;
 par &= 0xFFFFF000UL;
 par |= offset;

   *pa = par;
  return true;
}


//return true if handled the hypercall, false if not
bool uapp_i2c_ioaccess_handle_fast_hcall(arm8_32_regs_t *r){
	uint32_t fn;
	uint32_t mmio_pa=0;
	
	fn = r->r0;	

	if(fn == UAPP_I2C_IOACCESS_WRITEL){
		//r->r1 = input addresss
		//r->r2 = input value
		//if(!uapp_va2pa_withoff(r->r1, &mmio_pa)){
			//error, this should not happen, print a message to serial debug and halt
		//	_XDPRINTFSMP_("%s: WRITEL: Error, could not translate va2pa. halting!\n", __func__);
		//	while(1);
		//}	

		mmio_pa = (u32)I2C_BSC_BASE | ((u32)r->r1 & 0x00000FFFUL);

		mmio_write32(mmio_pa, r->r2);
		return true;
	
	}else if(fn == UAPP_I2C_IOACCESS_READL){
		//r->r1 = input addresss
		//r->r2 = output value
	
		//#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_PL011__) || defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_MINI__)
	    //    //initialize uart
	  	//    uart_init();
		//#endif

		//_XDPRINTFSMP_("%s: coming in: r1(addr)=0x%08x, r2(value)=0x%08x\n", __func__,
		//	r->r1, r->r2);

		//if(!uapp_va2pa_withoff(r->r1, &mmio_pa)){
		//	//error, this should not happen, print a message to serial debug and halt
		//	_XDPRINTFSMP_("%s: READL: Error, could not translate va2pa. halting!\n", __func__);
		//	while(1);
		//}	

		//_XDPRINTFSMP_("%s: revised: r1(addr)=0x%08x, r2(value)=0x%08x\n", __func__,
		//	mmio_pa, r->r2);

		mmio_pa = (u32)I2C_BSC_BASE | ((u32)r->r1 & 0x00000FFFUL);

		r->r2 = mmio_read32(mmio_pa);

		//_XDPRINTFSMP_("%s: going out: r1(addr)=0x%08x, r2(value)=0x%08x\n", __func__,
		//	mmio_pa, r->r2);

		return true;
	
	}else 
		return false;
}
