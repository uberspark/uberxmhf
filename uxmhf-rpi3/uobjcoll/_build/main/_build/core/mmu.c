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
	ARM 8 MMU functions
	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/debug.h>
//#include <uberspark/include/uberspark.h>

void mmu_invalidatetlbs(void){
	//invalidate all TLB
	sysreg_tlbiallh();
}

void mmu_invalidateicache(void){
	//invalidate instruction caches
	sysreg_iciallu();
}

//enable instruction caching
void mmu_enableicache(void){
	u32 hsctlr;

	hsctlr = sysreg_read_hsctlr();
	hsctlr |= (1 << 12);	//enable instruction caching
	sysreg_write_hsctlr(hsctlr);
}

//enable data caching
void mmu_enabledcache(void){
	u32 hsctlr;

	hsctlr = sysreg_read_hsctlr();
	hsctlr |= (1 << 2);		//enable data caching
	sysreg_write_hsctlr(hsctlr);
}

//disable instruction caching
void mmu_disableicache(void){
	u32 hsctlr;

	hsctlr = sysreg_read_hsctlr();
	hsctlr &= ~(1 << 12);	//disable instruction caching
	sysreg_write_hsctlr(hsctlr);
}

//disable data caching
void mmu_disabledcache(void){
	u32 hsctlr;

	hsctlr = sysreg_read_hsctlr();
	hsctlr &= ~(1 << 2);		//disable data caching
	sysreg_write_hsctlr(hsctlr);
}


//activate MMU translation
void mmu_activatetranslation(void){
	u32 hsctlr;

	hsctlr = sysreg_read_hsctlr();
	_XDPRINTF_("%s: HSCTLR before=0x%08x\n", __func__, hsctlr);

	hsctlr |= HSCTLR_M_MASK;
	hsctlr |= (1 << 2);		//enable data caching
	hsctlr |= (1 << 12);	//enable instruction caching

	sysreg_write_hsctlr(hsctlr);

	hsctlr = sysreg_read_hsctlr();
	_XDPRINTF_("%s: HSCTLR after=0x%08x\n", __func__, hsctlr);
}

