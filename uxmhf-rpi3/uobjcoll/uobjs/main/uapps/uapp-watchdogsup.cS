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
	uapp watchdog low-level support routines

	author: amit vasudevan (amitvasudevan@acm.org), ethan joseph (ethanj217@gmail.com)
*/

#include <uberspark/include/uberspark.h>
#include <uberspark/hwm/include/arch/arm/hwm.h>

CASM_FUNCDEF(void, uapp_watchdog_fiq_handler,
{
	CASM_BALIGN(32);
	__casm__ldr_pseudo_sp(uapp_watchdog_fiqhandler_stack);
	__casm__push_lr(); 
	__casm__push_r12(); 
	__casm__push_r11(); 
	__casm__push_r10(); 
	__casm__push_r9(); 
	__casm__push_r8(); 
	__casm__push_r7(); 
	__casm__push_r6(); 
	__casm__push_r5(); 
	__casm__push_r4(); 
	__casm__push_r3(); 
	__casm__push_r2(); 
	__casm__push_r1(); 
	__casm__push_r0();

	__casm__bl(uapp_watchdog_fiqhandler);

	// restore all saved registers
	__casm__pop_r0();
 	__casm__pop_r1();
 	__casm__pop_r2();
 	__casm__pop_r3();
 	__casm__pop_r4();
 	__casm__pop_r5();
 	__casm__pop_r6();
 	__casm__pop_r7();
 	__casm__pop_r8();
 	__casm__pop_r9();
 	__casm__pop_r10();
 	__casm__pop_r11();
 	__casm__pop_r12();
  	__casm__pop_lr();

	__casm__eret();
}, void *noparam)


__attribute__((section(".stack"))) __attribute__((aligned(8))) uapp_watchdog_fiqhandler_stack[8192];
// 	.global uapp_watchdog_fiqhandler_stack_top
// 	uapp_watchdog_fiqhandler_stack_top: