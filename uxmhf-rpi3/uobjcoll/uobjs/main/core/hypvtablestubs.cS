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
	HYP mode verctor table and stubs

	author: amit vasudevan (amitvasudevan@acm.org), ethan joseph (ethanj217@gmail.com)
*/

#include <uberspark/include/uberspark.h>
#include <uberspark/hwm/include/arch/arm/hwm.h>

/*
	G1.12.1 (Table G1-6 ARMv8)
	HYP vector table format:
	offsets:
		0x0: 	not used
		0x4: 	undefined instruction form HYP mode
		0x8: 	HVC in HYP mode
		0x0C:	prefetch abort from HYP mode
		0x10: 	data abort from HYP mode
		0x14:	HVC in non-HYP mode
		0x18:	IRQ
		0x1C:	FIQ
*/

/* need lower 5 bits (0-4) of the table address as 0, so use balign 32 */
CASM_FUNCDEF(void, g_hypvtable,
{
	//cpu-0
	__casm__b(hypvtable_reserved_handler0);
	__casm__b(hypvtable_reserved_handler0);
	__casm__b(hypvtable_reserved_handler0);
	__casm__b(hypvtable_reserved_handler0);
	__casm__b(hypvtable_reserved_handler0);
	__casm__b(hypvtable_hypsvc_handler0);
	__casm__b(hypvtable_reserved_handler0);
	__casm__b(hypvtable_reserved_handler0);
	//cpu-1
	__casm__b(hypvtable_reserved_handler1);
	__casm__b(hypvtable_reserved_handler1);
	__casm__b(hypvtable_reserved_handler1);
	__casm__b(hypvtable_reserved_handler1);
	__casm__b(hypvtable_reserved_handler1);
	__casm__b(hypvtable_hypsvc_handler1);
	__casm__b(hypvtable_reserved_handler1);
	__casm__b(hypvtable_reserved_handler1);
	//cpu-2
	__casm__b(hypvtable_reserved_handler2);
	__casm__b(hypvtable_reserved_handler2);
	__casm__b(hypvtable_reserved_handler2);
	__casm__b(hypvtable_reserved_handler2);
	__casm__b(hypvtable_reserved_handler2);
	__casm__b(hypvtable_hypsvc_handler2);
	__casm__b(hypvtable_reserved_handler2);
	__casm__b(hypvtable_reserved_handler2);
	//cpu-3
	__casm__b(hypvtable_reserved_handler3);
	__casm__b(hypvtable_reserved_handler3);
	__casm__b(hypvtable_reserved_handler3);
	__casm__b(hypvtable_reserved_handler3);
	__casm__b(hypvtable_reserved_handler3);
	__casm__b(hypvtable_hypsvc_handler3);
	__casm__b(hypvtable_reserved_handler3);
	__casm__b(hypvtable_reserved_handler3);
})


	.balign 32
	.global	hypvtable_reserved_handler0
hypvtable_reserved_handler0:
	ldr sp, =hypvtable_rsvhandler_stack_top0
	bl hyp_rsvhandler
1:	b 1b


	.global	hypvtable_reserved_handler1
hypvtable_reserved_handler1:
	ldr sp, =hypvtable_rsvhandler_stack_top1
	bl hyp_rsvhandler
1:	b 1b

	.global	hypvtable_reserved_handler2
hypvtable_reserved_handler2:
	ldr sp, =hypvtable_rsvhandler_stack_top2
	bl hyp_rsvhandler
1:	b 1b

	.global	hypvtable_reserved_handler3
hypvtable_reserved_handler3:
	ldr sp, =hypvtable_rsvhandler_stack_top3
	bl hyp_rsvhandler
1:	b 1b




	.global	hypvtable_hypsvc_handler0
hypvtable_hypsvc_handler0:
	ldr sp, =hypvtable_hypsvc_stack_top0
	b hypvtable_hypsvc_handler_common

	.global	hypvtable_hypsvc_handler1
hypvtable_hypsvc_handler1:
	ldr sp, =hypvtable_hypsvc_stack_top1
	b hypvtable_hypsvc_handler_common

	.global	hypvtable_hypsvc_handler2
hypvtable_hypsvc_handler2:
	ldr sp, =hypvtable_hypsvc_stack_top2
	b hypvtable_hypsvc_handler_common

	.global	hypvtable_hypsvc_handler3
hypvtable_hypsvc_handler3:
	ldr sp, =hypvtable_hypsvc_stack_top3
	b hypvtable_hypsvc_handler_common







/*
	G1.12.3 ARMv8
	exception return address is stored in ELR_hyp register and
	points to the instruction *after* the HVC instruction (Table G1-9)
*/
CASM_FUNCDEF(void, hypvtable_hypsvc_handler_common,
{
	// G1.9.2 (Figure G1-3)
	// HYP mode uses LR_usr, i.e, does not have LR banking, so save
	// since we are going to be using LR for C calling
	__casm__push_lr(); 

	// save guest gprs
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

	// invoke C handler
	__casm__mov_r0_sp();
	__casm__bl(hypsvc_handler);

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

	//
	//	G1.13.1 ARMv8
	//	exception returns from HYP mode is made via ERET instruction
	//	which basically returns to ELR_hyp and restores appropriate
	//	PE (processor execution) state
	//

	__casm__eret();
})

// .section ".stack"
// 	.balign 8
// 	.global hypvtable_stack
// 	stack:	.space	8192
// 	.global hypvtable_stack_top
// 	hypvtable_stack_top:

// 	.balign 8
// 	.global hypvtable_hypsvc_stack0
// 	hypvtable_hypsvc_stack0:	.space	16384
// 	.global hypvtable_hypsvc_stack_top0
// 	hypvtable_hypsvc_stack_top0:

// 	.balign 8
// 	.global hypvtable_hypsvc_stack1
// 	hypvtable_hypsvc_stack1:	.space	16384
// 	.global hypvtable_hypsvc_stack_top1
// 	hypvtable_hypsvc_stack_top1:

// 	.balign 8
// 	.global hypvtable_hypsvc_stack2
// 	hypvtable_hypsvc_stack2:	.space	16384
// 	.global hypvtable_hypsvc_stack_top2
// 	hypvtable_hypsvc_stack_top2:

// 	.balign 8
// 	.global hypvtable_hypsvc_stack3
// 	hypvtable_hypsvc_stack3:	.space	16384
// 	.global hypvtable_hypsvc_stack_top3
// 	hypvtable_hypsvc_stack_top3:

// 	.balign 8
// 	.global hypvtable_rsvhandler_stack0
// 	hypvtable_rsvhandler_stack0:	.space	8192
// 	.global hypvtable_rsvhandler_stack_top0
// 	hypvtable_rsvhandler_stack_top0:

// 	.balign 8
// 	.global hypvtable_rsvhandler_stack1
// 	hypvtable_rsvhandler_stack1:	.space	8192
// 	.global hypvtable_rsvhandler_stack_top1
// 	hypvtable_rsvhandler_stack_top1:

// 	.balign 8
// 	.global hypvtable_rsvhandler_stack2
// 	hypvtable_rsvhandler_stack2:	.space	8192
// 	.global hypvtable_rsvhandler_stack_top2
// 	hypvtable_rsvhandler_stack_top2:

// 	.balign 8
// 	.global hypvtable_rsvhandler_stack3
// 	hypvtable_rsvhandler_stack3:	.space	8192
// 	.global hypvtable_rsvhandler_stack_top3
// 	hypvtable_rsvhandler_stack_top3:



