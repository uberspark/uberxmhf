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
	CASM_BALIGN(32);
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
}, void *noparam)

CASM_FUNCDEF(void, hypvtable_reserved_handler0,
{
	CASM_BALIGN(32);
	__casm__ldr_pseudo_sp(hypvtable_rsvhandler_stack0);
	__casm__bl(hyp_rsvhandler);
CASM_LABEL(1);
	__casm__b(1b);

}, void *noparam)

CASM_FUNCDEF(void, hypvtable_reserved_handler1,
{
	__casm__ldr_pseudo_sp(hypvtable_rsvhandler_stack1);
	__casm__bl(hyp_rsvhandler);
CASM_LABEL(1);
	__casm__b(1b);

}, void *noparam)

CASM_FUNCDEF(void, hypvtable_reserved_handler2,
{
	__casm__ldr_pseudo_sp(hypvtable_rsvhandler_stack2);
	__casm__bl(hyp_rsvhandler);
CASM_LABEL(1);
	__casm__b(1b);

}, void *noparam)

CASM_FUNCDEF(void, hypvtable_reserved_handler3,
{
	__casm__ldr_pseudo_sp(hypvtable_rsvhandler_stack3);
	__casm__bl(hyp_rsvhandler);
CASM_LABEL(1);
	__casm__b(1b);

}, void *noparam)


CASM_FUNCDEF(void, hypvtable_hypsvc_handler0,
{
	CASM_BALIGN(32);
	__casm__ldr_pseudo_sp(hypvtable_hypsvc_stack0);
	__casm__bl(hypvtable_hypsvc_handler_common);
CASM_LABEL(1);
	__casm__b(1b);

}, void *noparam)

CASM_FUNCDEF(void, hypvtable_hypsvc_handler1,
{
	CASM_BALIGN(32);
	__casm__ldr_pseudo_sp(hypvtable_hypsvc_stack1);
	__casm__bl(hypvtable_hypsvc_handler_common);
CASM_LABEL(1);
	__casm__b(1b);

}, void *noparam)

CASM_FUNCDEF(void, hypvtable_hypsvc_handler2,
{
	CASM_BALIGN(32);
	__casm__ldr_pseudo_sp(hypvtable_hypsvc_stack2);
	__casm__bl(hypvtable_hypsvc_handler_common);
CASM_LABEL(1);
	__casm__b(1b);

}, void *noparam)

CASM_FUNCDEF(void, hypvtable_hypsvc_handler3,
{
	CASM_BALIGN(32);
	__casm__ldr_pseudo_sp(hypvtable_hypsvc_stack3);
	__casm__bl(hypvtable_hypsvc_handler_common);
CASM_LABEL(1);
	__casm__b(1b);

}, void *noparam)


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
}, void *noparam)
