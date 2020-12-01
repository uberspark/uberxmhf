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

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <uart.h>
#include <atags.h>
#include <debug.h>

extern void call_core(u32 r0, u32 id, struct atag *at);

void bsmain(u32 r0, u32 id, struct atag *at){
	u32 hsctlr, cpsr;

	//uart_init();

	//uart_puts("uXMHF-rpi3: bootstrap: Hello World!\n");

	cpsr = sysreg_read_cpsr();
	//uart_puts(" CPSR[mode]= ");
	//debug_hexdumpu32((cpsr & 0xF));

	if(! ((cpsr & 0xF) == 0xA) ){
		//uart_puts("uXMHF-rpi3: core: not in HYP mode. Halting!\n");
		HALT();
	}


	hsctlr = sysreg_read_hsctlr();
	//uart_puts(" HSCTLR before= ");
	//debug_hexdumpu32(hsctlr);

	hsctlr |= (1 << 12);	//enable instruction caching
	hsctlr |= (1 << 2);		//enable data caching

	sysreg_write_hsctlr(hsctlr);

	//hsctlr = sysreg_read_hsctlr();
	//uart_puts(" HSCTLR after= ");
	//debug_hexdumpu32(hsctlr);

	//uart_puts(" r0= ");
	//debug_hexdumpu32(r0);
	//uart_puts(" id= ");
	//debug_hexdumpu32(id);
	//uart_puts(" ATAGS= ");
	//debug_hexdumpu32(at);
	//uart_puts("uXMHF-rpi3: bootstrap: passing control to core...\n");

	//uart_flush();
	call_core(r0, id, at);
}
