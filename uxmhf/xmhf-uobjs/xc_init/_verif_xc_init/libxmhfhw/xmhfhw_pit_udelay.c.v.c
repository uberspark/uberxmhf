/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

// programmable interval timer (for micro second delay)
//author: amit vasudevan (amitvasudevan@acm.org)

#include <uberspark.h>
#include <xmhfhw.h>

//---microsecond delay----------------------------------------------------------
/*@
	assigns \nothing;
@*/
void xmhf_baseplatform_arch_x86_udelay(uint32_t usecs){
	uint8_t val, latchstatus=0;
	uint32_t latchregval;

	//enable 8254 ch-2 counter
	val = CASM_FUNCCALL(inb,0x61);
	val &= 0x0d; //turn PC speaker off
	val |= 0x01; //turn on ch-2
	CASM_FUNCCALL(outb,val, 0x61);

	//program ch-2 as one-shot
	CASM_FUNCCALL(outb,0xB0, 0x43);

	//compute appropriate latch register value depending on usecs
	//sanity check and cap usecs
	if(usecs > 0xD68461C0UL)
		usecs = 0xD68461C0UL;
	latchregval = (1193182 / 1000000) * usecs;

	//write latch register to ch-2
	val = (uint8_t)latchregval;
	CASM_FUNCCALL(outb,val, 0x42);
	val = (uint8_t)((uint32_t)latchregval >> (uint32_t)8);
	CASM_FUNCCALL(outb,val , 0x42);

	//while(!(inb(0x61) & 0x20));

	/*@
		loop invariant I3: latchstatus == 0;
		loop assigns latchstatus;
	@*/
	while(1){
		latchstatus = (inb(0x61) & 0x20);
		if(latchstatus)
			break;
	}

	//disable ch-2 counter
	val = CASM_FUNCCALL(inb,0x61);
	val &= 0x0c;
	CASM_FUNCCALL(outb,val, 0x61);
}

