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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_exhub.h>

//initialize IDT
/*@
	assigns xcexhub_idt_data[0..(EMHF_XCPHANDLER_MAXEXCEPTIONS-1)].isrLow;
	assigns xcexhub_idt_data[0..(EMHF_XCPHANDLER_MAXEXCEPTIONS-1)].isrHigh;
	assigns xcexhub_idt_data[0..(EMHF_XCPHANDLER_MAXEXCEPTIONS-1)].isrSelector;
	assigns xcexhub_idt_data[0..(EMHF_XCPHANDLER_MAXEXCEPTIONS-1)].count;
	assigns xcexhub_idt_data[0..(EMHF_XCPHANDLER_MAXEXCEPTIONS-1)].type;
	ensures \forall integer x; 0 <= x < (EMHF_XCPHANDLER_MAXEXCEPTIONS-1) ==> (xcexhub_idt_data[x].type == 0xEE);
	ensures \forall integer x; 0 <= x < (EMHF_XCPHANDLER_MAXEXCEPTIONS-1) ==> (xcexhub_idt_data[x].count == 0x0);
	ensures \forall integer x; 0 <= x < (EMHF_XCPHANDLER_MAXEXCEPTIONS-1) ==> (xcexhub_idt_data[x].isrSelector == __CS_CPL0);
	ensures \forall integer x; 0 <= x < (EMHF_XCPHANDLER_MAXEXCEPTIONS-1) ==> (xcexhub_idt_data[x].isrHigh == (uint16_t) ((uint32_t)xcexhub_excp_handlers[x] >> 16));
	ensures \forall integer x; 0 <= x < (EMHF_XCPHANDLER_MAXEXCEPTIONS-1) ==> (xcexhub_idt_data[x].isrLow == (uint16_t) xcexhub_excp_handlers[x]);
@*/
void xcexhub_setupidt(void){
	uint32_t i;


    	/*@
		loop invariant a1: 0 <= i <= EMHF_XCPHANDLER_MAXEXCEPTIONS;
		loop invariant a2: \forall integer x; 0 <= x < i ==> (xcexhub_idt_data[x].type == 0xEE);
		loop invariant a3: \forall integer x; 0 <= x < i ==> (xcexhub_idt_data[x].count == 0x0);
		loop invariant a4: \forall integer x; 0 <= x < i ==> (xcexhub_idt_data[x].isrSelector == __CS_CPL0);
		loop invariant a5: \forall integer x; 0 <= x < i ==> (xcexhub_idt_data[x].isrHigh == (uint16_t) ((uint32_t)xcexhub_excp_handlers[i] >> 16) );
		loop invariant a6: \forall integer x; 0 <= x < i ==> (xcexhub_idt_data[x].isrLow == (uint16_t) xcexhub_excp_handlers[i]);
		loop assigns xcexhub_idt_data[0..(EMHF_XCPHANDLER_MAXEXCEPTIONS-1)].isrLow;
		loop assigns xcexhub_idt_data[0..(EMHF_XCPHANDLER_MAXEXCEPTIONS-1)].isrHigh;
		loop assigns xcexhub_idt_data[0..(EMHF_XCPHANDLER_MAXEXCEPTIONS-1)].isrSelector;
		loop assigns xcexhub_idt_data[0..(EMHF_XCPHANDLER_MAXEXCEPTIONS-1)].count;
		loop assigns xcexhub_idt_data[0..(EMHF_XCPHANDLER_MAXEXCEPTIONS-1)].type;
		loop assigns i;
		loop variant EMHF_XCPHANDLER_MAXEXCEPTIONS - i;
	@*/
	for(i=0; i < EMHF_XCPHANDLER_MAXEXCEPTIONS; i++){
		xcexhub_idt_data[i].isrLow= (uint16_t)xcexhub_excp_handlers[i];
		xcexhub_idt_data[i].isrHigh= (uint16_t)((uint32_t)xcexhub_excp_handlers[i] >> 16);
		xcexhub_idt_data[i].isrSelector = __CS_CPL0;
		xcexhub_idt_data[i].count=0x0;
		xcexhub_idt_data[i].type=0xEE;	//32-bit interrupt gate
					//present=1, DPL=11b, system=0, type=1110b

	}
}

