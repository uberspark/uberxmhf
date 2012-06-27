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

/*
 * EMHF exception handler component low-level stubs
 */
 
#include <xmhf.h>
#include <xmhf-xcphandler.h>

.altmacro
.macro XtRtmEmitIdtStub vector
	.section .text
	
	//notes: 
	//1. we only handle exceptions (0-31) and nothing else
	//2. descriptor type for all exception handlers are 0x8E
	//   i.e., they are all interrupt gates, so when we get called
	//   EFLAGS.IF = 0 (interrupts disabled)
	//3. there are no stack switches as everything in the hypervisor
	//	 is CPL=0
	//4. stack layout is as follows when we enter
	//	 EFLAGS	(32-bits)
	//   CS		(32-bits)
	//	 EIP	(32-bits)
	//	 error-code (32-bits, depends on the exception)
	
	XtRtmIdtStub&vector&:
		
		//push GPR values on stack to construct a 
		//struct regs *r
		/*pushl	%edi	
		pushl	%esi	
		pushl	%ebp	
		pushl	%esp		
		pushl	%ebx	
		pushl	%edx	
		pushl	%ecx	
		pushl	%eax*/
		pushal	
    
		movw	$(__DS), %ax
		movw	%ax, %ds			//load DS
		movl 	%esp, %eax			//EAX = struct regs *
		
		pushl 	%eax				//struct regs *r
		pushl	$0x&vector&			//vector
		call	emhf_xcphandler_hub	//call C-land hub
		addl  	$0x08, %esp			//remove params from stack
		
		//restore GPRs
		/*popl	%eax	
		popl	%ecx	
		popl	%edx	
		popl	%ebx	
		popl	%esp	
		popl	%ebp	
		popl	%esi	
		popl	%edi*/
		popal	 
    
		//return from exception
		iretl
	
.endm

XtRtmEmitIdtStub 0	
XtRtmEmitIdtStub 1	
XtRtmEmitIdtStub 2	
XtRtmEmitIdtStub 3	
XtRtmEmitIdtStub 4	
XtRtmEmitIdtStub 5	
XtRtmEmitIdtStub 6	
XtRtmEmitIdtStub 7	
XtRtmEmitIdtStub 8	
XtRtmEmitIdtStub 9	
XtRtmEmitIdtStub a	
XtRtmEmitIdtStub b	
XtRtmEmitIdtStub c	
XtRtmEmitIdtStub d	
XtRtmEmitIdtStub e	
XtRtmEmitIdtStub f	
XtRtmEmitIdtStub 10	
XtRtmEmitIdtStub 11	
XtRtmEmitIdtStub 12	
XtRtmEmitIdtStub 13	
XtRtmEmitIdtStub 14	
XtRtmEmitIdtStub 15	
XtRtmEmitIdtStub 16	
XtRtmEmitIdtStub 17	
XtRtmEmitIdtStub 18	
XtRtmEmitIdtStub 19	
XtRtmEmitIdtStub 1a	
XtRtmEmitIdtStub 1b	
XtRtmEmitIdtStub 1c	
XtRtmEmitIdtStub 1d	
XtRtmEmitIdtStub 1e	
XtRtmEmitIdtStub 1f	


.section .data
	//EMHF interrupt descriptor table
	.global emhf_xcphandler_idt
	emhf_xcphandler_idt:
	.word emhf_xcphandler_idt_end - emhf_xcphandler_idt_start - 1
	.long emhf_xcphandler_idt_start
	.align 16
	.global emhf_xcphandler_idt_start
	emhf_xcphandler_idt_start:
	.fill	1024, 1, 0
	emhf_xcphandler_idt_end:


	.align 16
	.global emhf_xcphandler_exceptionstubs
	emhf_xcphandler_exceptionstubs:
	.long XtRtmIdtStub0
	.long XtRtmIdtStub1
	.long XtRtmIdtStub2
	.long XtRtmIdtStub3
	.long XtRtmIdtStub4
	.long XtRtmIdtStub5
	.long XtRtmIdtStub6
	.long XtRtmIdtStub7
	.long XtRtmIdtStub8
	.long XtRtmIdtStub9
	.long XtRtmIdtStuba
	.long XtRtmIdtStubb
	.long XtRtmIdtStubc
	.long XtRtmIdtStubd
	.long XtRtmIdtStube
	.long XtRtmIdtStubf
	.long XtRtmIdtStub10
	.long XtRtmIdtStub11
	.long XtRtmIdtStub12
	.long XtRtmIdtStub13
	.long XtRtmIdtStub14
	.long XtRtmIdtStub15
	.long XtRtmIdtStub16
	.long XtRtmIdtStub17
	.long XtRtmIdtStub18
	.long XtRtmIdtStub19
	.long XtRtmIdtStub1a
	.long XtRtmIdtStub1b
	.long XtRtmIdtStub1c
	.long XtRtmIdtStub1d
	.long XtRtmIdtStub1e
	.long XtRtmIdtStub1f
