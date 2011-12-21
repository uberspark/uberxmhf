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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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
 
#include <emhf.h>

.altmacro
.macro XtRtmEmitIdtStub vector
	.section .text
	XtRtmIdtStub&vector&:
		pushl	%edi	
    pushl	%esi	
	  pushl	%ebp	
		pushl	%esp  
    pushl	%ebx	
    pushl	%edx	
    pushl	%ecx	
    pushl	%eax	
    
    movw	$(__DS), %ax
		movw	%ax, %ds	
		movl %esp, %eax
		
		pushl %eax
		pushl	$0x&vector&
		call	runtime_exception_handler
		addl  $0x08, %esp
		
		popl	%eax	
    popl	%ecx	
    popl	%edx	
    popl	%ebx	
		popl	%esp	
    popl	%ebp	
    popl	%esi	
    popl	%edi	 
    
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
	.fill	EMHF_XCPHANDLER_IDTSIZE, 1, 0
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

