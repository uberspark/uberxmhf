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

#include <xmhf.h>
#include <xmhf-core.h>

//core/hypapp API/callbacks low-level stubs
//author: amit vasudevan (amitvasudevan@acm.org)

extern void libxmhfcore_hypappfromcore(u32 callnum);

/*//----------------------------------------------------------------------
//globals referenced
	.extern libxmhfcore_hypappfromcore

//----------------------------------------------------------------------
// code
// 

.section .text


.global libxmhfcore_hypappfromcore_stub
libxmhfcore_hypappfromcore_stub:
	pushl %esi
	call libxmhfcore_hypappfromcore
	addl $0x04, %esp
	
	movl $(XMHF_APIHUB_COREAPI_HYPAPPCBRETURN), %esi	//signal a return from hypapp callback
	sysenter
	
	int $0x03			//never get here
	hlt
*/
__attribute__((naked)) void libxmhfcore_hypappfromcore_stub(void) {

	asm volatile(
		"pushl %%esi \r\n"
		"call libxmhfcore_hypappfromcore \r\n"
		"addl $0x04, %%esp \r\n"
		"movl %0, %%esi \r\n"	//signal a return from hypapp callback
		"sysenter \r\n"
		"int $0x03 \r\n"		//never get here
		"hlt \r\n"
		: //no outputs
		: "i" (XMHF_APIHUB_COREAPI_HYPAPPCBRETURN)
		: //no clobber
	);

}


void libxmhfcore_hypapptocore(u32 callnum){

	asm volatile(
			"pushl 	%%ecx \r\n"										//save GPRs we will clobber
			"pushl 	%%edx \r\n"
			"pushl	%%esi \r\n"
			"movl 	%%esp, %%ecx \r\n"									//store return ESP and EIP for sysexit
			"movl 	$backfromcore, %%edx \r\n"
			"movl  %0, %%esi \r\n"									//load core API call number
			"sysenter \r\n"											//go to the core
			"backfromcore:	\r\n"
			"popl	%%esi \r\n"										//restore GPRs we clobbered
			"popl	%%edx \r\n"
			"popl	%%ecx \r\n"
			//"ret \r\n"													//return back to the hypap
			: // no outputs
			: "m" (callnum)
			: //no clobber
	);

}

/*
.global libxmhfcore_hypapptocore
libxmhfcore_hypapptocore:
	pushl 	%ecx										//save GPRs we will clobber
	pushl 	%edx
	pushl	%esi
	
	movl 	%esp, %ecx									//store return ESP and EIP for sysexit
	movl 	$backfromcore, %edx
	
	movl 16(%esp), %esi									//load core API call number
	sysenter											//go to the core

backfromcore:	
	
	popl	%esi										//restore GPRs we clobbered
	popl	%edx
	popl	%ecx
	
	ret													//return back to the hypap
	

//----------------------------------------------------------------------
// data
// 

.section .data

//----------------------------------------------------------------------
// stack
// 

.section .stack

*/
