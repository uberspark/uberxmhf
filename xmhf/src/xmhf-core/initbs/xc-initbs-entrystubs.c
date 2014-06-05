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

#include <xmhf-core.h>

/*
 * slab entry stubs
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
 
__attribute__((naked)) void entry_cr3(void){
	//setup
	//esi = base address of input parameter frame on stack (excluding return address)
	//edi = return address
	//ebx = function number
	//ecx = number of 32-bit dwords comprising the parameters (excluding return address)
	//we have eax, edx to play around with

	asm volatile (
			"pushl %%edi \r\n" 				//save return address
			
			"xorl %%ebp, %%ebp \r\n"			//ebp = 0
			"cmpl $0, %%edx \r\n"
			"je 1f \r\n"					//check to see if we need to allocate space for aggregate return value, if not just proceed
			"movl %%edx, %%ebp \r\n"		//
			//"shl $2, %%ebp \r\n"			//ebp = number of bytes that we need to allocate for aggregate return value
			"movl %%esp, %%edx \r\n"		//
			"subl %%ebp, %%edx \r\n"		//edx = address where aggregate return value begins on stack
			"1:\r\n"
			//"shl $2, %%ecx \r\n"			//ecx = number of bytes occupied by input parameters
			"addl %%ecx, %%ebp \r\n"		//ebp = total bytes that we need to allocate for aggregate return value + input parameters
			//"shr $2, %%ecx \r\n"			//ecx = number of dwords occupied by input parameters
			"subl %%ebp, %%esp 	\r\n"		//esp = new empty tos to house input parameters
			"movl %%esp, %%edi \r\n"		//edi = esp
			"cld \r\n"
			//"rep movsl \r\n"				//copy parameters 
			"rep movsb \r\n"
			"cmpl $0, %%edx \r\n"
			"je 1f \r\n"
			"addl $4, %%esp \r\n"			//pop out old aggregate return value address
			"pushl %%edx \r\n"				//store local aggregate return value address
			"movl %%edx, %%esi \r\n"
			
			"1:\r\n"
			"cmpl $0x0, %%ebx \r\n"			//check for correct function number
			"jne 1f \r\n"
			"call entry_0 \r\n"				//call function
			"jmp endswitch \r\n"
			
			"1:\r\n"
			"cmpl $0x1, %%ebx \r\n"			//check for correct function number
			"jne 1f \r\n"
			"call entry_1 \r\n"				//call function
			"jmp endswitch \r\n"

			"1:\r\n"
			"cmpl $0x2, %%ebx \r\n"			//check for correct function number
			"jne 1f \r\n"
			"call entry_2 \r\n"				//call function
			"subl $4, %%ebp \r\n"
			"jmp endswitch \r\n"

			"1:\r\n"
			"cmpl $0x3, %%ebx \r\n"			//check for correct function number
			"jne 1f \r\n"
			"call entry_3 \r\n"				//call function
			"subl $4, %%ebp \r\n"
			"jmp endswitch \r\n"
			
			"1:\r\n"
			"endswitch:\r\n"
			"addl %%ebp, %%esp \r\n"		//remove parameters from stack
			"popl %%edi \r\n"
			"jmpl *%%edi \r\n"				//return back to caller slab
			:
			:
			:
		);
}


