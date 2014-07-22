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
 * slab trampoline that is mapped into every slab memory view
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-core.h>

// esi = 32-bit address of input parameter base
// edi = 32-bit address of return from slab call
// ebp = 32-bit address of destination slab entry point
// ecx = top 16-bits = size of result dwords
//		 bottom 16-bits = size of parameter dwords
// ebx = 32-bit function number
// eax = 32-bit src slab macmid
// edx = 32-bit dst slab macmid

__attribute__((naked)) __attribute (( section(".slabtrampoline") )) void _slab_trampoline(void){
	
	asm volatile(	
			"movl %%edx, %%cr3 \r\n"				//load callee MAC
			
			"pushl %%esi \r\n"						//save caller parameter base address
			"pushl %%eax \r\n"						//save caller MAC
			"pushl %%edi \r\n" 						//save caller return address
			"pushl %%ecx \r\n"						//save caller param/ret count
			
			"movl %%ebp, %%eax \r\n"				//eax= callee entry point
											
			"xorl %%ebp, %%ebp \r\n"				//zero out %ebp so we can use it to keep track of stack frame
			
			"xorl %%edx, %%edx \r\n"				//edx=0
			"movw %%cx, %%dx \r\n"					//edx=parameter dwords
			"shr $16, %%ecx \r\n"					//ecx=result dwords
						
			"cmpl $0, %%ecx \r\n"					//check if we are supporting aggregate return type for this slab call
			"je 1f \r\n"							//if no, then skip aggregate return type stack frame adjustment
			
			"movl %%ecx, %%ebp \r\n"				//ebp=result dwords
			"movl %%esp, %%ecx \r\n"				//ecx=top of stack
			"subl %%ebp, %%ecx \r\n"				//ecx=top of stack (32-bit address of aggregate return type bufffer)
			"addl $4, %%esi	\r\n"					//skip the caller aggregate return type buffer pointer on input parameter list
													//we will create a new stack frame for our return type buffer pointer
			"subl $4, %%edx \r\n"					//reduce parameter size by 1 dword to account for the aggregate return type buffer pointer
			
			"1:\r\n"						
			"addl %%edx, %%ebp \r\n"				//ebp=parameter + result dwords
			"subl %%ebp, %%esp 	\r\n"				//adjust top of stack to accomodate input parameters and aggregate return type buffer (if applicable)
			"movl %%esp, %%edi \r\n"				//edi=top of stack (with room made for input parameters)
			"cld \r\n"								//clear direction flag to copy forward
			"rep movsb \r\n"						//copy input parameters (at esi) to top of stack
			
			"cmpl $0, %%ecx \r\n"					//if we have aggregate return type then we need to push the aggregate return type buffer address
			"je 1f \r\n"							//if not, then invoke the callee slab entry point
			"pushl %%ecx \r\n"						//push our new return type buffer address that we have just made space for in our new call frame
			"movl %%ecx, %%esi \r\n"				//esi= 32-bit address of aggregate return type buffer which we will use to copy back return value
											
			"1: call *%%eax \r\n"					//invoke callee slab entry point
											
			"addl %%ebp, %%esp \r\n"				//discard callee stack frame that we created
			
			"popl %%ecx \r\n"						//restore caller MAC, return address and param/return size
			"popl %%edi \r\n"				
			"popl %%eax \r\n"
		
			"movl %%eax, %%cr3 \r\n"				//load caller MAC
			
			"movl %%edi, %%eax \r\n"				//eax=caller return address

			"popl %%edi \r\n"						//edi=caller parameter base address
			"movl (%%edi), %%edi \r\n"				//edi=caller aggregate return type buffer
			
			"shr $16, %%ecx \r\n"					//ecx=result dwords
			"cld \r\n"						
			"rep movsb \r\n"						//store aggregate return value (if any)
			
			"jmpl *%%eax \r\n"						//go back to caller
		: 
		: 
		:	 							
	);
	
	
}
