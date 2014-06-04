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

// XMHF slab import library decls./defns.
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHF_SLAB_IMPLIB_H__
#define __XMHF_SLAB_IMPLIB_H__

#ifndef __ASSEMBLY__
extern slab_table_t _slab_table[];

/*static inline void ignition(u32 destination_slab_index, u32 funcnum, u32 addrtos) __attribute__((always_inline)){
	//edi = address of parameters on stack
	////esi = return address
	
	asm volatile(
		"movl %0, %%edi \r\n"
		//"movl $retfromslab, %%esi \r\n"
		"movl %1, %%eax \r\n"
		"movl %2, %%ecx \r\n"
		"call *%%ecx \r\n"
		//"retfromslab:	\r\n"
		:	//outputs
		: "g" (addrtos), "g" (funcnum), "m" (_slab_table[destination_slab_index].slab_header.entry_cr3)	//inputs
		: "edi", "esi", "eax", "ecx" 	//clobber
	);

}*/

__attribute__((naked)) static inline void entry_0(void) __attribute__((noinline)){
	//setup
	//esi = base address of input parameter frame on stack (excluding return address)
	//edi = return address
	//ebx = function number
	//ecx = number of 32-bit dwords comprising the parameters (excluding return address)
	//we have eax, edx to play around with
		
	asm volatile(
		"pushl %%edi \r\n"				//save caller gprs
		"pushl %%esi \r\n"			
		"pushl %%ebp \r\n"
		"pushl %%ecx \r\n"
		"pushl %%ebx \r\n"
		
		"leal 24(%%esp), %%esi \r\n"	//setup esi
		"movl $1f, %%edi \r\n"			//setup edi
		"movl %0, %%ebx \r\n"			//setup ebx
		"movl %1, %%ecx \r\n"			//setup ecx
		"movl %2, %%eax \r\n"
		"movl %3, %%edx \r\n"			//setup edx
		"jmpl *%%eax \r\n"				//jump to destination slab interface
		
		"1: \r\n"						//destination slab returns here
		"popl %%ebx \r\n"				//restore caller gprs
		"popl %%ecx \r\n"
		"popl %%ebp \r\n"
		"popl %%esi \r\n"
		"popl %%edi \r\n"
		"ret \r\n"
		: //outputs
		: "i" (0), "i" (0), "m" (_slab_table[XMHF_SLAB_INDEX_TEMPLATE].slab_header.entry_cr3), "i" (0)	//inputs
		: 
	);

}


//static inline void entry(void) __attribute__((noinline)){
__attribute__ ((naked)) static inline u32 entry_1(u32 param1, u32 param2) __attribute__((noinline)){
	//setup
	//esi = base address of input parameter frame on stack (excluding return address)
	//edi = return address
	//ebx = function number
	//ecx = number of 32-bit dwords comprising the parameters (excluding return address)
	//we have eax, edx to play around with
		
	asm volatile(
		"pushl %%edi \r\n"				//save caller gprs
		"pushl %%esi \r\n"			
		"pushl %%ebp \r\n"
		"pushl %%ecx \r\n"
		"pushl %%ebx \r\n"
		
		"leal 24(%%esp), %%esi \r\n"	//setup esi
		"movl $1f, %%edi \r\n"			//setup edi
		"movl %0, %%ebx \r\n"			//setup ebx
		"movl %1, %%ecx \r\n"			//setup ecx
		"movl %2, %%eax \r\n"
		"movl %3, %%edx \r\n"			//setup edx
		"jmpl *%%eax \r\n"				//jump to destination slab interface
				
		"1: \r\n"						//destination slab returns here
		"popl %%ebx \r\n"				//restore caller gprs
		"popl %%ecx \r\n"
		"popl %%ebp \r\n"
		"popl %%esi \r\n"
		"popl %%edi \r\n"
		"ret \r\n"
		: //outputs
		: "i" (1), "i" ((sizeof(param1)+sizeof(param2))/sizeof(u32)), "m" (_slab_table[XMHF_SLAB_INDEX_TEMPLATE].slab_header.entry_cr3), "i" (0)
		: 
	);
}

__attribute__((naked)) static inline context_desc_t entry_2(u32 cpu_index, bool isbsp, u32 partition_index) __attribute__((noinline)){
	//setup
	//esi = base address of input parameter frame on stack (excluding return address)
	//edi = return address
	//ebx = function number
	//ecx = number of 32-bit dwords comprising the parameters (excluding return address)
	//edx = number of 32-bit dwords that will be automatically popped off the stack by the callee function
	//we have eax, edx to play around with
		
	asm volatile(
		"pushl %%edi \r\n"				//save caller gprs
		"pushl %%esi \r\n"			
		"pushl %%ebp \r\n"
		"pushl %%ecx \r\n"
		"pushl %%ebx \r\n"
		
		"leal 24(%%esp), %%esi \r\n"	//setup esi
		"movl $1f, %%edi \r\n"			//setup edi
		"movl %0, %%ebx \r\n"			//setup ebx
		"movl %1, %%ecx \r\n"			//setup ecx
		"movl %2, %%eax \r\n"
		"movl %3, %%edx \r\n"			//setup edx
		"jmpl *%%eax \r\n"				//jump to destination slab interface
				
		"1: \r\n"						//destination slab returns here
		"movl %3, %%ecx \r\n"
		"movl 24(%%esp), %%edi \r\n"
		"cld \r\n"
		"rep movsb \r\n"
		"popl %%ebx \r\n"				//restore caller gprs
		"popl %%ecx \r\n"
		"popl %%ebp \r\n"
		"popl %%esi \r\n"
		"popl %%edi \r\n"
		"ret $4 \r\n"
		: //"=a" (retval)
		: "i" (2), "i" (((sizeof(cpu_index)+sizeof(isbsp)+sizeof(partition_index))/sizeof(u32)) + sizeof(u32)), "m" (_slab_table[XMHF_SLAB_INDEX_TEMPLATE].slab_header.entry_cr3), "i" (sizeof(context_desc_t))	//inputs
		: 
	);

}


#endif //__ASSEMBLY__

#endif //__XMHF_SLAB_IMPLIB__
