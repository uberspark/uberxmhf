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


/*
 * 	 
 *  XMHF core API interface component low-level trampolines
 * 
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */

void xmhf_apihub_arch_fromhypapp_stub(void);
extern u32 hypapp_cbhub_pc;
extern u32 hypapp_tos;
extern u32 core_ptba;
extern u32 hypapp_ptba;


//__attribute__((naked)) void xmhf_apihub_arch_tohypapp_wip(u32 hypappcallnum){
void xmhf_apihub_arch_tohypapp(u32 hypappcallnum){

asm volatile ( 	"pushal	\r\n"							//save all GPRs
				"pushl $backfromhypapp \r\n"			//push return EIP on top of stack
				"movl %0, %%esi \r\n"					//esi = hypappcallnum
				"movl $0x0, %%edx \r\n"					//store SYSENTER CS  
				"movl %1, %%eax \r\n"
				"movl %2, %%ecx \r\n"
				"wrmsr \r\n"
				"movl $0x0, %%edx \r\n"					//store SYSENTER ESP 
				"movl %%esp, %%eax \r\n"
				"movl %3, %%ecx \r\n"
				"wrmsr \r\n"
				"movl $0x0, %%edx \r\n"					//store SYSENTER EIP
				"movl %4, %%eax \r\n"			
				"movl %5, %%ecx \r\n"
				"wrmsr \r\n"
				"movl %6, %%ecx \r\n"					//store SYSEXIT ESP
				"movl %7, %%edx \r\n"					//store SYSEXIT EIP
				"movl %8, %%eax \r\n"					//load hypapp page tables
				"movl %%eax, %%cr3 \r\n"			
				"movw %9,  %%ax \r\n"			//load hypapp DS segment selector
				"movw %%ax, %%ds \r\n"					//SS and CS loaded by sysexit below
				"sysexit \r\n"							//invoke hypapp callback*/
				"backfromhypapp: \r\n"
				"popal \r\n"							// restore all GPRs
				:	//no outputs
				: "m" (hypappcallnum), "i" (__CS_CPL0), "i" (IA32_SYSENTER_CS_MSR), "i" (IA32_SYSENTER_ESP_MSR), "i" (&xmhf_apihub_arch_fromhypapp_stub), 
					"i" (IA32_SYSENTER_EIP_MSR), "m" (hypapp_tos), "m" (hypapp_cbhub_pc), "m" (hypapp_ptba), "i" (__DS_CPL3)
				:   //no clobber list
		);

}

__attribute__((naked)) void xmhf_apihub_arch_fromhypapp_stub(void){

asm volatile(
	"cmpl %0, %%esi\r\n"		//check if it is return from hyppapp callback
	"jne coreapicall \r\n"										//if not continue below to return from hypapp callback
	"movl %1, %%eax \r\n"									//load core page tables
	"movl %%eax, %%cr3 \r\n"			
	"movw %2, %%ax \r\n"								//switch to ring-0 DS
	"movw	%%ax, %%ds \r\n"
	"ret \r\n"													// this will pop the return EIP from top of stack and resume execution at backfromhypapp above
	"int $0x03 \r\n"											// we should never get here
	"hlt \r\n"
	"coreapicall: \r\n"											//this is a regular core API call
	"pushal \r\n"												//save all GPRs
	"movl %3, %%eax \r\n"									//load core page tables
	"movl %%eax, %%cr3 \r\n"			
	"movw %4, %%ax \r\n"								//switch to ring-0 DS
	"movw	%%ax, %%ds \r\n"
	"pushl	%%esi \r\n"
	"call xmhf_apihub_arch_fromhypapp \r\n"						//invoke C land core API hub handler
	"addl $0x4, %%esp \r\n"
	"movw %5, %%ax \r\n"								//load hypapp DS segment selector
	"movw %%ax, %%ds \r\n"										//SS and CS loaded by sysexit below
	"movl %6, %%eax \r\n"								//load hypapp page tables
	"movl %%eax, %%cr3 \r\n"			
	"popal \r\n"												//restore all GPRS
	"sysexit \r\n"												//exit back to hypapp
	"int $0x03 \r\n"
	"hlt \r\n"
	
		: //no outputs
		: "i" (XMHF_APIHUB_COREAPI_HYPAPPCBRETURN), "m" (core_ptba), "i" (__DS_CPL0), "m" (core_ptba), "i" (__DS_CPL0), "i" (__DS_CPL3), "m" (hypapp_ptba)
		: //no clobber list

);


}
