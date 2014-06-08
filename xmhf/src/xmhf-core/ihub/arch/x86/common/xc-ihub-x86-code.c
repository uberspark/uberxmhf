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
 * XMHF ihub slab (x86 arch. backend)
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-core.h>
#include <xc-x86.h>

/* originally in xc-ihub-apihub-x86.c */

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
	"call xmhf_apihub_fromhypapp \r\n"						//invoke C land core API hub handler
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
				: "esi", "edx", "eax", "ecx"
		);

}



/* originally in xc-ihub-xcphandler-x86.c */

static void xmhf_xcphandler_arch_unhandled(u32 vector, struct regs *r){
	u32 exception_cs, exception_eip, exception_eflags, errorcode=0;

	if(vector == CPU_EXCEPTION_DF ||
		vector == CPU_EXCEPTION_TS ||
		vector == CPU_EXCEPTION_NP ||
		vector == CPU_EXCEPTION_SS ||
		vector == CPU_EXCEPTION_GP ||
		vector == CPU_EXCEPTION_PF ||
		vector == CPU_EXCEPTION_AC){
		errorcode = *(uint32_t *)(r->esp+0);
		r->esp += sizeof(uint32_t);	//skip error code on stack if applicable
	}

	exception_eip = *(uint32_t *)(r->esp+0);
	exception_cs = *(uint32_t *)(r->esp+sizeof(uint32_t));
	exception_eflags = *(uint32_t *)(r->esp+(2*sizeof(uint32_t)));

	printf("\nunhandled exception %x, halting!", vector);
	printf("\nstate dump follows...");
	//things to dump
	printf("\nCS:EIP 0x%04x:0x%08x with EFLAGS=0x%08x, errorcode=%08x", (u16)exception_cs, exception_eip, exception_eflags, errorcode);
	printf("\nCR0=%08x, CR2=%08x, CR3=%08x, CR4=%08x", read_cr0(), read_cr2(), read_cr3(), read_cr4());
	printf("\nEAX=0x%08x EBX=0x%08x ECX=0x%08x EDX=0x%08x", r->eax, r->ebx, r->ecx, r->edx);
	printf("\nESI=0x%08x EDI=0x%08x EBP=0x%08x ESP=0x%08x", r->esi, r->edi, r->ebp, r->esp);
	printf("\nCS=0x%04x, DS=0x%04x, ES=0x%04x, SS=0x%04x", (u16)read_segreg_cs(), (u16)read_segreg_ds(), (u16)read_segreg_es(), (u16)read_segreg_ss());
	printf("\nFS=0x%04x, GS=0x%04x", (u16)read_segreg_fs(), (u16)read_segreg_gs());
	printf("\nTR=0x%04x", (u16)read_tr_sel());

	//do a stack dump in the hopes of getting more info.
	{
		uint32_t i;
		uint32_t stack_start = r->esp;
		printf("\n-----stack dump (16 entries)-----");
		for(i=stack_start; i < stack_start+(16*sizeof(uint32_t)); i+=sizeof(uint32_t)){
			printf("\nStack(0x%08x) -> 0x%08x", i, *(uint32_t *)i);
		}
		printf("\n-----end------------");
	}
	HALT();
}

//exception handler hub
void xmhf_xcphandler_arch_hub(u32 vector, struct regs *r){
	switch(vector){
			case CPU_EXCEPTION_NMI:{
				xmhf_smpguest_arch_eventhandler_nmiexception(r);
				}
				break;

			default:{
				xmhf_xcphandler_arch_unhandled(vector, r);
				//we will never get here
			}
	}
}
