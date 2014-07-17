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
 * XMHF core exception handling slab
 * x86 arch. backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-core.h>
#include <xc-x86.h>
#include <xc-x86vmx.h>

#define __XMHF_SLAB_CALLER_INDEX__	XMHF_SLAB_XCEXHUB_INDEX
#include <xc-coreapi.h>
#undef __XMHF_SLAB_CALLER_INDEX__



//initialize IDT
void xmhf_baseplatform_arch_x86_initializeIDT(void){

	asm volatile(
		"lidt  %0 \r\n"
		: //no outputs
		: "m" (_idt)
		: //no clobber
	);
	
}

/* originally within xc-xcphandler-x86.c */

/*#define XMHF_EXCEPTION_HANDLER_DEFINE(vector) 												\
	static void __xmhf_exception_handler_##vector(void) __attribute__((naked)) { 					\
		asm volatile(	"pushal	\r\n"								\
						"movw	%0, %%ax\r\n"						\
						"movw	%%ax, %%ds\r\n"						\
						"movl 	%%esp, %%eax\r\n"					\
						"pushl 	%%eax\r\n"							\
						"pushl	%1\r\n" 							\
						"call	xmhf_xcphandler_arch_hub\r\n"			\
						"addl  	$0x08, %%esp\r\n"					\
						"popal	 \r\n"								\
						"iretl\r\n"									\
					:												\
					:	"i" (__DS_CPL0), "i" (vector)				\
		);															\
	}\
*/

__attribute__((section(".stack"))) static u32 _xcexhub_exception_lock = 1;
__attribute__((section(".stack"))) static u32 _xcexhub_exception_savedesp[MAX_PLATFORM_CPUS];
__attribute__((section(".stack"))) static u32 _xcexhub_exception_savedesp_index = &_xcexhub_exception_savedesp[0];
//__attribute__((section(".stack"))) static u32 _xcexhub_exception_savedcr3 = 0;
//exclusive exception handling stack, we switch to this stack if there
//are any exceptions during hypapp execution
__attribute__((section(".stack"))) __attribute__(( aligned(4096) )) static u8 _xcexhub_exception_stack[MAX_PLATFORM_CPUS][PAGE_SIZE_4K];
__attribute__((section(".stack"))) __attribute__(( aligned(4096) )) static u32 _xcexhub_exception_stack_index = &_xcexhub_exception_stack[1];


//XXX: TODO: we can't use a lock for the entire exception handling below since out current
//quiesce logic holds up every core within the NMI handler; this needs to be reentrant so
//we need to operate on core-specific save structures

#define XMHF_EXCEPTION_HANDLER_DEFINE(vector) 												\
	static void __xmhf_exception_handler_##vector(void) __attribute__((naked)) { 					\
		asm volatile(												\
						"1:	bt	$0, %0	\r\n"						\
						"jnc 1b	\r\n"								\
						"lock \r\n"   								\	
						"btrl	$0, %0	\r\n"						\	
						"jnc 1b \r\n"   							\
																	\
						"xchg %%esp, %1 \r\n"						\ 	
						"pushl %1 \r\n"								\	
						"pushal \r\n"								\
						"movl %%esp, %%eax \r\n"					\
						"addl $36, %%eax \r\n"						\	
						"addl $4096, %%eax \r\n"					\
						"movl %%eax, %1 \r\n"						\	
																	\
						"btsl	$0, %0		\r\n"					\
																	\
						"movl %%cr3, %%eax \r\n"					\
						"pushl %%eax \r\n"							\
																	\
						"movl %2, %%eax \r\n"						\
						"movl %%eax, %%cr3 \r\n"					\
																	\
						"movw	%3, %%ax\r\n"						\
						"movw	%%ax, %%ds\r\n"						\
						"movl 	%%esp, %%eax\r\n"					\
						"pushl 	%%eax\r\n"							\
						"pushl	%4\r\n" 							\
						"call	xmhf_xcphandler_arch_hub\r\n"		\
						"addl  	$0x08, %%esp\r\n"					\
																	\
						"popl %%eax \r\n"							\
						"movl %%eax, %%cr3 \r\n"					\
																	\
						"popal	 \r\n"								\
																	\
						"pop %%esp \r\n"							\
																	\
																	\
						"iretl\r\n"									\
					:												\
					:	"m" (_xcexhub_exception_lock), "m" (_xcexhub_exception_stack_index), "m" (_slab_table[XMHF_SLAB_XCEXHUB_INDEX].slab_macmid), "i" (__DS_CPL0), "i" (vector)				\
		);															\
	}\



#define XMHF_EXCEPTION_HANDLER_ADDROF(vector) &__xmhf_exception_handler_##vector

XMHF_EXCEPTION_HANDLER_DEFINE(0)
XMHF_EXCEPTION_HANDLER_DEFINE(1)
XMHF_EXCEPTION_HANDLER_DEFINE(2)
XMHF_EXCEPTION_HANDLER_DEFINE(3)
XMHF_EXCEPTION_HANDLER_DEFINE(4)
XMHF_EXCEPTION_HANDLER_DEFINE(5)
XMHF_EXCEPTION_HANDLER_DEFINE(6)
XMHF_EXCEPTION_HANDLER_DEFINE(7)
XMHF_EXCEPTION_HANDLER_DEFINE(8)
XMHF_EXCEPTION_HANDLER_DEFINE(9)
XMHF_EXCEPTION_HANDLER_DEFINE(10)
XMHF_EXCEPTION_HANDLER_DEFINE(11)
XMHF_EXCEPTION_HANDLER_DEFINE(12)
XMHF_EXCEPTION_HANDLER_DEFINE(13)
XMHF_EXCEPTION_HANDLER_DEFINE(14)
XMHF_EXCEPTION_HANDLER_DEFINE(15)
XMHF_EXCEPTION_HANDLER_DEFINE(16)
XMHF_EXCEPTION_HANDLER_DEFINE(17)
XMHF_EXCEPTION_HANDLER_DEFINE(18)
XMHF_EXCEPTION_HANDLER_DEFINE(19)
XMHF_EXCEPTION_HANDLER_DEFINE(20)
XMHF_EXCEPTION_HANDLER_DEFINE(21)
XMHF_EXCEPTION_HANDLER_DEFINE(22)
XMHF_EXCEPTION_HANDLER_DEFINE(23)
XMHF_EXCEPTION_HANDLER_DEFINE(24)
XMHF_EXCEPTION_HANDLER_DEFINE(25)
XMHF_EXCEPTION_HANDLER_DEFINE(26)
XMHF_EXCEPTION_HANDLER_DEFINE(27)
XMHF_EXCEPTION_HANDLER_DEFINE(28)
XMHF_EXCEPTION_HANDLER_DEFINE(29)
XMHF_EXCEPTION_HANDLER_DEFINE(30)
XMHF_EXCEPTION_HANDLER_DEFINE(31)
	
static u32 exceptionstubs[] = { 	XMHF_EXCEPTION_HANDLER_ADDROF(0),
							XMHF_EXCEPTION_HANDLER_ADDROF(1),
							XMHF_EXCEPTION_HANDLER_ADDROF(2),
							XMHF_EXCEPTION_HANDLER_ADDROF(3),
							XMHF_EXCEPTION_HANDLER_ADDROF(4),
							XMHF_EXCEPTION_HANDLER_ADDROF(5),
							XMHF_EXCEPTION_HANDLER_ADDROF(6),
							XMHF_EXCEPTION_HANDLER_ADDROF(7),
							XMHF_EXCEPTION_HANDLER_ADDROF(8),
							XMHF_EXCEPTION_HANDLER_ADDROF(9),
							XMHF_EXCEPTION_HANDLER_ADDROF(10),
							XMHF_EXCEPTION_HANDLER_ADDROF(11),
							XMHF_EXCEPTION_HANDLER_ADDROF(12),
							XMHF_EXCEPTION_HANDLER_ADDROF(13),
							XMHF_EXCEPTION_HANDLER_ADDROF(14),
							XMHF_EXCEPTION_HANDLER_ADDROF(15),
							XMHF_EXCEPTION_HANDLER_ADDROF(16),
							XMHF_EXCEPTION_HANDLER_ADDROF(17),
							XMHF_EXCEPTION_HANDLER_ADDROF(18),
							XMHF_EXCEPTION_HANDLER_ADDROF(19),
							XMHF_EXCEPTION_HANDLER_ADDROF(20),
							XMHF_EXCEPTION_HANDLER_ADDROF(21),
							XMHF_EXCEPTION_HANDLER_ADDROF(22),
							XMHF_EXCEPTION_HANDLER_ADDROF(23),
							XMHF_EXCEPTION_HANDLER_ADDROF(24),
							XMHF_EXCEPTION_HANDLER_ADDROF(25),
							XMHF_EXCEPTION_HANDLER_ADDROF(26),
							XMHF_EXCEPTION_HANDLER_ADDROF(27),
							XMHF_EXCEPTION_HANDLER_ADDROF(28),
							XMHF_EXCEPTION_HANDLER_ADDROF(29),
							XMHF_EXCEPTION_HANDLER_ADDROF(30),
							XMHF_EXCEPTION_HANDLER_ADDROF(31),
};
						

//initialize EMHF core exception handlers
//void xmhf_xcphandler_arch_initialize(void){
//arch_x86_idtdesc_t xcexhub_initialize(void){
void xcexhub_initialize(void){
	u32 *pexceptionstubs;
	u32 i;

	printf("\n%s: setting up runtime IDT...", __FUNCTION__);
	
	for(i=0; i < EMHF_XCPHANDLER_MAXEXCEPTIONS; i++){
		idtentry_t *idtentry=(idtentry_t *)((u32)&_idt_start+ (i*8));
		idtentry->isrLow= (u16)exceptionstubs[i];
		idtentry->isrHigh= (u16) ( (u32)exceptionstubs[i] >> 16 );
		idtentry->isrSelector = __CS_CPL0;
		idtentry->count=0x0;
		idtentry->type=0xEE;	//32-bit interrupt gate
								//present=1, DPL=11b, system=0, type=1110b
	}
	
	xmhf_baseplatform_arch_x86_initializeIDT();
	
	printf("\n%s: IDT setup done.", __FUNCTION__);
	//return _idt;
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
}

//exception handler hub
void xmhf_xcphandler_arch_hub(u32 vector, struct regs *r){
	switch(vector){
			case CPU_EXCEPTION_NMI:{
				xc_coreapi_arch_eventhandler_nmiexception(r);
				}
				break;

			case 0x3:{
					xmhf_xcphandler_arch_unhandled(vector, r);
					printf("\n%s: exception 3, returning", __FUNCTION__);
			}
			break;
			
			default:{
				xmhf_xcphandler_arch_unhandled(vector, r);
				printf("\nHalting System!\n");
				HALT();
			}
	}
}
	
