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

// XMHF slab decls./defns.
// author: amit vasudevan (amitvasudevan@acm.org)
// XXX: need to split arch. dependent portions

#ifndef __XMHF_SLAB_H__
#define __XMHF_SLAB_H__

#define	XMHF_SLAB_FN_RETTYPE_NORMAL		0x0
#define	XMHF_SLAB_FN_RETTYPE_AGGREGATE	0x4


#define XMHF_SLAB_XCPRIMEON_INDEX			(0)
#define XMHF_SLAB_TESTSLAB1_INDEX			(1)
#define XMHF_SLAB_TESTSLAB2_INDEX			(2)
#define XMHF_SLAB_XCSMP_INDEX				(3)
#define XMHF_SLAB_XCRICHGUEST_INDEX			(4)
#define XMHF_SLAB_XCIHUB_INDEX				(5)
#define XMHF_SLAB_XCAPI_INDEX				(6)
#define XMHF_SLAB_XCEXHUB_INDEX				(7)

//hypapp slab indices currently allow for only one hypapp to be linked in
//TODO: add support for multiple hypapps
#define XMHF_SLAB_XHHYPERDEP_INDEX			(8)
#define XMHF_SLAB_XHHELLOWORLD_INDEX		(8)

#ifndef __ASSEMBLY__

//slab interface aggregate return type
typedef union {
		bool retval_bool;
		u8 retval_u8;
		u16 retval_u16;
		u32 retval_u32;
		u64 retval_u64;
		struct regs retval_regs;
		context_desc_t retval_context_desc;
		xc_hypapp_arch_param_t retval_xc_hypapp_arch_param;
} slab_retval_t;

//extern slab_header_t _slab_table[];

extern __attribute__(( section(".sharedro_xcbootinfoptr") )) XMHF_BOOTINFO *xcbootinfo;
extern __attribute__ ((section(".sharedro_slab_table"))) slab_header_t _slab_table[XMHF_SLAB_NUMBEROFSLABS];

/*#define _XMHF_SLAB_DEFEXPORTFN(fn_name, fn_num, fn_aggregateret)		\
			"1:\r\n"								\
			"cmpl $"#fn_num", %%ebx \r\n"			\
			"jne 1f \r\n"							\
			"call "#fn_name" \r\n"					\
			"subl $"#fn_aggregateret", %%ebp \r\n"	\
			"jmp endswitch \r\n"					\
*/

#define _XMHF_SLAB_DEFEXPORTFN(fn_name, fn_num, fn_aggregateret)		\
			"cmpl $"#fn_num", %%ebx \r\n"			\
			"jne 1f \r\n"							\
			"jmp "#fn_name" \r\n"					\
			"1:\r\n"								\


#define XMHF_SLAB_DEFEXPORTFN(fn_name, fn_num, fn_aggregateret)		_XMHF_SLAB_DEFEXPORTFN(fn_name, fn_num, fn_aggregateret)

//setup
//esi = base address of input parameter frame on stack (excluding return address)
//edi = return address
//ebx = function number
//ecx = number of 32-bit dwords comprising the parameters (excluding return address)
/*							
#define XMHF_SLAB_DEFINTERFACE(...) __attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) void _slab_interface(void){	\
	asm volatile (							\
			"pushl %%edi \r\n" 				\
											\
			"xorl %%ebp, %%ebp \r\n"		\
			"cmpl $0, %%edx \r\n"			\
			"je 1f \r\n"					\
			"movl %%edx, %%ebp \r\n"		\
			"movl %%esp, %%edx \r\n"		\
			"subl %%ebp, %%edx \r\n"		\
			"1:\r\n"						\
			"addl %%ecx, %%ebp \r\n"		\
			"subl %%ebp, %%esp 	\r\n"		\
			"movl %%esp, %%edi \r\n"		\
			"cld \r\n"						\
			"rep movsb \r\n"				\
			"cmpl $0, %%edx \r\n"			\
			"je 1f \r\n"					\
			"addl $4, %%esp \r\n"			\
			"pushl %%edx \r\n"				\
			"movl %%edx, %%esi \r\n"		\
											\
			__VA_ARGS__ 					\
											\
			"1:\r\n"						\
			"endswitch:\r\n"				\
			"addl %%ebp, %%esp \r\n"		\
			"popl %%edi \r\n"				\
			"jmpl *%%edi \r\n"				\
			:								\
			:								\
			:								\
		);									\
}*/											\


#define XMHF_SLAB_DEFINTERFACE(...) __attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) void _slab_interface(void){	\
	asm volatile (							\
											\
			__VA_ARGS__ 					\
											\
			:								\
			:								\
			:								\
		);									\
}											\


#define XMHF_SLAB_DEFINTERFACEBARE(fn) __attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) void _slab_interface(void){	\
	asm volatile (							\
			"jmp "#fn" \r\n" 				\
			:								\
			:								\
			:								\
		);									\
}											\

/*
#define _XMHF_SLAB_DEFIMPORTFNSTUB(src_slab_index, dest_slab_index, fnnum, fn_paramsize, fn_retsize, fn_aggregateret) asm volatile(	\
						"pushl %%edi \r\n"				\
						"pushl %%esi \r\n"				\
						"pushl %%ebp \r\n"				\
						"pushl %%ecx \r\n"				\
						"pushl %%ebx \r\n"				\
														\
						"leal 24(%%esp), %%esi \r\n"	\
						"movl $1f, %%edi \r\n"			\
						"movl %0, %%ebx \r\n"			\
						"movl %1, %%ecx \r\n"			\
						"movl %3, %%edx \r\n"			\
						"movl %5, %%eax \r\n"			\
						"movl %%eax, %%cr3 \r\n"		\
						"movl %2, %%eax \r\n"			\
						"jmpl *%%eax	\r\n"			\
														\
						"1: \r\n"						\
						"movl %4, %%ecx \r\n"			\
						"movl %%ecx, %%cr3 \r\n"		\
						"movl %3, %%ecx \r\n"			\
						"movl 24(%%esp), %%edi \r\n"	\
						"cld \r\n"						\
						"rep movsb \r\n"				\
						"popl %%ebx \r\n"				\
						"popl %%ecx \r\n"				\
						"popl %%ebp \r\n"				\
						"popl %%esi \r\n"				\
						"popl %%edi \r\n"				\
						"ret $"#fn_aggregateret" \r\n"					\
						: 								\
						: "i" (fnnum), "i" (fn_paramsize), "m" (_slab_table[dest_slab_index].entry_cr3), "i" (fn_retsize), "m" (_slab_table[src_slab_index].slab_macmid), "m" (_slab_table[dest_slab_index].slab_macmid)	\
						:	 							\
						);								\
*/

// esi = 32-bit address of input parameter base
// edi = 32-bit address of return from slab call
// ebp = 32-bit address of destination slab entry point
// ecx = top 16-bits = size of result dwords
//		 bottom 16-bits = size of parameter dwords
// ebx = 32-bit function number
// eax = 32-bit src slab macmid
// edx = 32-bit dst slab macmid

#define _XMHF_SLAB_DEFIMPORTFNSTUB(src_slab_index, dest_slab_index, fnnum, fn_paramsize, fn_retsize, fn_aggregateret) asm volatile(	\
						"pushl %%edi \r\n"				\
						"pushl %%esi \r\n"				\
						"pushl %%ebp \r\n"				\
						"pushl %%ecx \r\n"				\
						"pushl %%ebx \r\n"				\
														\
						"leal 24(%%esp), %%esi \r\n"	\
						"movl $1f, %%edi \r\n"			\
						"movl %0, %%ebp \r\n"			\
						"movw %1, %%cx \r\n"			\
						"rol $16, %%ecx \r\n"			\
						"movw %2, %%cx \r\n"			\
						"movl %3, %%ebx \r\n"			\
						"movl %4, %%eax \r\n"			\
						"movl %5, %%edx \r\n"			\
														\
						"jmp _slab_trampoline \r\n"		\
														\
						"1: \r\n"						\
						"popl %%ebx \r\n"				\
						"popl %%ecx \r\n"				\
						"popl %%ebp \r\n"				\
						"popl %%esi \r\n"				\
						"popl %%edi \r\n"				\
						"ret $"#fn_aggregateret" \r\n"					\
						: 								\
						: "m" (_slab_table[dest_slab_index].entry_cr3), "i" (fn_retsize), "i" (fn_paramsize), "i" (fnnum), "m" (_slab_table[src_slab_index].slab_macmid), "m" (_slab_table[dest_slab_index].slab_macmid)	\
						:	 							\
						);								\

#define XMHF_SLAB_DEFIMPORTFNSTUB(src_slab_index, dest_slab_index, fnnum, fn_paramsize, fn_retsize, fn_aggregateret) _XMHF_SLAB_DEFIMPORTFNSTUB(src_slab_index, dest_slab_index, fnnum, fn_paramsize, fn_retsize, fn_aggregateret)


//#define XMHF_SLAB_DEFIMPORTFN(fn_decl, fn_stub)	__attribute__ ((section(".slab_trampoline"))) __attribute__((naked)) __attribute__ ((noinline)) static inline fn_decl { fn_stub }

#define XMHF_SLAB_DEFIMPORTFN(fn_rettype, fn_name, fn_decl, fn_stub)	\
	__attribute__ ((section(".slab_trampoline"))) __attribute__((naked)) __attribute__ ((noinline)) static inline fn_rettype __impslab__##fn_name fn_decl { fn_stub }	\

#define XMHF_SLAB_CALL(slabfn) __impslab__##slabfn


/*
#define XMHF_SLAB(slab_name)	\
	extern void _slab_interface(void);												\
	extern u8 slab_rodata_start[];													\
	extern u8 slab_rodata_end[];													\
	extern u8 slab_rwdata_start[];													\
	extern u8 slab_rwdata_end[];													\
	extern u8 slab_code_start[];													\
	extern u8 slab_code_end[];														\
	extern u8 slab_stack_start[];													\
	extern u8 slab_stack_end[];														\
																					\
	__attribute__ ((section(".stack"))) static u8 _slab_stack[XMHF_SLAB_STACKSIZE];	\
																					\
	__attribute__ ((section(".slabrodata"))) slab_header_t slab_header = {			\
		.slab_index = 0,															\
		.slab_macmid = 0,															\
		.slab_privilegemask = 0,													\
		.slab_tos = ((u32)(&_slab_stack) + sizeof(_slab_stack)), 					\
		.slab_rodata.start = &slab_rodata_start,									\
		.slab_rodata.end = (u32)&slab_rodata_end,									\
		.slab_rwdata.start = &slab_rwdata_start,									\
		.slab_rwdata.end = (u32)&slab_rwdata_end,									\
		.slab_code.start = (u32)&slab_code_start,									\
		.slab_code.end = (u32)&slab_code_end,										\
		.slab_stack.start = (u32)&slab_stack_start,									\
		.slab_stack.end = (u32)&slab_stack_end,										\
		.entry_cr3 = &_slab_interface,												\
	};																				\
*/


#define XMHF_SLAB(slab_name)	\
	__attribute__ ((section(".stack"))) u8 _slab_stack[XMHF_SLAB_STACKSIZE];	\

//	__attribute__ ((section(".slab_trampoline"))) u8 _slab_trampoline_peg[1];	\

#endif //__ASSEMBLY__

#endif //__XMHF_SLAB_H__
