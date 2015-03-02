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

#ifndef __XMHFHICSLAB_H__
#define __XMHFHICSLAB_H__

#include <xmhf-hwm.h>
#include <xmhfhw.h>

#define XMHF_HIC_UAPI                       (0x666)

#define XMHF_HIC_UAPI_CPUSTATE                  (0)

#define XMHF_HIC_UAPI_CPUSTATE_VMREAD           (1)
#define XMHF_HIC_UAPI_CPUSTATE_VMWRITE          (2)
#define XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD    (3)
#define XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE   (4)
#define XMHF_HIC_UAPI_CPUSTATE_WRMSR            (5)
#define XMHF_HIC_UAPI_CPUSTATE_RDMSR            (6)


#define XMHF_HIC_UAPI_PHYSMEM                   (16)

#define XMHF_HIC_UAPI_PHYSMEM_PEEK              (17)
#define XMHF_HIC_UAPI_PHYSMEM_POKE              (18)

#define XMHF_HIC_UAPI_MEMPGTBL                  (24)

#define XMHF_HIC_UAPI_MEMPGTBL_GETENTRY         (25)
#define XMHF_HIC_UAPI_MEMPGTBL_SETENTRY         (26)


#define GUEST_SLAB_HEADER_MAGIC     (0x76543210)

#define XMHF_HIC_SLABCALL                   (0xA0)
#define XMHF_HIC_SLABRET                    (0xA1)

#define XMHF_HIC_SLABCALLEXCEPTION          (0xA2)
#define XMHF_HIC_SLABRETEXCEPTION           (0xA3)

#define XMHF_HIC_SLABCALLINTERCEPT          (0xA4)
#define XMHF_HIC_SLABRETINTERCEPT           (0xA5)


#ifndef __ASSEMBLY__

typedef void slab_input_params_t;
typedef void slab_output_params_t;


typedef struct {
    u32 slab_ctype;
    u32 src_slabid;
    u32 dst_slabid;
    u32 cpuid;
    u32 in_out_params[10];
} __attribute__((packed)) slab_params_t;




//////
// uapi related types

typedef struct {
    u32 guest_slab_index;
    void *addr_from;
    void *addr_to;
    u32 numbytes;
}__attribute__((packed)) xmhf_hic_uapi_physmem_desc_t;

typedef struct {
    u32 guest_slab_index;
    u64 gpa;
    u64 entry;
}__attribute__((packed)) xmhf_hic_uapi_mempgtbl_desc_t;

//guest slab header data type
typedef struct {
    u32 magic;
    __attribute__((aligned(4096))) u64 lvl2mempgtbl_pml4t[PAE_MAXPTRS_PER_PDPT];
    __attribute__((aligned(4096))) u64 lvl2mempgtbl_pdpt[PAE_MAXPTRS_PER_PDPT];
    __attribute__((aligned(4096))) u64 lvl2mempgtbl_pdts[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
    __attribute__(( aligned(16) )) u64 gdt[16];
} __attribute__((packed)) guest_slab_header_t;



//////
// HIC UAPI and trampoline invocation macros



//HIC UAPI


__attribute__((naked)) bool __slab_calluapi(u64 reserved_uapicall,
        u64 reserved_uapicall_num,  u64 uapi_subfn,
        u64 reserved, u64 iparams, u64 oparams);

void __slab_calluapinew(slab_params_t *sp);


#define XMHF_HIC_SLAB_UAPI_CPUSTATE(cpustatefn, iparams, oparams) \
    __slab_calluapi(XMHF_HIC_UAPI, XMHF_HIC_UAPI_CPUSTATE, cpustatefn, 0, iparams, oparams)


#define XMHF_HIC_SLAB_UAPI_PHYSMEM(physmemfn, iparams, oparams) \
    __slab_calluapi(XMHF_HIC_UAPI, XMHF_HIC_UAPI_PHYSMEM, physmemfn, 0, iparams, oparams)


#define XMHF_HIC_SLAB_UAPI_MEMPGTBL(mempgtblfn, iparams, oparams) \
    __slab_calluapi(XMHF_HIC_UAPI, XMHF_HIC_UAPI_MEMPGTBL, mempgtblfn, 0, iparams, oparams)


#define XMHF_SLAB_UAPI(sp) __slab_calluapinew(sp)

//HIC trampoline

__attribute__((naked)) bool __slab_calltrampoline(u64 reserved,
    slab_input_params_t *iparams, u64 iparams_size,
    slab_output_params_t *oparams, u64 oparams_size, u64 dst_slabid);

void __slab_calltrampolinenew(slab_params_t *sp);


#define XMHF_SLAB_CALL(dst_slabname, dst_slabid, iparams, iparams_size, oparams, oparams_size) \
    __slab_calltrampoline(0, iparams, iparams_size, oparams, oparams_size, dst_slabid)


#define XMHF_SLAB_CALLNEW(sp) \
    __slab_calltrampolinenew(sp)




//////
// slab entry stub definitions


void slab_interface(slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 src_slabid, u64 cpuindex);

void slab_main(slab_params_t *sp);

typedef void (*FPSLABMAIN)(slab_params_t *sp);
/* x86-64

//_slab_entrystub entry register mappings:
//
//RDI = iparams
//RSI = iparams_size
//RDX = slab entrystub; used for SYSEXIT
//RCX = slab entrystub stack TOS for the CPU; used for SYSEXIT
//R8 = oparams
//R9 = oparams_size
//R10 = src_slabid
//R11 = cpuid






#define XMHF_SLAB(slab_name)	\
	__attribute__ ((section(".rodata"))) char * _namestring="_xmhfslab_hyp";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 _slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".stackhdr"))) u64 _slab_tos[MAX_PLATFORM_CPUS]= { ((u64)&_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u64)_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 _dmadataplaceholder[1];\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub(void){	\
	asm volatile ( \
            "pushq %%r10 \r\n" \
            "movq %%r8, %%rdx \r\n" \
            "movq %%r9, %%rcx \r\n" \
            "movq %%r10, %%r8 \r\n" \
            "movq %%r11, %%r9 \r\n" \
            "callq slab_interface \r\n"		\
            "popq %%r9 \r\n" \
            "movq %0, %%rdi \r\n" \
            "sysenter \r\n" \
            \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
            \
			:  \
			:  "i" (XMHF_HIC_SLABRET) \
			:  \
		);	\
    }\





#define XMHF_SLAB_GUEST(slab_name)	\
	__attribute__ ((section(".rodata"))) char * _namestring="_xmhfslab_guest";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 _slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE]; \
	__attribute__ ((section(".stackhdr"))) u64 _slab_tos[MAX_PLATFORM_CPUS]= { ((u64)&_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u64)_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 _dmadataplaceholder[1];\
    __attribute__ ((section(".rwdatahdr"))) guest_slab_header_t _guestslabheader = {GUEST_SLAB_HEADER_MAGIC, 0};\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub(void){	\
	asm volatile ( \
          "jmp slab_interface \r\n"		\
			:  \
			:  \
			:  \
		);	\
    }\



#define XMHF_SLAB_INTERCEPT(slab_name)	\
	__attribute__ ((section(".rodata"))) char * _namestring="_xmhfslab_hyp";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 _slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".stackhdr"))) u64 _slab_tos[MAX_PLATFORM_CPUS]= { ((u64)&_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u64)_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 _dmadataplaceholder[1];\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub(void){	\
	asm volatile ( \
            "pushq %%r10 \r\n" \
            "movq %%r8, %%rdx \r\n" \
            "movq %%r9, %%rcx \r\n" \
            "movq %%r10, %%r8 \r\n" \
            "movq %%r11, %%r9 \r\n" \
            "callq slab_interface \r\n"		\
            "popq %%r9 \r\n" \
            "movq %0, %%rdi \r\n" \
            "sysenter \r\n" \
            \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
            \
			:  \
			:  "i" (XMHF_HIC_SLABRETINTERCEPT) \
			:  \
		);	\
    }\



#define XMHF_SLAB_EXCEPTION(slab_name)	\
	__attribute__ ((section(".rodata"))) char * _namestring="_xmhfslab_hyp";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 _slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".stackhdr"))) u64 _slab_tos[MAX_PLATFORM_CPUS]= { ((u64)&_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u64)_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u64)&_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 _dmadataplaceholder[1];\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub(void){	\
	asm volatile ( \
            "pushq %%r10 \r\n" \
            "movq %%r8, %%rdx \r\n" \
            "movq %%r9, %%rcx \r\n" \
            "movq %%r10, %%r8 \r\n" \
            "movq %%r11, %%r9 \r\n" \
            "callq slab_interface \r\n"		\
            "popq %%r9 \r\n" \
            "movq %0, %%rdi \r\n" \
            "sysenter \r\n" \
            \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
            \
			:  \
			:  "i" (XMHF_HIC_SLABRETEXCEPTION) \
			:  \
		);	\
    }\

*/


//_slab_entrystub entry register mappings:
//
//RDI = iparams
//RSI = iparams_size
//RDX = slab entrystub; used for SYSEXIT
//RCX = slab entrystub stack TOS for the CPU; used for SYSEXIT
//R8 = oparams
//R9 = oparams_size
//R10 = src_slabid
//R11 = cpuid




/*

#define XMHF_SLAB(slab_name)	\
	__attribute__ ((section(".rodata"))) char * _namestring="_xmhfslab_hyp";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 _slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".stackhdr"))) u32 _slab_tos[MAX_PLATFORM_CPUS]= { ((u32)&_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u32)_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 _dmadataplaceholder[1];\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub(void){	\
	asm volatile ( \
            "call slab_interface \r\n"		\
            "sysenter \r\n" \
            \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
            \
			:  \
			:  "i" (XMHF_HIC_SLABRET) \
			:  \
		);	\
    }\





#define XMHF_SLAB_GUEST(slab_name)	\
	__attribute__ ((section(".rodata"))) char * _namestring="_xmhfslab_guest";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 _slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE]; \
	__attribute__ ((section(".stackhdr"))) u32 _slab_tos[MAX_PLATFORM_CPUS]= { ((u32)&_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u32)_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 _dmadataplaceholder[1];\
    __attribute__ ((section(".rwdatahdr"))) guest_slab_header_t _guestslabheader = {GUEST_SLAB_HEADER_MAGIC, 0};\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub(void){	\
	asm volatile ( \
          "jmp slab_interface \r\n"		\
			:  \
			:  \
			:  \
		);	\
    }\



#define XMHF_SLAB_INTERCEPT(slab_name)	\
	__attribute__ ((section(".rodata"))) char * _namestring="_xmhfslab_hyp";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 _slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".stackhdr"))) u32 _slab_tos[MAX_PLATFORM_CPUS]= { ((u32)&_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u32)_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 _dmadataplaceholder[1];\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub(void){	\
	asm volatile ( \
            "call slab_interface \r\n"		\
            "sysenter \r\n" \
            \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
            \
			:  \
			:  "i" (XMHF_HIC_SLABRETINTERCEPT) \
			:  \
		);	\
    }\



#define XMHF_SLAB_EXCEPTION(slab_name)	\
	__attribute__ ((section(".rodata"))) char * _namestring="_xmhfslab_hyp";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 _slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".stackhdr"))) u32 _slab_tos[MAX_PLATFORM_CPUS]= { ((u32)&_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u32)_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 _dmadataplaceholder[1];\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub(void){	\
	asm volatile ( \
            "call slab_interface \r\n"		\
            "sysenter \r\n" \
            \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
            \
			:  \
			:  "i" (XMHF_HIC_SLABRETEXCEPTION) \
			:  \
		);	\
    }\

*/






#define XMHF_SLABNEW(slab_name)	\
	__attribute__ ((section(".rodata"))) char * _namestring="_xmhfslab_hyp";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 _slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".stackhdr"))) u32 _slab_tos[MAX_PLATFORM_CPUS]= { ((u32)&_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u32)_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 _dmadataplaceholder[1];\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub(void){	\
	asm volatile ( \
            "jmp slab_main \r\n" \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
            \
			:  \
			:  "i" (XMHF_HIC_SLABRET) \
			:  \
		);	\
    }\


#define XMHF_SLAB(slab_name)	\
	__attribute__ ((section(".rodata"))) char * _namestring="_xmhfslab_hyp";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 _slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".stackhdr"))) u32 _slab_tos[MAX_PLATFORM_CPUS]= { ((u32)&_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u32)_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 _dmadataplaceholder[1];\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub(void){	\
	asm volatile ( \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
            \
			:  \
			:  "i" (XMHF_HIC_SLABRET) \
			:  \
		);	\
    }\




#define XMHF_SLAB_GUEST(slab_name)	\
	__attribute__ ((section(".rodata"))) char * _namestring="_xmhfslab_guest";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 _slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE]; \
	__attribute__ ((section(".stackhdr"))) u32 _slab_tos[MAX_PLATFORM_CPUS]= { ((u32)&_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u32)_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 _dmadataplaceholder[1];\
    __attribute__ ((section(".rwdatahdr"))) guest_slab_header_t _guestslabheader = {GUEST_SLAB_HEADER_MAGIC, 0};\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub(void){	\
	asm volatile ( \
            "jmp slab_main \r\n" \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
 			:  \
			:  \
			:  \
		);	\
    }\



#define XMHF_SLAB_INTERCEPT(slab_name)	\
	__attribute__ ((section(".rodata"))) char * _namestring="_xmhfslab_hyp";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 _slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".stackhdr"))) u32 _slab_tos[MAX_PLATFORM_CPUS]= { ((u32)&_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u32)_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 _dmadataplaceholder[1];\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub(void){	\
	asm volatile ( \
            "jmp slab_main \r\n" \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
            \
			:  \
			:  "i" (XMHF_HIC_SLABRETINTERCEPT) \
			:  \
		);	\
    }\



#define XMHF_SLAB_EXCEPTION(slab_name)	\
	__attribute__ ((section(".rodata"))) char * _namestring="_xmhfslab_hyp";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 _slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".stackhdr"))) u32 _slab_tos[MAX_PLATFORM_CPUS]= { ((u32)&_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u32)_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u32)&_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 _dmadataplaceholder[1];\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub(void){	\
	asm volatile ( \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
            \
			:  \
			:  "i" (XMHF_HIC_SLABRETEXCEPTION) \
			:  \
		);	\
    }\




#endif //__ASSEMBLY__


#endif //__XMHFHICSLAB_H__


