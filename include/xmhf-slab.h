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

//#define XMHF_SLAB_CALLP2P					0xB0

#define XMHF_SLAB_CALLTYPE_CALLP2P				0xB0
#define XMHF_SLAB_CALLTYPE_RETP2P               0xB1


#define XMHF_SLAB_XCPRIMEON_INDEX			(0)
#define XMHF_SLAB_TESTSLAB1_INDEX			(1)
#define XMHF_SLAB_TESTSLAB2_INDEX			(2)
#define XMHF_SLAB_XCEXHUB_INDEX				(3)
#define XMHF_SLAB_XCSMP_INDEX				(4)
#define XMHF_SLAB_XCDEV_INDEX               (5)
#define XMHF_SLAB_XCRICHGUEST_INDEX			(6)
#define XMHF_SLAB_XCIHUB_INDEX				(7)

#define XMHF_SLAB_XCAPIPLATFORM_INDEX       (8)
#define XMHF_SLAB_XCAPIHPT_INDEX            (9)
#define XMHF_SLAB_XCAPICPUSTATE_INDEX       (10)
#define XMHF_SLAB_XCAPITRAPMASK_INDEX       (11)
#define XMHF_SLAB_XCAPIPARTITION_INDEX      (12)

#define XMHF_SLAB_XCAPI_INDEX               (13)

//hypapp slab indices currently allow for only one hypapp to be linked in
//TODO: add support for multiple hypapps
#define XMHF_SLAB_XHHYPERDEP_INDEX			(13)
#define XMHF_SLAB_XHHELLOWORLD_INDEX		(13)

#ifndef __ASSEMBLY__

typedef struct {
	bool desc_valid;
	u64 numdevices;
    xc_platformdevice_arch_desc_t arch_desc[MAX_PLATFORM_DEVICES];
} __attribute__((packed)) xc_platformdevice_desc_t;

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
        xc_platformdevice_desc_t retval_xc_platformdevice_desc;
}__attribute__((packed)) slab_retval_t;

typedef struct {
    bool input_bool[8];
    u64 input_u64[8];
    u32 input_u32[8];
    u16 input_u16[8];
    u8 input_u8[8];
    struct regs input_regs;
    context_desc_t input_context_desc;
    xc_hypapp_arch_param_t input_xc_hypapp_arch_param;
    xc_platformdevice_desc_t input_xc_platformdevice_desc;
}__attribute__((packed)) slab_params_t;


extern __attribute__(( section(".sharedro_xcbootinfoptr") )) XMHF_BOOTINFO *xcbootinfo;
extern __attribute__ ((section(".sharedro_slab_table"))) slab_header_t _slab_table[XMHF_SLAB_NUMBEROFSLABS];

typedef struct {
	u32 returnaddress;
	u32 rsvd0[6];
	u32 src_slabid;
	u32 dst_slabid;
	u32 fn_id;
	u8 params[1];
} __attribute__((packed)) slab_trampoline_frame_t;

/*
__attribute__ ((section(".slab_trampoline"))) __attribute__((naked)) __attribute__ ((noinline)) static inline slab_retval_t __xmhf_impslab_p2p(u32 src_slabid, u32 dst_slabid, u32 iface_subid, u32 iface_subparamsize, ...){
	asm volatile(
						"pushl %%ebp \r\n"
						"pushl %%ecx \r\n"
						"pushl %%esi \r\n"
						"pushl %%edi \r\n"
						"pushl $1f	\r\n"

						"movl %%esp, %%ecx \r\n"
						"movl 40(%%esp), %%edx \r\n"
						"addl %0, %%edx \r\n"
						"rol $16, %%edx \r\n"
						"movw %1, %%dx \r\n"

						"jmp _slab_trampolinenew \r\n"

						"1: \r\n"
						"movl %2, %%ecx \r\n"
						"movl 24(%%esp), %%edi \r\n"
						"cld \r\n"
						"rep movsb \r\n"

						"addl $4, %%esp \r\n"
						"popl %%edi \r\n"
						"popl %%esi \r\n"
						"popl %%ecx \r\n"
						"popl %%ebp \r\n"

						"ret $0x4 \r\n"
						:
						: "i"(4*sizeof(u32)), "i" (XMHF_SLAB_CALLP2P), "i" (sizeof(slab_retval_t))	\
						:
	);

}

//privilege-to-privilege (P2P) slab call macro
#define XMHF_SLAB_CALL_P2P(slab_name, src_slabid, dst_slabid, iface_subid, ...) __xmhf_impslab_p2p(src_slabid, dst_slabid, iface_subid, __VA_ARGS__)

#define XMHF_SLAB_DEF(slab_name)	\
	__attribute__ ((section(".stack"))) u8 _slab_stack[XMHF_SLAB_STACKSIZE];	\
																				\
	__attribute__((naked)) __attribute__ ((section(".slab_entrystubnew"))) __attribute__((align(1))) void _interfacestub_##slab_name(void){	\
	asm volatile (							\
			"pushl %%ebp \r\n"				\
			"movl %%esp, %%ebp \r\n"		\
											\
			"movl %%ecx, %%ebx	\r\n"		\
			"shr $16, %%ecx \r\n"			\
			"subl %0, %%esp \r\n"			\
			"movl %%esp, %%eax \r\n"		\
			"subl %%ecx, %%esp \r\n"		\
			"movl %%esp, %%edi \r\n"		\
			"cld \r\n"						\
			"rep movsb \r\n"				\
											\
			"cmpw %1, %%bx \r\n"			\
			"jne 3f \r\n"					\
											\
			"pushl %%eax \r\n"				\
			"call "#slab_name"_interface \r\n"		\
											\
			"2:\r\n"						\
			"movl %%edi, %%esi \r\n"		\
			"movl %%ebp, %%esp \r\n"		\
			"movl (%%esp), %%ebp \r\n"		\
			"addl $4, %%esp \r\n"			\
			"ret \r\n"						\
											\
			"3: \r\n"						\
			"int $0x03 \r\n"				\
			"hlt \r\n"						\
			:								\
			: "i" (sizeof(slab_retval_t)), "i" (XMHF_SLAB_CALLP2P)		\
			:								\
		);									\
}

#define XMHF_SLAB_DEF_BARE(slab_name)	\
	__attribute__ ((section(".stack"))) u8 _slab_stack[XMHF_SLAB_STACKSIZE];	\
																				\
	__attribute__((naked)) __attribute__ ((section(".slab_entrystubnew"))) __attribute__((align(1))) void _interfacestub_##slab_name(void){	\
	asm volatile (							\
			"jmp "#slab_name"_interface \r\n"		\
			:								\
			: 								\
			:								\
		);									\
}
*/
















__attribute__ ((section(".slab_trampoline"))) __attribute__((naked)) __attribute__ ((noinline)) static inline slab_retval_t __xmhf_impslab_p2p(u32 src_slabid, u32 dst_slabid, u32 iface_subid, u32 iface_subparamsize, ...){

}

//privilege-to-privilege (P2P) slab call macro
#define XMHF_SLAB_CALL_P2P(slab_name, src_slabid, dst_slabid, iface_subid, ...) __xmhf_impslab_p2p(src_slabid, dst_slabid, iface_subid, __VA_ARGS__)

#define XMHF_SLAB_DEF(slab_name)	\
	__attribute__ ((section(".stack"))) u8 slab_name##_slab_stack[XMHF_SLAB_STACKSIZE];	\
																				\
	__attribute__((naked)) __attribute__ ((section(".slab_entrystubnew"))) __attribute__((align(1))) void _interfacestub_##slab_name(void){	\
}

#define XMHF_SLAB_DEF_BARE(slab_name)	\
	__attribute__ ((section(".stack"))) u8 slab_name##_slab_stack[XMHF_SLAB_STACKSIZE];	\
																				\
	__attribute__((naked)) __attribute__ ((section(".slab_entrystubnew"))) __attribute__((align(1))) void _interfacestub_##slab_name(void){	\
}

#define XMHF_SLAB_CALL(x)   x









//////////////////////////////////////////////////////////////////////////////




//slabretval_t - rdi
//u64 src_slabid - rsi
//u64 dst_slabid - rdx
//u64 call_type - rcx
//u64 rsv0 - r8
//u64 rsv1 - r9
//[rsp] = return rip
//[rsp+8] = slab_params_t srparams
__attribute__ ((section(".slab_trampoline"))) __attribute__((naked)) __attribute__ ((noinline)) static inline slab_retval_t __xmhf_slab_callstubp2p(u64 src_slabid, u64 dst_slabid, u64 call_type, u64 rsv0, u64 rsv1, slab_params_t srparams){

    asm volatile (
        "movq $1f, %%r8 \r\n"
        "leaq 8(%%rsp), %%r9 \r\n"
        "int $0x03\r\n"
        "int $0x03\r\n"
        "jmp _slab_trampolinenew \r\n"

        "1:\r\n"
        "int $0x03\r\n"
        "movq %%rdi, %%rax \r\n"
        "retq \r\n"
        :
        :
        :
    );

}



//#define XMHF_SLAB_CALLP2P(slab_name, src_slabid, dst_slabid, call_type, rsv0, ...) slab_name##_interface(src_slabid, dst_slabid, call_type, rsv0, __VA_ARGS__)
#define XMHF_SLAB_CALLP2P(slab_name, src_slabid, dst_slabid, call_type, rsv0, ...) __xmhf_slab_callstubp2p(src_slabid, dst_slabid, call_type, rsv0, __VA_ARGS__)


#define XMHF_SLAB_DEFENTRYSTUBBARE(slab_name)	\
	__attribute__ ((section(".stack"))) u8 slab_name##_slab_stack[XMHF_SLAB_STACKSIZE];	\
																				\
	__attribute__((naked)) __attribute__ ((section(".slab_entrystubnew"))) __attribute__((align(1))) void _interfacestub_##slab_name(void){	\
}


#define XMHF_SLAB_DEFENTRYSTUB(slab_name)	\
	__attribute__ ((section(".stack"))) u8 slab_name##_slab_stack[XMHF_SLAB_STACKSIZE];	\
																				\
	__attribute__((naked)) __attribute__ ((section(".slab_entrystubnew"))) __attribute__((align(1))) void _entrystub_##slab_name(void){	\
	asm volatile (							\
            "pushq %%rdi \r\n" \
            "pushq %%rsi \r\n" \
            "pushq %%rdx \r\n" \
            "pushq %%rcx \r\n" \
            "pushq %%r8 \r\n" \
            "pushq %%r9 \r\n" \
                            \
                            \
            "int $0x03 \r\n" \
                            \
                            \
            "subq $4096, %%rsp \r\n" \
            "movq %%rsp, %%rax \r\n" \
                            \
                            \
            "int $0x03 \r\n" \
                            \
            "pushq %%rsi \r\n" \
            "pushq %%rdi \r\n" \
            "pushq %%rcx \r\n" \
                                \
            "movq %0, %%rcx \r\n" \
            "movq %%r9, %%rsi \r\n" \
            "movq %%rax, %%rdi \r\n" \
                            \
            "int $0x03 \r\n" \
                            \
            "cld \r\n" \
            "rep movsb \r\n" \
                        \
            "popq %%rcx \r\n" \
            "popq %%rdi \r\n" \
            "popq %%rsi \r\n" \
                        \
                            \
            "int $0x03 \r\n" \
                            \
            "callq "#slab_name"_interface \r\n"		\
                        \
                       \
            "int $0x03 \r\n" \
                            \
            "addq $4096, %%rsp \r\n" \
                        \
                       \
            "int $0x03 \r\n" \
                            \
            "popq %%r9 \r\n" \
            "popq %%r8 \r\n" \
            "popq %%rcx \r\n" \
            "popq %%rdx \r\n" \
            "popq %%rsi \r\n" \
            "popq %%rdi \r\n" \
                    \
            "movq %1, %%rcx \r\n" \
                            \
            "int $0x03 \r\n" \
                            \
            "jmp _slab_trampolinenew \r\n" \
			:								\
			: "i" (sizeof(slab_params_t)), "i" (XMHF_SLAB_CALLTYPE_RETP2P)	\
			:								\
		);									\
}






#endif //__ASSEMBLY__

#endif //__XMHF_SLAB_H__
