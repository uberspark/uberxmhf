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
 * arch. specific exception handler stubs that are mapped into a slab
 * memory view
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-core.h>

#include <xcexhub.h>

__attribute__(( section(".slabtrampoline") )) static u64 _xcexhub_exception_lock = 1;
__attribute__(( section(".slabtrampoline") )) __attribute__(( aligned(4096) )) static u8 _xcexhub_exception_stack[(MAX_PLATFORM_CPUS+1)][PAGE_SIZE_4K];
__attribute__(( section(".slabtrampoline") )) static u64 _xcexhub_exception_stack_index = &_xcexhub_exception_stack[MAX_PLATFORM_CPUS];


//#define XMHF_EXCEPTION_HANDLER_DEFINE(vector) 												\
//	__attribute__(( section(".slabtrampoline") )) static void __xmhf_exception_handler_##vector(void) __attribute__((naked)) { 					\
//		asm volatile(												\
//						"iretq\r\n"									\
//					:												\
//					:	\
//		);															\
//	}\


#define XMHF_EXCEPTION_HANDLER_DEFINE(vector) 												\
	__attribute__(( section(".slabtrampoline") )) static void __xmhf_exception_handler_##vector(void) __attribute__((naked)) { 					\
		asm volatile(												\
						"1:	btq	$0, %0	\r\n"						/*start atomic operation*/\
						"jnc 1b	\r\n"								\
						"lock \r\n"   								\
						"btrq	$0, %0	\r\n"						\
						"jnc 1b \r\n"   							\
                                                                    \
						"subq $4096, %1 \r\n"                       \
						"xchgq %%rsp, %1 \r\n"						/*rsp=stack top for current CPU*/ \
						"pushq %1 \r\n"								/*store original exception entry rsp*/ \
						"movq %%rsp, %1 \r\n"                       /*compute and store next stack top*/ \
                        "addq $8, %1 \r\n"                          \
                                                                    \
						"btsq	$0, %0		\r\n"					/*end atomic operation */ \
																\
                        "pushq %%rbp \r\n"\
                        "pushq %%rdi \r\n"\
                        "pushq %%rsi \r\n"\
                        "pushq %%rdx \r\n"\
                        "pushq %%rcx \r\n"\
                        "pushq %%rbx \r\n"\
                        "pushq %%rax \r\n"\
                        "pushq %%r15 \r\n"\
                        "pushq %%r14 \r\n"\
                        "pushq %%r13 \r\n"\
                        "pushq %%r12 \r\n"\
                        "pushq %%r11 \r\n"\
                        "pushq %%r10 \r\n"\
                        "pushq %%r9 \r\n"\
                        "pushq %%r8 \r\n"\
                        "movq %%rsp, %%rsi \r\n"\
                        "mov %2, %%rdi \r\n"\
                        "callq xmhf_xcphandler_arch_hub \r\n"\
                        "popq %%r8 \r\n"\
                        "popq %%r9 \r\n"\
                        "popq %%r10 \r\n"\
                        "popq %%r11 \r\n"\
                        "popq %%r12 \r\n"\
                        "popq %%r13 \r\n"\
                        "popq %%r14 \r\n"\
                        "popq %%r15 \r\n"\
                        "popq %%rax \r\n"\
                        "popq %%rbx \r\n"\
                        "popq %%rcx \r\n"\
                        "popq %%rdx \r\n"\
                        "popq %%rsi \r\n"\
                        "popq %%rdi \r\n"\
                        "popq %%rbp \r\n"\
                                                                    \
						"2:	btq	$0, %0	\r\n"						/*start atomic operation*/\
						"jnc 2b	\r\n"								\
						"lock \r\n"   								\
						"btrq	$0, %0	\r\n"						\
						"jnc 2b \r\n"   							\
																	\
                        "popq %%rsp \r\n"							/*restore original exception entry rsp*/\
						"addq $4096, %1 \r\n"                       \
																	\
						"btsq	$0, %0		\r\n"					/*end atomic operation */ \
																	\
						"iretq\r\n"									\
					:												\
					:	"m" (_xcexhub_exception_lock), "m" (_xcexhub_exception_stack_index), "i" (vector)				\
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

__attribute__(( section(".section_archds") )) u64  _exceptionstubs[] = { XMHF_EXCEPTION_HANDLER_ADDROF(0),
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


