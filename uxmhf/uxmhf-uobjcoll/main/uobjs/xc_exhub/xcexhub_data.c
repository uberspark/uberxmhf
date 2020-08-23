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


#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
// #include <xmhfgeec.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_exhub.h>

// IDT
__attribute__((section(".data"))) __attribute__(( aligned(16) )) idtentry_t xcexhub_idt_data[EMHF_XCPHANDLER_MAXEXCEPTIONS] ;
// IDT descriptor
__attribute__((section(".data"))) __attribute__(( aligned(16) )) arch_x86_idtdesc_t xcexhub_idt = {
	.size=sizeof(xcexhub_idt_data)-1,
	.base=(uint32_t)&xcexhub_idt_data,
};


//list of exception handlers
__attribute__((section(".data"))) uint32_t xcexhub_excp_handlers[EMHF_XCPHANDLER_MAXEXCEPTIONS] = {
		(uint32_t)&__xmhf_exception_handler_0,
		(uint32_t)&__xmhf_exception_handler_1,
		(uint32_t)&__xmhf_exception_handler_2,
		(uint32_t)&__xmhf_exception_handler_3,
		(uint32_t)&__xmhf_exception_handler_4,
		(uint32_t)&__xmhf_exception_handler_5,
		(uint32_t)&__xmhf_exception_handler_6,
		(uint32_t)&__xmhf_exception_handler_7,
		(uint32_t)&__xmhf_exception_handler_8,
		(uint32_t)&__xmhf_exception_handler_9,
		(uint32_t)&__xmhf_exception_handler_10,
		(uint32_t)&__xmhf_exception_handler_11,
		(uint32_t)&__xmhf_exception_handler_12,
		(uint32_t)&__xmhf_exception_handler_13,
		(uint32_t)&__xmhf_exception_handler_14,
		(uint32_t)&__xmhf_exception_handler_15,
		(uint32_t)&__xmhf_exception_handler_16,
		(uint32_t)&__xmhf_exception_handler_17,
		(uint32_t)&__xmhf_exception_handler_18,
		(uint32_t)&__xmhf_exception_handler_19,
		(uint32_t)&__xmhf_exception_handler_20,
		(uint32_t)&__xmhf_exception_handler_21,
		(uint32_t)&__xmhf_exception_handler_22,
		(uint32_t)&__xmhf_exception_handler_23,
		(uint32_t)&__xmhf_exception_handler_24,
		(uint32_t)&__xmhf_exception_handler_25,
		(uint32_t)&__xmhf_exception_handler_26,
		(uint32_t)&__xmhf_exception_handler_27,
		(uint32_t)&__xmhf_exception_handler_28,
		(uint32_t)&__xmhf_exception_handler_29,
		(uint32_t)&__xmhf_exception_handler_30,
		(uint32_t)&__xmhf_exception_handler_31
};

