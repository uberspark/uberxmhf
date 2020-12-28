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

#ifndef __XC_EXHUB_H__
#define __XC_EXHUB_H__

#define UAPI_XCEXHUB_DEBUG     	1
#define UAPI_XCEXHUB_SETUPIDT	2
#define UAPI_XCEXHUB_LOADIDT	3
#define UAPI_XCEXHUB_LOADHOSTIDTRBASE 4

#ifndef __ASSEMBLY__

extern __attribute__((section(".data"))) __attribute__(( aligned(16) )) idtentry_t xcexhub_idt_data[EMHF_XCPHANDLER_MAXEXCEPTIONS]; //ro
extern __attribute__((section(".data"))) __attribute__(( aligned(16) )) arch_x86_idtdesc_t xcexhub_idt; //ro
extern __attribute__((section(".data"))) uint32_t xcexhub_excp_handlers[EMHF_XCPHANDLER_MAXEXCEPTIONS];


CASM_FUNCDECL(void __xmhf_exception_handler_0(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_1(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_2(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_3(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_4(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_5(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_6(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_7(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_8(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_9(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_10(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_11(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_12(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_13(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_14(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_15(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_16(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_17(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_18(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_19(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_20(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_21(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_22(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_23(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_24(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_25(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_26(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_27(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_28(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_29(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_30(void *noparam));
CASM_FUNCDECL(void __xmhf_exception_handler_31(void *noparam));

void xcexhub_entryexcp(x86vmx_exception_frame_t *exframe);
CASM_FUNCDECL(void xcexhub_retexcp(x86vmx_exception_frame_t *exframe));
void xcexhub_excpmain(slab_params_t *sp);

void xcexhub_setupidt(void);


#endif //__ASSEMBLY__


#endif //__XC_EXHUB_H__
