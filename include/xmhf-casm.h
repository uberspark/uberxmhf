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

// xmhf-casm.h - CASM pseudo-language decls.
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHF_CASM_H_
#define __XMHF_CASM_H_

#ifndef __ASSEMBLY__

#if defined (__clang__)

#define CASM_LABEL(x)   asm volatile (#x": \r\n");
#define CASM_BALIGN(x)  asm volatile (".balign "#x" \r\n");

#define CASM_BEGINCODE() \
    static void __casm_begincode(void){ \
    } \

#define CASM_ENDCODE() \
    static void __casm_endcode(void){ \
    } \

#define CASM_FUNCDEF(fn_rettype, fn_name, fn_body, ...) \
    __attribute__((naked)) fn_rettype fn_name (__VA_ARGS__) \
    { \
    fn_body \
    } \

#else //!__clang__

#define CASM_LABEL(x)   __builtin_annot(#x": ");
#define CASM_BALIGN(x)  __builtin_annot(".balign "#x" ");

#define CASM_BEGINCODE() \
    static void __casm_begincode(void){ \
        __builtin_annot(".section .text"); \
    } \

#define CASM_ENDCODE() \
    static void __casm_endcode(void){ \
        __builtin_annot(".section .text"); \
    } \

#define CASM_FUNCDEF(fn_rettype, fn_name, fn_body, ...) \
    void __casmdef_##fn_name(void){ \
        __builtin_annot(".global "#fn_name); \
        __builtin_annot(#fn_name": "); \
    } \
    fn_rettype fn_name (__VA_ARGS__) \
    { \
    fn_body \
    } \


#endif //__clang__


#endif // __ASSEMBLY__

#endif /* __XMHF_CASM_H_ */
