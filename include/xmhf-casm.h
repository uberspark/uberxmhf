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



#define _NUM_ARGS(X8, X7, X6, X5, X4, X3, X2, X1, N, ...)   N

#define NUM_ARGS(...) _NUM_ARGS(__VA_ARGS__, 8, 7, 6, 5, 4, 3, 2, 1)

#define EXPAND(X)       X
#define FIRSTARG(X, ...)    (X)
#define RESTARGS(X, ...)    (__VA_ARGS__)
#define FOREACH(MACRO, LIST)    FOREACH_(NUM_ARGS LIST, MACRO, LIST)
#define FOREACH_(N, M, LIST)    FOREACH__(N, M, LIST)
#define FOREACH__(N, M, LIST)   FOREACH_##N(M, LIST)
#define FOREACH_1(M, LIST)  M LIST
#define FOREACH_2(M, LIST)  EXPAND(M FIRSTARG LIST) FOREACH_1(M, RESTARGS LIST)
#define FOREACH_3(M, LIST)  EXPAND(M FIRSTARG LIST) FOREACH_2(M, RESTARGS LIST)
#define FOREACH_4(M, LIST)  EXPAND(M FIRSTARG LIST) FOREACH_3(M, RESTARGS LIST)
#define FOREACH_5(M, LIST)  EXPAND(M FIRSTARG LIST) FOREACH_4(M, RESTARGS LIST)
#define FOREACH_6(M, LIST)  EXPAND(M FIRSTARG LIST) FOREACH_5(M, RESTARGS LIST)
#define FOREACH_7(M, LIST)  EXPAND(M FIRSTARG LIST) FOREACH_6(M, RESTARGS LIST)
#define FOREACH_8(M, LIST)  EXPAND(M FIRSTARG LIST) FOREACH_7(M, RESTARGS LIST)

#define CASM_LABEL(x)   __builtin_annot(#x": ");
#define CASM_BALIGN(x)  __builtin_annot(".balign "#x" ");

#define CASM_NOPARAM        NULL

#define CASM_FUNCDECL(x)    x

#define CASM_FUNCDEF_FULL(fn_section, fn_align, fn_rettype, fn_name, fn_body, ...) \
    void __casmdef_##fn_name(void){ \
        __builtin_annot(".section "#fn_section); \
        __builtin_annot(".align "#fn_align); \
        __builtin_annot(".global "#fn_name); \
        __builtin_annot(#fn_name": "); \
    } \
    fn_rettype fn_name (__VA_ARGS__) \
    { \
    fn_body \
    } \

#define CASM_FUNCDEF(fn_rettype, fn_name, fn_body, ...) \
    CASM_FUNCDEF_FULL(.text, 0x4, fn_rettype, fn_name, fn_body, __VA_ARGS__) \

#if defined (__XMHF_VERIFICATION__)
    #define CASM_FUNCCALL_PARAM(X)    to_be_added(X),
#else
    #define CASM_FUNCCALL_PARAM(X)
#endif // defined

#define CASM_FUNCCALL(fn_name, ...)   (\
    FOREACH(CASM_FUNCCALL_PARAM, (__VA_ARGS__)) \
    fn_name(__VA_ARGS__) \
    )\



#endif // __ASSEMBLY__

#endif /* __XMHF_CASM_H_ */
