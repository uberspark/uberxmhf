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
 * EMHF exception handler component low-level stubs
 */

#include <xmhf.h>
#include <xmhf-xcphandler.h>

.altmacro
.macro XtRtmEmitIdtStub vector skip_err_code
    .section .text

    //notes:
    //1. we only handle exceptions (0-31) and nothing else
    //2. descriptor type for all exception handlers are 0x8E
    //   i.e., they are all interrupt gates, so when we get called
    //   EFLAGS.IF = 0 (interrupts disabled)
    //3. there are no stack switches as everything in the hypervisor
    //   is CPL=0
    //4. stack layout is as follows when we enter
    //   EFLAGS (32-bits)
    //   CS     (32-bits)
    //   EIP    (32-bits)
    //   error-code (32-bits, depends on the exception)

    XtRtmIdtStub&vector&:

        // push GPR values on stack to construct struct regs *r
        pushq   %rax
        pushq   %rcx
        pushq   %rdx
        pushq   %rbx
        pushq   %rsp
        pushq   %rbp
        pushq   %rsi
        pushq   %rdi
        pushq   %r8
        pushq   %r9
        pushq   %r10
        pushq   %r11
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15

        /* We want %rsp to be the value before the first push */
        addq $(4 * 8), 88(%rsp)

        movq    %rsp, %rsi          // RSI (second argument) = struct regs *
        movq    $0x&vector&, %rdi   // RDI (first argument) = vector
        call    xmhf_xcphandler_hub // call C-land hub

        // pop GPR values, except RSP
        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %r11
        popq    %r10
        popq    %r9
        popq    %r8
        popq    %rdi
        popq    %rsi
        popq    %rbp
        leaq    8(%rsp), %rsp
        popq    %rbx
        popq    %rdx
        popq    %rcx
        popq    %rax

        /* If the exception puts an error code on the stack, ignore it */
        .if &skip_err_code&
        leaq    8(%rsp), %rsp
        .endif

        // return from exception
        iretq

.endm

XtRtmEmitIdtStub 0  0
XtRtmEmitIdtStub 1  0
XtRtmEmitIdtStub 2  0
XtRtmEmitIdtStub 3  0
XtRtmEmitIdtStub 4  0
XtRtmEmitIdtStub 5  0
XtRtmEmitIdtStub 6  0
XtRtmEmitIdtStub 7  0
XtRtmEmitIdtStub 8  1
XtRtmEmitIdtStub 9  0
XtRtmEmitIdtStub a  1
XtRtmEmitIdtStub b  1
XtRtmEmitIdtStub c  1
XtRtmEmitIdtStub d  1
XtRtmEmitIdtStub e  1
XtRtmEmitIdtStub f  0
XtRtmEmitIdtStub 10 0
XtRtmEmitIdtStub 11 1
XtRtmEmitIdtStub 12 0
XtRtmEmitIdtStub 13 0
XtRtmEmitIdtStub 14 0
XtRtmEmitIdtStub 15 0
XtRtmEmitIdtStub 16 0
XtRtmEmitIdtStub 17 0
XtRtmEmitIdtStub 18 0
XtRtmEmitIdtStub 19 0
XtRtmEmitIdtStub 1a 0
XtRtmEmitIdtStub 1b 0
XtRtmEmitIdtStub 1c 0
XtRtmEmitIdtStub 1d 0
XtRtmEmitIdtStub 1e 0
XtRtmEmitIdtStub 1f 0


.section .data
    //EMHF interrupt descriptor table
    .global xmhf_xcphandler_idt
    xmhf_xcphandler_idt:
    .word xmhf_xcphandler_idt_end - xmhf_xcphandler_idt_start
    .quad xmhf_xcphandler_idt_start
    .align 16
    .global xmhf_xcphandler_idt_start
    xmhf_xcphandler_idt_start:
    .fill   (EMHF_XCPHANDLER_MAXEXCEPTIONS * 16), 1, 0
    xmhf_xcphandler_idt_end:


    .align 16
    .global xmhf_xcphandler_exceptionstubs
    xmhf_xcphandler_exceptionstubs:
    .quad XtRtmIdtStub0
    .quad XtRtmIdtStub1
    .quad XtRtmIdtStub2
    .quad XtRtmIdtStub3
    .quad XtRtmIdtStub4
    .quad XtRtmIdtStub5
    .quad XtRtmIdtStub6
    .quad XtRtmIdtStub7
    .quad XtRtmIdtStub8
    .quad XtRtmIdtStub9
    .quad XtRtmIdtStuba
    .quad XtRtmIdtStubb
    .quad XtRtmIdtStubc
    .quad XtRtmIdtStubd
    .quad XtRtmIdtStube
    .quad XtRtmIdtStubf
    .quad XtRtmIdtStub10
    .quad XtRtmIdtStub11
    .quad XtRtmIdtStub12
    .quad XtRtmIdtStub13
    .quad XtRtmIdtStub14
    .quad XtRtmIdtStub15
    .quad XtRtmIdtStub16
    .quad XtRtmIdtStub17
    .quad XtRtmIdtStub18
    .quad XtRtmIdtStub19
    .quad XtRtmIdtStub1a
    .quad XtRtmIdtStub1b
    .quad XtRtmIdtStub1c
    .quad XtRtmIdtStub1d
    .quad XtRtmIdtStub1e
    .quad XtRtmIdtStub1f
