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

/* secure loader low-level support routines
   authors: amit vasudevan (amitvasudevan@acm.org)
*/

#include <xmhf.h>

.section .text
/*------------------------------------------------------------------------------*/
    .global xmhf_sl_arch_x86_invoke_runtime_entrypoint
xmhf_sl_arch_x86_invoke_runtime_entrypoint:
/*------------------------------------------------------------------------------*/
    /* test whether sla == spa */
    cmpq    $0, %r9
    je      skip_jump

    /* save arguments */
    push    %r9     /* sla2spa(0) */
    push    %r8     /* cr3 */
    push    %rcx    /* stacktop */
    push    %rdx    /* entrypoint */
    push    %rsi    /* idtbase */
    push    %rdi    /* gdtbase */

    /* modify sl page table to be able to jump back */
    movq    $0, %rdi
    call    xmhf_setup_sl_paging

    /* flush TLB */
    movq    %cr3, %rax
    movq    %rax, %cr3

    /* restore arguments */
    pop     %rdi
    pop     %rsi
    pop     %rdx
    pop     %rcx
    pop     %r8
    pop     %r9

    leaq    1f(%r9), %rax   /* physical address of $1f */
    jmpq    *%rax
1:

    skip_jump:

    /* switch to runtime paging */
    movq %r8, %cr3

    /* switch to runtime gdt */
    lgdt (%rdi)
    lidt (%rsi)

    /*
     * the structure of sl GDT and runtime gdt are mostly the same, so no need
     * to change segment etc.
     */

    /* set segment registers (should be no-op) */
    movw    $(__DS), %ax
    movw    %ax, %ss
    movw    %ax, %ds
    movw    %ax, %es
    movw    %ax, %fs
    movw    %ax, %gs

    /* initialize runtime stack */
    movq    %rcx, %rsp

    /* clear flags */
    pushq   $0
    popf

    /* jump to runtime entry point */
    jmpq    *%rdx
