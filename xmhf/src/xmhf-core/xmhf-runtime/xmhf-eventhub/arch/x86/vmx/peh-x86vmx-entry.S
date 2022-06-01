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

//peh-x86vmx-entry.S
//entry point for EMHF partition event-hub component for Intel x86 vmx
//author: amit vasudevan (amitvasudevan@acm.org)
#include <xmhf.h>

//----------------------------------------------------------------------
//globals referenced
    .extern xmhf_parteventhub_arch_x86vmx_intercept_handler

//----------------------------------------------------------------------
// xmhf_parteventhub_entry_x86vmx
// we get control here right after any event within a partition
// note: the h/w is the "caller" so we never actually "return"
.section .text
.global xmhf_parteventhub_arch_x86vmx_entry
xmhf_parteventhub_arch_x86vmx_entry:
    // Currently esp / rsp points to VCPU

#ifdef __AMD64__
    /* save all CPU GPRs */
    PUSHAQ
    /* grab VCPU *, put to 1st argument */
    movq 128(%rsp), %rdi
    /* get hold of pointer to saved GPR on stack, put to 2nd argument */
    movq %rsp, %rsi
#elif defined(__I386__)
    /* save all CPU GPRs */
    pushal
    /* grab VCPU * */
    movl 32(%esp), %edi
    /* get hold of pointer to saved GPR on stack, put to 2nd argument */
    pushl %esp
    /* put VCPU * to 1st argument */
    pushl %edi
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */

    /* invoke "C" event handler */
    call xmhf_parteventhub_arch_x86vmx_intercept_handler

#ifdef __AMD64__
    /* restore all CPU GPRs */
    POPAQ
#elif defined(__I386__)
    /* adjust ESP following i386 calling convention */
    addl $0x08, %esp
    /* restore all CPU GPRs */
    popal
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */

    //resume partition
    vmresume

    //if we get here then vm resume failed, just bail out with a BP exception
    int $0x03
    hlt
