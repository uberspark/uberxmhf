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

// islayer low-level support for VMX
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>

//---globals and externs referenced by this module------------------------------------------
.extern x_gdt_start

.section .text

/*
 * Template for performing VM entry.
 * inst is the instruction for VM entry (VMLAUNCH or VMRESUME).
 * is_vmresume an integer indicating whether inst is VMRESUME.
 */

.altmacro
.macro __vmx_vmentry_template inst is_vmresume

.global __vmx_vmentry_&inst

__vmx_vmentry_&inst:

    //set up registers
#ifdef __AMD64__
    movq    %rdi, %rsp
    POPAQ
#elif defined(__I386__)
    movl    4(%esp), %esp
    popal
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */

    //perform VM entry
    inst

    //if we get here then some error happened during the launch

    //there are two possible causes of failure, VMFailInvalid or
    //VMFailValid (VM instruction error field contains the error code)
    //check which happened and return appropriate value in eax
    jc      0f
    jnz     2f

    movl    $0x1, %eax      // VMfailInvalid
    jmp     3f

2:
    movl    $0x2, %eax      // VMsucceed (violation of specs)
    jmp     3f

0:
    xorl    %eax, %eax      // VMfailValid

3:
    /*
     * Call C function __vmx_vmentry_fail_callback() to report error to user.
     * 1st argument is 0 for VMLAUNCH, 1 for VMRESUME.
     * 2nd argument is 0 for VMfailValid, 1 for VMfailInvalid, 2 for VMsucceed.
     */
#ifdef __AMD64__
    movl    %eax, %esi
    movl    $0, %edi
#elif defined(__I386__)
    pushl   %eax
    pushl   $0
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
    call    __vmx_vmentry_fail_callback
1:  hlt
    jmp     1b

.endm

/* Define __vmx_vmentry_vmlaunch() */
__vmx_vmentry_template vmlaunch 0

/* Define __vmx_vmentry_vmresume() */
__vmx_vmentry_template vmresume 1

