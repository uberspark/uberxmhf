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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

//------------------------------------------------------------------------------
// v86monitorsup.S
//
// v86 monitor data/stubs
//
// author: amit vasudevan (amitvasudevan@acm.org)
#include <target.h>

.extern v86_handleinterrupt
.altmacro

.macro RUNTIMEV86EMITIDTSTUBS fromvec, tovec
	__runtime_v86_idtstub&\fromvec&:

	pushl %esp
	pushl %eax
	pushl %ebx
	pushl %ecx
	pushl %edx
	pushl %esi
	pushl %edi
	pushl %ebp
	
	
	movw $0x001C, %ax
	movw %ax, %ds
	movw %ax, %es
	
	movl %esp, %eax
  pushl %eax
  pushl $\fromvec
  call v86_handleinterrupt
	addl $0x08, %esp
	
	popl %ebp
	popl %edi
	popl %esi
	popl %edx
	popl %ecx
	popl %ebx
	popl %eax
	popl %esp
	
	
	iretl	//will pop segment registers as well since we are returning to V86

	
  .ifgt    (\tovec - \fromvec)
  RUNTIMEV86EMITIDTSTUBS %(\fromvec+1), \tovec
  .endif
.endm


.macro runtime_v86_emitidtstubs_definitions fromvec, tovec
	.long __runtime_v86_idtstub&fromvec&
  .ifgt     (\tovec-\fromvec)
  runtime_v86_emitidtstubs_definitions %(\fromvec+1),\tovec
  .endif
.endm

.section .text
RUNTIMEV86EMITIDTSTUBS 0, 13
RUNTIMEV86EMITIDTSTUBS 14, 114
RUNTIMEV86EMITIDTSTUBS 115, 215
RUNTIMEV86EMITIDTSTUBS 216, 255

	.extern v86_gpfh
	.extern runtime_printnum
	.global __v86_gpfh_stub
	__v86_gpfh_stub:
	//we get here on a GPF in V86 mode, there could be two
	//cases:
	//case1: a GPF fault was generated to the v86 monitor
	//case2: INT 0D (IRQ 5) was executed
	//for case2 we simply chain to the INT 0D interrupt stub
	
	//determine which case (1 or 2)
	//for case1: the fault frame is 40 bytes including an error code
	//for case2: the int frame is 36 bytes without an error code
	pushl %ebx
	movw $0x001C, %bx
	movw %bx, %ds
	movw %bx, %es
	
	lea __runtime_v86_ring0stack, %ebx
	addl $0x4000, %ebx
	subl %esp, %ebx
	subl $0x4, %ebx
	cmpl $0x24, %ebx
	//cmpl $0xbe42cfdc, %esp
	//jne continuefault
	
	ja continuefault
	//jmp continuefault
	
	//this is a INT 0D IRQ
	popl %ebx
	jmp __runtime_v86_idtstub13
	continuefault:
	
	popl %ebx
	addl $0x4, %esp //pop error code, we dont need it
	pushl %esp
	pushl %eax
	pushl %ebx
	pushl %ecx
	pushl %edx
	pushl %esi
	pushl %edi
	pushl %ebp
	
	
	movl %esp, %eax
  pushl %eax
  call v86_gpfh
	addl $0x04, %esp

	popl %ebp
	popl %edi
	popl %esi
	popl %edx
	popl %ecx
	popl %ebx
	popl %eax
	popl %esp

	iretl	//will pop off segment registers as well as we are going back to V86



.section .data
	.global __runtime_v86_idtfunctionptrs
	__runtime_v86_idtfunctionptrs:
	runtime_v86_emitidtstubs_definitions 0, 13
	runtime_v86_emitidtstubs_definitions 14, 114
	runtime_v86_emitidtstubs_definitions 115, 215
	runtime_v86_emitidtstubs_definitions 216, 255
		
	
.section .vtdata	
	//v86 mode structures
	.global __runtime_v86_pagedir
	__runtime_v86_pagedir:
	.fill 4096, 1, 0
	
	.global __runtime_v86_pagetables
	__runtime_v86_pagetables:
	.fill 4096*1024, 1, 0
	
	.global __runtime_v86_idt
	__runtime_v86_idt:
	.fill 4096, 1, 0
	
	.global __runtime_v86_gdt
	__runtime_v86_gdt:
	.fill 4096, 1, 0
	
	.global __runtime_v86_tss
	__runtime_v86_tss:
	.fill 4096*4, 1, 0
	
	.global __runtime_v86_ldt
	__runtime_v86_ldt:
	.fill 4096, 1, 0
	
	.global __runtime_v86_ring0stack
	__runtime_v86_ring0stack:
	.fill 4096*4, 1, 0
	
//------------------------------------------------------------------------------
