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

// secure loader low-level support routines
// authors: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h> 

.section .text
//------------------------------------------------------------------------------	
	.global emhf_sl_arch_x86_invoke_runtime_entrypoint
emhf_sl_arch_x86_invoke_runtime_entrypoint:
//------------------------------------------------------------------------------
	//turn on paging
	movl	$(0x00000030), %eax	//CR4_PAE | CR4_PSE
	movl	%eax, %cr4
	movl	0x14(%esp), %edi	//EDI = page table base address
	movl	%edi, %cr3			
	movl	$(0x80000015), %eax	 // ET, EM, PE, PG
	movl	%eax, %cr0			 //turn on paging

	//grab gdtbase and idtbase parameters
	movl 	0x4(%esp), %esi
	movl 	0x8(%esp), %edi

	//load runtime gdt and idt
	subl  $0x8, %esp
	
	movw  %fs:(%esi), %ax
	movw  %ax, (%esp)
	movl  %fs:0x2(%esi), %eax
	movl  %eax, 0x2(%esp)

	lgdt	(%esp)

	movw  %fs:(%edi), %ax
	movw  %ax, (%esp)
	movl  %fs:0x2(%edi), %eax
	movl  %eax, 0x2(%esp)
	
	lidt	(%esp)

	addl  $0x8, %esp
	
	//grab entrypoint and topofstack parameters
	movl 	0xC(%esp), %edi
	movl  	0x10(%esp), %esi

	//load runtime segment selectors
	movw	$(__DS), %ax
	movw	%ax, %ds	
	movw	%ax, %es
	movw	%ax, %fs
	movw	%ax, %gs
	
	//initialize runtime stack
	movw  %ax, %ss
	movl  %esi,%esp

	//clear flags
	pushl	$0
	popf
	
	//far jump to runtime entry point
	pushl	$(__CS)
	pushl	%edi
	lret
	
