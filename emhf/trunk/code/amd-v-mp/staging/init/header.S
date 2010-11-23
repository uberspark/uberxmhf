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

#include <target.h>

	.section .multiboot_header

	.align 4
	.global multiboot_header
multiboot_header:
	.long 0x1BADB002
	.long 0x10003
	.long	-(0x1BAEB005) 
	.long multiboot_header
	.long multiboot_header
	.long 0
	.long 0
	.long init_start
	.long 0
	.long 0
	.long 0
	.long 0
	
	.extern cstartup
	.section .text
	.global init_start
init_start:
	
	movl    $(init_stack + 8192), %esp
     
  pushl   $0
  popf
     
  pushl   %ebx
  //pushl   %eax
     
	call cstartup
	
halt:
	hlt
	jmp halt
	
//------------------------------------------------------------------------------	
	.global XtLdrTransferControlToRtm
XtLdrTransferControlToRtm:
//------------------------------------------------------------------------------
	movl 	0x4(%esp), %esi
	movl 	0x8(%esp), %edi

	subl  0x8, %esp
	
	movw  (%esi), %ax
	movw  %ax, (%esp)
	movl  0x2(%esi), %eax
	movl  %eax, 0x2(%esp)
	
	lgdt	(%esp)

	movw  (%edi), %ax
	movw  %ax, (%esp)
	movl  0x2(%edi), %eax
	movl  %eax, 0x2(%esp)
	
	lidt	(%esp)

	addl  0x8, %esp
	
	movw	$(__DS), %ax
	movw	%ax, %ds	
	movw	%ax, %es
	movw	%ax, %fs
	movw	%ax, %gs
	ljmp	$(__CS), $(1f)
1:

	pushl	$0
	popf

	movl 	0xC(%esp), %edi
	movl  0x10(%esp), %esi
	
	movl  %esi,  %esp
	
	jmpl *%edi
	
	
	.section .stack
	.global init_stack
init_stack:
	.fill	8192, 1, 0
	
