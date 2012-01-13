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

// secure loader low-level support routines
// authors: amit vasudevan (amitvasudevan@acm.org)

#include <emhf.h> 

.section .text
//------------------------------------------------------------------------------	
	.global XtLdrTransferControlToRtm
XtLdrTransferControlToRtm:
//------------------------------------------------------------------------------
	//turn on paging
	movl	$(0x00000030), %eax	//CR4_PAE | CR4_PSE
	movl	%eax, %cr4
	movl	0x14(%esp), %edi	//EDI = page table base address
	movl	%edi, %cr3			
	movl	$(0x80000015), %eax	 // ET, EM, PE, PG
	movl	%eax, %cr0			 //turn on paging

	movl 	0x4(%esp), %esi
	movl 	0x8(%esp), %edi

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
	
	
	
	movl 	0xC(%esp), %edi
	movl  0x10(%esp), %esi

	movw	$(__DS), %ax
	movw	%ax, %ds	
	movw	%ax, %es
	movw	%ax, %fs
	movw	%ax, %gs
	
	movw  %ax, %ss
  movl  %esi,%esp

	pushl	$0
	popf
	
	
//we will patch the entrypoint to the hypervisor runtime before
//transfering control. not the most elegant approach, but since our
//sl CS is segmented, the flat runtime CS can only be reloaded with
//a far selector:offset jump and x86 doesnt have an indirect variant
//of this instruction 
.global	sl_runtime_entrypoint_patch
	sl_runtime_entrypoint_patch:	
	jmp $(__CS), $(0x00000000)

