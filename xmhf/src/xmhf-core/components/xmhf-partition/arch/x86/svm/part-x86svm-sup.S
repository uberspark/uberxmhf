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

//islayersup_svm.S
//implements supporting low-level routines for SVM isolation layer
//author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h> 

//---globals referenced by this module------------------------------------------
.extern g_midtable_numentries
.extern g_midtable
.extern emhf_parteventhub_arch_x86svm_entry

#define SAVEALL_GPRS \
        pushl	%edi	; \
        pushl	%esi	; \
				pushl	%ebp	; \
				pushl	%esp    ; \
        pushl	%ebx	; \
        pushl	%edx	; \
        pushl	%ecx	; \
        pushl	%eax	; 
	
#define RESTOREALL_GPRS \
				popl	%eax	; \
        popl	%ecx	; \
        popl	%edx	; \
        popl	%ebx	; \
				popl	%esp	; \
        popl	%ebp	; \
        popl	%esi	; \
        popl	%edi	; 

.extern svm_intercept_handler

.section .text

//---__svm_start_hvm------------------------------------------------------------	
//we dont care about saving any CPU GPRs as we enter startHVM
.global __svm_start_hvm
__svm_start_hvm:
  movl 0x4(%esp), %ebx  //ebx = vcpu vaddr of current CPU
  movl 0x8(%esp), %eax  //eax = vmcb phys. addr of current CPU

	//XX: save vcpu vaddr
	pushl %ebx

  //real-mode setup just like the BIOS
  movl $0x0, %ebx
	movl $0x0, %ecx
	movl $0x80, %edx
	movl $0x0, %ebp
	movl $0x0, %esi
	movl $0x0, %edi

__svm_resume_hvm:	
	//execute the HVM
	//stgi
  vmrun
	//clgi
	//stgi

	//invoke EMHF partition event-hub entry-point
	call emhf_parteventhub_arch_x86svm_entry
	
	//resume HVM
	jmp __svm_resume_hvm
  
	
