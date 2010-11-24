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

//islayersup.S
//implements supporting low-level routines for isolation layer
//author: amit vasudevan (amitvasudevan@acm.org)

#include <target.h>
#include <msr.h>

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

.extern XtRtmIslInterceptHandler

.section .text

//---startHVM-------------------------------------------------------------------	
//we dont care about saving any CPU GPRs as we enter startHVM
.global startHVM
startHVM:
  movl 0x4(%esp), %ebx  //ebx = vcpu vaddr of current CPU
  movl 0x8(%esp), %eax  //eax = vmcb phys. addr of current CPU

  pushl %ebx            //save vcpu vaddr on top of stack
  
  //real-mode setup just like the BIOS
  movl $0x0, %ebx
	movl $0x0, %ecx
	movl $0x80, %edx
	movl $0x0, %ebp
	movl $0x0, %esi
	movl $0x0, %edi

resumeHVM:	
	//execute the HVM
	//stgi
  vmrun
  //clgi
	//stgi
	
	//we get here due to ANY intecept within the HVM
	//step-1: save all CPU GPRs
	SAVEALL_GPRS
	
	//get a hold of vcpu into ebx
	movl 32(%esp), %ebx
	
	//get hold of pointer to saved GPR on stack
	movl %esp, %eax
	
	//1st argument is vcpu followed by pointer to saved GPRs
	pushl %eax
	pushl %ebx
	call XtRtmIslInterceptHandler
  addl $0x08, %esp

  //restore all CPU GPRs, will also resture eax=phys. addr of vmcb
  RESTOREALL_GPRS

  //resume HVM
  jmp resumeHVM
  
	