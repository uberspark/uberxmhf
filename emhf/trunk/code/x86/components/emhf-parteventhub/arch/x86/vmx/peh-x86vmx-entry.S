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

//peh-x86vmx-entry.S
//entry point for EMHF partition event-hub component for Intel x86 vmx
//author: amit vasudevan (amitvasudevan@acm.org)
#include <emhf.h>

//----------------------------------------------------------------------
//globals referenced
	.extern g_midtable_numentries
	.extern g_midtable
	.extern vmx_intercept_handler

//----------------------------------------------------------------------
//macros to save and restore GPRs
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


//----------------------------------------------------------------------
// emhf_parteventhub_entry_x86vmx
// we get control here right after any event within a partition
// note: the h/w is the "caller" so we never actually "return"
.section .text
.global emhf_parteventhub_entry_x86vmx
emhf_parteventhub_entry_x86vmx:
	//step-1: save all CPU GPRs
	SAVEALL_GPRS
	      
    //step-2: get hold of local APIC id
    mov $(MSR_APIC_BASE), %ecx
    rdmsr
    andl $0xFFFFF000, %eax
    addl $0x20, %eax
    movl (%eax), %eax
    shr $24, %eax

    //step-3: get VCPU * for this CPU/core
    movl g_midtable_numentries, %edx
    movl $(g_midtable), %ebx
    xorl %ecx, %ecx
    getvcpuloop:
        movl 0x0(%ebx, %ecx, 8), %ebp  //ebp contains the lapic id
        cmpl %eax, %ebp
        jz gotvcpu
        incl %ecx
        cmpl %edx, %ecx
        jb getvcpuloop
        //we should never get here, if so just halt
        hlt
    gotvcpu:
		movl 0x4(%ebx, %ecx, 8), %esi //esi contains vcpu pointer

   	//step-4: get hold of pointer to saved GPR on stack
   	movl %esp, %eax

	//step-5: invoke "C" event handler
   	//1st argument is VCPU * followed by pointer to saved GPRs
	pushl %eax
	pushl %esi
	call vmx_intercept_handler
    addl $0x08, %esp

    //step-6; restore all CPU GPRs
      RESTOREALL_GPRS

    //resume partition
    vmresume
              
    //if we get here then vm resume failed, just bail out with a BP exception 
    int $0x03
    hlt
  
  
