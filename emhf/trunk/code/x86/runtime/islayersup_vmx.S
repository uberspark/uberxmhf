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

// islayer low-level support for VMX
// author: amit vasudevan (amitvasudevan@acm.org)

#include <target.h>


//---globals referenced by this module------------------------------------------
.extern vmx_intercept_handler
.extern g_midtable_numentries
.extern g_midtable
.extern x_gdt_start

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


.section .text
	.global __vmx_callback
	__vmx_callback:
       	//we get here due to ANY intecept within the HVM
      	//step-1: save all CPU GPRs
	      SAVEALL_GPRS
	      
        //get hold of local APIC id
        mov $(MSR_APIC_BASE), %ecx
        rdmsr
        andl $0xFFFFF000, %eax
        addl $0x20, %eax
        movl (%eax), %eax
        shr $24, %eax

        movl g_midtable_numentries, %edx
    
        //get vcpu virtual address of this CPU/core
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

       	//get hold of pointer to saved GPR on stack
      	movl %esp, %eax

      	//1st argument is vcpu followed by pointer to saved GPRs
	     pushl %eax
	     pushl %esi
	     call vmx_intercept_handler
       addl $0x08, %esp

      //restore all CPU GPRs
      RESTOREALL_GPRS

      //resume HVM
      vmresume
              
      //if we get here then vm resume failed, just bail out with a BP exception 
      int $0x03
      hlt
  
  
   
.section .text
  .global __vmx_start_hvm
  __vmx_start_hvm:
   //real-mode setup just like the BIOS
   pushal
   
   movl $0x0, %eax
   movl $0x0, %ebx
	 movl $0x0, %ecx
   movl $0x80, %edx
	 movl $0x0, %ebp
	 movl $0x0, %esi
	 movl $0x0, %edi
	 
	 vmlaunch
	 
	 //if we get here then some error happened during the launch
	 popal
	 ret


//---__vmx_loadTR---------------------------------------------------------------
//loads TR on the core   
.section .text
  .global __vmx_loadTR
  __vmx_loadTR:

	pushal  
  
	//load TR
	//note: we MUST clear the TSS descriptor "busy" bit before issuing
	//the LTR instruction on Intel cores, else we will #GPF.  
	movl $(x_gdt_start), %edi
	xorl %eax, %eax
	movw $(__TRSEL), %ax
	addl %eax, %edi				//%edi is pointer to TSS descriptor in GDT
	addl $0x4, %edi				//%edi points to top 32-bits of 64-bit TSS desc.
	lock andl $0xFFFF00FF, (%edi)
	lock orl  $0x00008900, (%edi)  
	ltr %ax								//load TR

	popal
	ret
