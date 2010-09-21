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

// runtime support structures
// author: amit vasudevan (amitvasudevan@acm.org)

#include <target.h>
#include <msr.h>
#include <svm.h>

.altmacro
.macro XtRtmEmitIdtStub vector
	.section .text
	XtRtmIdtStub&vector&:
		pushl	%edi	
    pushl	%esi	
	  pushl	%ebp	
		pushl	%esp  
    pushl	%ebx	
    pushl	%edx	
    pushl	%ecx	
    pushl	%eax	
    
    movw	$(__DS), %ax
		movw	%ax, %ds	
		movl %esp, %eax
		
		pushl %eax
		pushl	$0x&vector&
		call	XtRtmExceptionHandler
		addl  $0x08, %esp
		
		popl	%eax	
    popl	%ecx	
    popl	%edx	
    popl	%ebx	
		popl	%esp	
    popl	%ebp	
    popl	%esi	
    popl	%edi	 
    
    iretl
	
.endm

XtRtmEmitIdtStub 0	
XtRtmEmitIdtStub 1	
XtRtmEmitIdtStub 2	
XtRtmEmitIdtStub 3	
XtRtmEmitIdtStub 4	
XtRtmEmitIdtStub 5	
XtRtmEmitIdtStub 6	
XtRtmEmitIdtStub 7	
XtRtmEmitIdtStub 8	
XtRtmEmitIdtStub 9	
XtRtmEmitIdtStub a	
XtRtmEmitIdtStub b	
XtRtmEmitIdtStub c	
XtRtmEmitIdtStub d	
XtRtmEmitIdtStub e	
XtRtmEmitIdtStub f	
XtRtmEmitIdtStub 10	
XtRtmEmitIdtStub 11	
XtRtmEmitIdtStub 12	
XtRtmEmitIdtStub 13	
XtRtmEmitIdtStub 14	
XtRtmEmitIdtStub 15	
XtRtmEmitIdtStub 16	
XtRtmEmitIdtStub 17	
XtRtmEmitIdtStub 18	
XtRtmEmitIdtStub 19	
XtRtmEmitIdtStub 1a	
XtRtmEmitIdtStub 1b	
XtRtmEmitIdtStub 1c	
XtRtmEmitIdtStub 1d	
XtRtmEmitIdtStub 1e	
XtRtmEmitIdtStub 1f	


	.extern cstartup
	
	
	
	.section .s_xtlpb
	.global _xtlpb
_xtlpb:
	.long cstartup
	.long xtrac_3level_pdpt
	.long	xtrac_3level_pdt
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long x_init_stack
	.long 8192
	.long x_gdt
	.long 0 //.extern nwadapterstructure
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long x_idt
	.long x_idt_functionpointers
	.long 32
	.long 0 //x_e1000desc
	.long 0 //x_e1000header
	.long 0 //x_e1000body
  .global __ha
  __ha:
	.long 0  //physical base address of runtime
	.long 0  //virtual base address of runtime
	.long 0  //2M aligned size of runtime
	.long __grube820buffer   //GRUB E820 map
	.long 0                  //number of entries
	.long __mp_cpuinfo       //MP cpu information
	.long 0                  //number of entries
	
	.section .data
	x_gdt:
	.word	x_gdt_end - x_gdt_start - 1	
	.long	x_gdt_start

	.align	16
	x_gdt_start:
	.quad	0x0000000000000000	
	.quad	0x00cf9a000000ffff	
	.quad	0x00cf92000000ffff	
	.quad	0x0000000000000000	
	x_gdt_end:

	//IDT
	x_idt:
	.word x_idt_end - x_idt_start - 1
	.long x_idt_start
	.align 16
	x_idt_start:
	.fill	8*32, 1, 0
	x_idt_end:
	.align 16
	x_idt_functionpointers:
	.long XtRtmIdtStub0
	.long XtRtmIdtStub1
	.long XtRtmIdtStub2
	.long XtRtmIdtStub3
	.long XtRtmIdtStub4
	.long XtRtmIdtStub5
	.long XtRtmIdtStub6
	.long XtRtmIdtStub7
	.long XtRtmIdtStub8
	.long XtRtmIdtStub9
	.long XtRtmIdtStuba
	.long XtRtmIdtStubb
	.long XtRtmIdtStubc
	.long XtRtmIdtStubd
	.long XtRtmIdtStube
	.long XtRtmIdtStubf
	.long XtRtmIdtStub10
	.long XtRtmIdtStub11
	.long XtRtmIdtStub12
	.long XtRtmIdtStub13
	.long XtRtmIdtStub14
	.long XtRtmIdtStub15
	.long XtRtmIdtStub16
	.long XtRtmIdtStub17
	.long XtRtmIdtStub18
	.long XtRtmIdtStub19
	.long XtRtmIdtStub1a
	.long XtRtmIdtStub1b
	.long XtRtmIdtStub1c
	.long XtRtmIdtStub1d
	.long XtRtmIdtStub1e
	.long XtRtmIdtStub1f
	
	
	.global __grube820buffer
  __grube820buffer:
	.fill SIZE_STRUCT_GRUBE820 * MAX_E820_ENTRIES, 1, 0
	
	.global __mp_cpuinfo
	__mp_cpuinfo:
	.fill SIZE_STRUCT_PCPU * MAX_PCPU_ENTRIES, 1, 0
	
	
	.section .stack
	.global x_init_stack
x_init_stack:
	.fill	8192, 1, 0

  //runtime stacks for individual CPUs
  .global __cpustacks
  __cpustacks:
  .fill RUNTIME_STACK_SIZE * MAX_PCPU_ENTRIES, 1, 0

  .section .data
  .align 4
  .global __vcpubuffers
  __vcpubuffers:
  .fill SIZE_STRUCT_VCPU * MAX_VCPU_ENTRIES, 1, 0
  
	
	.section	.svmdata
	.align 4096
	//page tables for the runtime
  xtrac_3level_pdpt:
		.fill 4096, 1, 0
	.global xtrac_3level_pdt
	xtrac_3level_pdt:
		.fill 4*4096, 1, 0



	//virtual LAPIC page for BSP to track SIPI
	.global virtual_LAPIC_base
	virtual_LAPIC_base:
	 .fill 4096, 1, 0

  //nested page tables for CPUs
  .global svm_npt_pdpt_buffers
  svm_npt_pdpt_buffers:
    .fill 4096 * MAX_VCPU_ENTRIES, 1, 0
  
  .global svm_npt_pdts_buffers
  svm_npt_pdts_buffers:
    .fill (4*4096)* MAX_VCPU_ENTRIES, 1, 0

	.global svm_npt_pts_buffers
	svm_npt_pts_buffers:
		.fill (2048*4096) * MAX_VCPU_ENTRIES, 1, 0

  //sipi pages for CPUs
  .global svm_sipi_page_buffers
  svm_sipi_page_buffers:
    .fill 4096 * MAX_VCPU_ENTRIES, 1, 0

  //VM_HSAVE buffers for CPUs
  .global svm_hsave_buffers
  svm_hsave_buffers:
  .fill 8192 * MAX_VCPU_ENTRIES, 1, 0
  
  //VMCB buffers for CPUs
  .global svm_vmcb_buffers
  svm_vmcb_buffers:
  .fill 8192 * MAX_VCPU_ENTRIES, 1, 0 

  //IOPM buffer for CPUs
  .global svm_iopm
	svm_iopm:
		.fill	SIZEOF_IOPM_BITMAP, 1, 0

  //MSRPM buffer for CPUs
  .global svm_msrpm
  svm_msrpm:
    .fill SIZEOF_MSRPM_BITMAP, 1, 0


//---AP boot-strap code---------------------------------------------------------
.section .text
  .code16
  .global _ap_bootstrap_start
  _ap_bootstrap_start:
    jmp ap_bootstrap_bypassdata
    _ap_gdtdesc:
      .word _ap_gdt_end - _ap_gdt_start - 1
      .long _ap_gdt_start - _ap_bootstrap_start + 0x10000  
    .global _ap_cr3_value
    _ap_cr3_value:
      .long 0
    .global _ap_cr4_value
    _ap_cr4_value: 
      .long 0
    .align 16
    _ap_gdt_start:
      .quad 0x0000000000000000
      .quad	0x00cf9a000000ffff	
	    .quad	0x00cf92000000ffff
    _ap_gdt_end:
      .word 0
  ap_bootstrap_bypassdata:
      movw $0x1000, %ax
    	movw %ax, %ds
    	movw %ax, %es
    	movw $0xFFFF, %sp
    	movw $0x4000, %ax
    	movw %ax, %ss
    	
    	movw $0x0002, %si

      lgdt (%si)

      movl %cr0, %eax
      orl $0x1, %eax
      movl %eax, %cr0

      jmpl $0x08, $(_ap_clear_pipe - _ap_bootstrap_start + (AP_BOOTSTRAP_CODE_SEG << 4))
    .code32
    _ap_clear_pipe:
      movw $0x10, %ax
      movw %ax, %ds
      movw %ax, %es
      movw %ax, %ss

      // inserted by Jon to clear AP microcode
      //movl $MSR_AMD64_PATCH_CLEAR, %ecx
      //wrmsr // eax and edx ignored
              
      movl $(_ap_cr3_value - _ap_bootstrap_start + (AP_BOOTSTRAP_CODE_SEG << 4)), %esi
      movl (%esi), %ebx
      movl %ebx, %cr3
      movl $(_ap_cr4_value - _ap_bootstrap_start + (AP_BOOTSTRAP_CODE_SEG << 4)), %esi
      movl (%esi), %ebx
      movl %ebx, %cr4
      
      movl %cr0, %eax
      orl $0x80000000, %eax
      movl %eax, %cr0

      movl $_ap_pmode_entry_with_paging, %eax
      jmpl *%eax
      hlt
      
  .global _ap_bootstrap_end
  _ap_bootstrap_end:
    nop
    nop
    nop
    nop

//------------------------------------------------------------------------------    
.section  .data
  .align 8
  .global __midtable
  __midtable:
  .fill (SIZE_STRUCT_MIDTAB * MAX_MIDTAB_ENTRIES), 1, 0

.extern allcpus_common_start
.extern midtable_numentries

.section .text
  .global _ap_pmode_entry_with_paging
  _ap_pmode_entry_with_paging:
    //load our gdt and idt
    lgdt x_gdt
    lidt x_idt
    
    
    //get hold of local APIC id
    mov $(MSR_APIC_BASE), %ecx
    rdmsr
    andl $0xFFFFF000, %eax
    addl $0x20, %eax
    movl (%eax), %eax
    shr $24, %eax

    movl midtable_numentries, %edx
    
    //get vcpu virtual address of this CPU/core
    movl $(__midtable), %ebx
    xorl %ecx, %ecx
getvcpuloop:
    movl 0x0(%ebx, %ecx, SIZE_STRUCT_MIDTAB), %ebp  //ebp contains the lapic id
    cmpl %eax, %ebp
    jz gotvcpu
    incl %ecx
    cmpl %edx, %ecx
    jb getvcpuloop
    //we should never get here, if so just halt
    hlt
gotvcpu:
   movl 0x4(%ebx, %ecx, SIZE_STRUCT_MIDTAB), %esi //esi contains vcpu pointer
   movl 0x0(%esi), %esp     //load stack for this CPU
   pushl %esi
   call allcpus_common_start
   //we should never get here, if so just halt
   hlt  

//---spinlock/unlock------------------------------------------------------------
.section .text
  .global spin_lock
  spin_lock:
    pushl %esi
    movl 0x8(%esp), %esi
    spin:	bt	$0, (%esi)		//mutex is available?
      	jnc	spin			      //wait till it is

      	lock				        //lock the bus (exclusive access)	
	      btr	$0, (%esi)		    //and try to grab the mutex	
	      jnc	spin			      //spin until successful --> spinlock :p
    popl %esi
    ret
    
  .global spin_unlock
  spin_unlock:
      pushl %esi
      movl 0x8(%esp), %esi
      bts	$0, (%esi)		       //release the spinlock
      popl %esi
      ret


      		
