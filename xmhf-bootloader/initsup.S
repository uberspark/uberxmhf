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

// init low-level support routines
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h> 

.extern midtable_numentries
.extern mp_cstartup
.extern midtable

//---AP boot-strap code---------------------------------------------------------
.section .text
  .code16
  .global _ap_bootstrap_start
  _ap_bootstrap_start:
    jmp ap_bootstrap_bypassdata
    _ap_gdtdesc:
      .word _ap_gdt_end - _ap_gdt_start - 1
      .long _ap_gdt_start - _ap_bootstrap_start + 0x10000  
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
      movw %ax, %fs
      movw %ax, %gs

      movl $init_core_lowlevel_setup, %eax
      jmpl *%eax
      hlt
      
  .global _ap_bootstrap_end
  _ap_bootstrap_end:
    nop
    nop
    nop
    nop

//---init_core_lowlevel_setup---------------------------------------------------
.section .text
  .global init_core_lowlevel_setup
  init_core_lowlevel_setup:
    
	//load our gdt 
  lgdt init_gdt
    
  //get hold of local APIC id
  mov $(MSR_APIC_BASE), %ecx
  rdmsr
  andl $0xFFFFF000, %eax
  addl $0x20, %eax
  movl (%eax), %eax
  shr $24, %eax

  movl midtable_numentries, %edx
    
  //get vcpu virtual address of this CPU/core
    movl $(midtable), %ebx
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
   movl 0x0(%esi), %esp     //load stack for this CPU
   pushl %esi
   call mp_cstartup
   //we should never get here, if so just halt
   hlt  



//------------------------------------------------------------------------------
.section  .data
      		
	//the GDT
	init_gdt:
	.word	init_gdt_end - init_gdt_start - 1	
	.long	init_gdt_start

	.align	16
	init_gdt_start:
	.quad	0x0000000000000000	
	.quad	0x00cf9a000000ffff	
	.quad	0x00cf92000000ffff	
	.quad	0x0000000000000000	
	init_gdt_end:



              
