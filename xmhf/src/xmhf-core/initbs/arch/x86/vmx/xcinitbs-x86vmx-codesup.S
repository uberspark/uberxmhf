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

/*
 xcinitbs 16-bit low-level AP bootup code; will be moved into xc-initbs-x86vmx-code.c
 as static data buffer once we are done testing...
*/

	.section .data
	.code16
  .global _ap_bootstrap_blob_defunct
  _ap_bootstrap_blob_defunct:
  _ap_bootstrap_start:
    jmp ap_bootstrap_bypassdata
    .global _ap_cr3_value
    _ap_cr3_value:
      .long 0
    .global _ap_cr4_value
    _ap_cr4_value: 
      .long 0
    .global _ap_runtime_entrypoint
    _ap_runtime_entrypoint:
	  .long 0
    .align 16
    .global _mle_join_start
    _mle_join_start:
    .long _ap_gdt_end - _ap_gdt_start - 1 // gdt_limit
    .long _ap_gdt_start - _ap_bootstrap_start + 0x10000// gdt_base
    .long 0x00000008 // CS
    .long _ap_clear_pipe - _ap_bootstrap_start + 0x10000 // entry point
    _mle_join_end:
    
    _ap_gdtdesc:
      .word _ap_gdt_end - _ap_gdt_start - 1
      .long _ap_gdt_start - _ap_bootstrap_start + 0x10000  
    
    .align 16
    _ap_gdt_start:
      .quad 0x0000000000000000
      .quad 0x00cf9a000000ffff	
      .quad 0x00cf92000000ffff
    _ap_gdt_end:
      .word 0
    
    .align 16
  ap_bootstrap_bypassdata:
      movw $0x1000, %ax
    	movw %ax, %ds
    	movw %ax, %es
    	movw $0xFFFF, %sp
    	movw $0x4000, %ax
    	movw %ax, %ss
    	
    	movw $0x0020, %si

      lgdt (%si)

      movl %cr0, %eax
      orl $0x1, %eax
      movl %eax, %cr0

      jmpl $0x08, $(_ap_clear_pipe - _ap_bootstrap_start + (0x1000 << 4))
    .code32
    _ap_clear_pipe:
      movw $0x10, %ax
      movw %ax, %ds
      movw %ax, %es
      movw %ax, %ss
      movw %ax, %fs
      movw %ax, %gs

	  // set CR0 WP bit
	  movl %cr0, %eax
	  orl 0x00010000, %eax
	  movl %eax, %cr0
	  
	  // set NX bit
	  movl 0xc0000080, %ecx
	  rdmsr
	  orl (1 << 11), %eax
	  wrmsr
	  			
      movl $(_ap_cr3_value - _ap_bootstrap_start + (0x1000 << 4)), %esi
      movl (%esi), %ebx
      movl %ebx, %cr3
      movl $(_ap_cr4_value - _ap_bootstrap_start + (0x1000 << 4)), %esi
      movl (%esi), %ebx
      movl %ebx, %cr4
      movl $(_ap_runtime_entrypoint - _ap_bootstrap_start + (0x1000 << 4)), %esi
      movl (%esi), %ebx
      
      movl %cr0, %eax
      orl $0x80000000, %eax	
      movl %eax, %cr0

      jmpl *%ebx
      hlt
		
	  .fill 256, 1, 0
