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

// Secure Loader Block
// author: jonmccune@gmail.com

#include <target.h>
#include <msr.h>
#include <svm.h>

//Useful macro for busy wait-based serial debug of a single character
// .altmacro
// .macro OneChar2Serial theChar
//       movl  $1000000, %edx
// 1:
//       subl $1, %edx
//       cmpl $0, %edx
//       jz 1b

//       movb &theChar&, %al
//       movw $0x3f8, %dx
//       out %al, (%dx)              
// .endm              

.section .text
              
//---SLB header
.global _slb_start
_slb_start:   
.word _slb_bootstrap_start - _slb_start // SLB entry point (bits 0-15)
.word _slb_end - _slb_start         // SLB size (bits 16-32)
              
//---SLB boot-strap code---------------------------------------------------------
  .code32
  .global _slb_bootstrap_start
  _slb_bootstrap_start:
    jmp _slb_bootstrap_bypassdata

    // temporary GDT pseudo-descriptor (until paging can be re-enabled)
	temp_gdt:
	.word	temp_gdt_end - temp_gdt_start - 1	
	.long	temp_gdt_start - _slb_start + SLB_BOOTSTRAP_CODE_BASE
    // temporary GDT
	.align	16
	temp_gdt_start:
	.quad	0x0000000000000000	
	.quad	0x00cf9a000000ffff	
	.quad	0x00cf92000000ffff	
	.quad	0x0000000000000000	
	temp_gdt_end:
    // CR3
    .global _slb_cr3_value
    _slb_cr3_value:
      .long 0
    // CR4
    .global _slb_cr4_value
    _slb_cr4_value: 
      .long 0
    // ESP
    .global _slb_esp_value
    _slb_esp_value: 
      .long 0
    // EBP
    .global _slb_ebp_value
    _slb_ebp_value: 
      .long 0
    // entry-point in virtual address universe (runtime.c:cstartup)
    .global _slb_post_skinit_entry
     _slb_post_skinit_entry: 
      .long 0
              
  _slb_bootstrap_bypassdata:
              
      // load GDT via GDT pseudo-descriptor
      movl $(temp_gdt - _slb_start + SLB_BOOTSTRAP_CODE_BASE), %esi
      lgdt %ss:(%esi)

      // reload segment registers
      movw $0x10, %bx
      movw  %bx, %es
      movw  %bx, %fs
      movw  %bx, %gs
      movw  %bx, %ds              
              
      movl $(_slb_cr3_value - _slb_start + SLB_BOOTSTRAP_CODE_BASE), %esi
      movl (%esi), %ebx
      movl %ebx, %cr3

      movl $(_slb_cr4_value - _slb_start + SLB_BOOTSTRAP_CODE_BASE), %esi
      movl (%esi), %ebx
      movl %ebx, %cr4

      // load target address for branch once paging is enabled
      movl $(_slb_post_skinit_entry - _slb_start + SLB_BOOTSTRAP_CODE_BASE), %ebx

      //    enable PG (paging) flag (bit 31 of CR0)
      movl %cr0, %eax
      orl $0x80000000, %eax
      // mov to CR0 must be followed immediately by a branch instruction
      movl %eax, %cr0
      jmp 1f
1:            

      //    restore esp, ebp to pre-skinit values
      movl $(_slb_esp_value - _slb_start + SLB_BOOTSTRAP_CODE_BASE), %esi
      movl (%esi), %esp
      movl $(_slb_ebp_value - _slb_start + SLB_BOOTSTRAP_CODE_BASE), %esi
      movl (%esi), %ebp
              
      // resuming execution of code in runtimesup.S
      jmp *(%ebx)
      hlt // should never get here
      
  .global _slb_bootstrap_end
  _slb_bootstrap_end:
.global _slb_end
_slb_end:      
    nop
    nop
    nop
    nop
