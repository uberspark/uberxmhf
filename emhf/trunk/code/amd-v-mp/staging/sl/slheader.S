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

// secure loader support routines
// authors: amit vasudevan (amitvasudevan@acm.org) and jonmccune@gmail.com

#include <target.h>
#include <msr.h>
#include <svm.h>


//our C main
.extern slmain

//the start of SL is a special header that is required by SKINIT
//we need to place this right at the start in our linker script
//note: our sl is always padded to 64K in size regardless of the
//actual size of the code and data. further the linker relocation
//base for our sl is always zero.
.section .sl_header
              
	.global _sl_header
	_sl_header:   
	.word _sl_start 	//SL entry point relative to header (bits 0-15)
	.word 0xFFFF  		//SL size including the header (bits 16-32)
									  //i.e, 0 through 65535 inclusive = 64K

.section .text
              
	.global _sl_start
	_sl_start:	//we get here with CS and SS as flat code and data segment 	
						  //selectors, ESP is initialized to _sl_end, GIF=0 so we are
						  //running with no interruptions, EFLAGS_IF=0 and paging is off
						  //EAX = 64K aligned physical memory address where our sl was
						  //loaded
	
	//save EAX 
	movl %eax, %ebp
	
	//[DEBUG]
	//enable HDT debugging, SKINIT disables it
	movl $(VM_CR_MSR), %ecx
	rdmsr
	andl $(~(1<<VM_CR_DPD)), %eax
	wrmsr
						  

	//from here on we use EBP as base and variable accesses will be as offsets
	//from _sl_header for position independence
	
	//setup GDT so that CS:base=sl base, limit=64K, type=code
	//DS,SS,ES: base=sl base, limit=64K, type=data
	//FS and GS: base=0, limit=4G, type=data (FLAT)

		//grab offset of sl_gdt_start
		movl $(sl_gdt_start), %ebx	
	
		//bits 0:16 of %eax = bits 16:23 of sl base address
		//bits 24:31 of %eax = bits 24:31 of sl base address
		movl %ebp, %eax
		movl %ebp, %ecx
		andl $0xFF000000, %eax
		andl $0x00FF0000, %ecx
		shrl $16, %ecx	
		orl %ecx, %eax

		//get high 32-bits of 64-bit GDT entry for selector 0x08 (code)
		//and update it with the base address of the sl
		movl %ss:12(%ebp, %ebx), %esi
		andl $0x00FFFF00, %esi
		orl %eax, %esi
		movl %esi, %ss:12(%ebp, %ebx) 
		
		//get high 32-bits of 64-bit GDT entry for selector 0x10 (data)
		//and update it with the base address of the sl
		movl %ss:20(%ebp, %ebx), %esi
		andl $0x00FFFF00, %esi
		orl %eax, %esi
		movl %esi, %ss:20(%ebp, %ebx) 
		

	//fixup linear address of GDT using sl load-base
	movl $(sl_gdt), %ebx	
	addl %ebp, %ss:2(%ebp, %ebx)
	
	//load sl gdt	
	lgdt %ss:(%ebp,%ebx)


	//far jump to reload %cs
	jmpl $0x08, $(sl_startnew)

	//we start here with our new GDT CS selector
sl_startnew:	
	//load new segment selectors for DS, SS and ES
	movw $0x10, %ax
	movw %ax, %ds
	movw %ax, %es
	movw %ax, %ss

	//load 4G flat selectors to FS and GS
	movw $0x18, %ax
	movw %ax, %fs
	movw %ax, %gs

	//setup ESP to top of 64K
	movl $0xFFFF, %esp	

	pushl %ebp
	call slmain
	
  //we should never get here
	spinforever:
		jmp spinforever
	hlt							  

.section .data
	
	//the secure loader GDT
	sl_gdt:
	.word	sl_gdt_end - sl_gdt_start - 1	
	.long	sl_gdt_start							//this will be fixed up to sl load-base
	.align	16
	sl_gdt_start:
	.quad	0x0000000000000000				//0x00: NULL selector	
//	.quad	0x00409a000000ffff				//0x08: 64K CODE selector	
//	.quad	0x004092000000ffff				//0x10: 64K DATA selector	
	.quad	0x00cf9a000000ffff				//0x08: 4G CODE selector with sl load-base	
	.quad	0x00cf92000000ffff				//0x10: 4G DATA selector with sl load-base	
	.quad 0x00cf92000000ffff				//0x18: 4G DATA selector with zero base
	.quad	0x0000000000000000				//0x20: NULL selector	
	sl_gdt_end:


//this is the stack section
.section .sl_stack
	.fill __SL_STACKSIZE, 1, 0 

//this section exists so that the linker script can pad our sl image
//to exactly 64K
.section .sl_trailer
	.global _sl_trailer
	_sl_trailer:
	.fill 4096, 1, 0
	
//this section is the input parameter section for the secure loader
//parameters from "init" are placed here. ordering of the variables
//MUST match that in include/target.h
//this section is currently a pagesize in length and resides above
//the 64K sl image
.section .sl_params

	.global slpb_buffer
	slpb_buffer:
	.long	SL_PARAMETER_BLOCK_MAGIC				//magic		
	.long	0																//hashSL
	.long 0																//errorHandler
	.long 0																//isEarlyInit
	.long 0																//numE820Entries
	.fill	(SIZE_STRUCT_GRUBE820 * MAX_E820_ENTRIES), 1, 0	//grub E820 map buffer
		