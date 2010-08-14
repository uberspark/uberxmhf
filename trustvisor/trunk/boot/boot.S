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

/* boot.s - TrustVisor bootstrap code for skinit */
/* Adapted from Xen's x86_32.S for TrustVisor by Ning Qu and Arvind Seshadri */
	
#include <types.h>
#include <multiboot.h>
#include <paging.h>
#include <visor.h>
#include <processor.h>
#include <msr.h>
#include <dev.h>
	
	.section "_init_text"
/* start of code segment */
ENTRY(start) 
/* SLB header for using the skinit instruction. See AMD Vol.2 for details. */
	
	.align 4
	.word __start - start
        .word _visor_init_edata - start

__start:
/* Protection already enabled when skinit finishes executing. %esp is set
 * to the top of the SLB memory (slb_start + 64KB). %cs and %ss selectors
 * are set of 0x0008 and 0x0010 respectively. The corresponding descriptors
 * initialized to 32-bit segments, base 0, limit 4GB. All other segment
 * selectors retain their old values. All GPRs except %eax are cleared.
 * %eax has pointer to the SLB.
 */

	movl 	$MSR_VM_CR, %ecx
        rdmsr
#ifdef __DEBUG__
/* DPD, R_INIT and DIS_A20M flags in VM_CR are set to 1, clear them */
	andl	$(0xfffffff8), %eax
#else
/* DPD, R_INIT and DIS_A20M flags in VM_CR are set to 1, clear them 
 * except DPD
 */
	andl	$(0xfffffff9), %eax
#endif
	wrmsr

/* Load the boot gdt descriptor */
	lgdt	%cs:visor_boot_gdt_descr
	movw	$(__VISOR_DS), %cx
/* Load the data segment selectors */
	movw	%cx, %ds	
	movw	%cx, %es
	movw	%cx, %fs
	movw	%cx, %gs
/* Long jump to load cs */	
	ljmp	$(__VISOR_CS), $(1f)
1:
/* skinit initializes the stack point to the end of the skinit area.
 * The bootloader code and the kernel's bootstrap code pass
 * data to TrustVisor by placing the data on the top of TrustVisor's stack.
 * adjust %esp so that we do not overwrite the data that is passed.
 */
        subl	$INIT_STACK_RESV, %esp

/* Clear eflags */
	pushl	$0
	popf

/* Call TrustVisor initialization routine before paging enabled */
	call	init_visor

/* enable paging */
	mov	%cr0, %eax
	orl	$0x80000000, %eax
	mov	%eax, %cr0

/* Switch to runtime stack */
	lss	visor_stack, %esp
/* Relocate esp to top of runtime stack */	
	addl	$(STACK_SIZE), %esp
	
/* Call TrustVisor initialization routine after paging enabled */
	call	init_visor_post

/* Switch to runtime gdt */
	lgdt	%cs:visor_gdt_descr
	movw	$(__VISOR_DS), %cx
/* Load the data segment selector */
	movw	%cx, %ds	
	movw	%cx, %es
	movw	%cx, %fs
	movw	%cx, %gs
/* Long jump to load cs */	
	ljmp	$(__VISOR_CS), $(1f)
1:
	jmp	start_runtime
/* We should never return. Force CPU to panic if we do. */
	ud2	/* Undefined opcode */

/* Create a separate section for boot initialized data */
	.section "visor_boot_static_data", "wa"
/* boot GDT descriptor for TrustVisor */	
	.word	0			/* 32-bit align gdt descr */
visor_boot_gdt_descr:	
	.word	visor_boot_gdt_end - visor_boot_gdt - 1	/* gdt limit */
	.long	visor_boot_gdt		/* gdt base */

	.align	16
/* boot GDT for TrustVisor. 4GB code and data segments accessible at CPL0 */
ENTRY(visor_boot_gdt)
	.quad	0x0000000000000000	/* NULL descriptor */
	.quad	0x00cf9a000000ffff	/* Code seg */
	.quad	0x00cf92000000ffff	/* Data seg */
visor_boot_gdt_end:

/* Create a separate section for runtime initialized data */
	.section "visor_static_data", "wa"
/* runtime GDT descriptor for TrustVisor */	
	.word	0			/* 32-bit align gdt descr */
visor_gdt_descr:	
	.word	visor_gdt_end - visor_gdt - 1	/* gdt limit */
	.long	visor_gdt	/* gdt base */

	.align	16
/* runtime GDT for TrustVisor. 4GB code and data segments accessible at CPL0 */
ENTRY(visor_gdt)
	.quad	0x0000000000000000	/* NULL descriptor */
	.quad	0x00cf9a000000ffff	/* Code seg */
	.quad	0x00cf92000000ffff	/* Data seg */
visor_gdt_end:

	ALIGN	
/* Stack segment descriptor */
ENTRY(visor_stack)
	.long	stack 
	.long	__VISOR_DS

/* Start of PDP table for TrustVisor, aligned to 32 bytes */
	.align	32
ENTRY(visor_pdp_table)
        .quad	0x00
	.quad	0x00
	.quad	0x00
	.quad	0x00
/* Start of PDP table for Nested Paging, aligned to 32 bytes */
	.align	32
ENTRY(nested_pdp_table)
        .quad	0x00
	.quad	0x00
	.quad	0x00
	.quad	0x00

	.section "bss_page_table","w"
ENTRY(visor_pd_table)
        .fill	4 * PAGE_SIZE_4K, 1, 0
ENTRY(nested_pd_table)
        .fill	4 * PAGE_SIZE_4K, 1, 0
ENTRY(nested_pt_table)
        .fill	2048 * PAGE_SIZE_4K, 1, 0

	.section "bss_scode", "w"
/* Various buffer for scode whitelist and verification */
ENTRY(scode_whitelist)
        .fill	WHITELIST_SIZE * PAGE_SIZE_4K, 1, 0
ENTRY(scode_buffer)
	.fill	MODBUF_SIZE * PAGE_SIZE_4K, 1, 0

	.section "bss_visor_vmcb", "w"
ENTRY(visor_vmcb_label)
	.fill	PAGE_SIZE_4K, 1, 0

	.section "bss_visor_vm_hsave_area", "w"
ENTRY(visor_hsave_area)	
	.fill	PAGE_SIZE_4K, 1, 0

	.section "bss_visor_io_perm_bitmap", "w"
ENTRY(visor_io_perm_bitmap)
	.fill	3 * PAGE_SIZE_4K, 1, 0

	.section "bss_visor_msr_perm_bitmap", "w"
ENTRY(visor_msr_perm_bitmap)
	.fill	2 * PAGE_SIZE_4K, 1, 0

	.section "bss_scode_pfn_bitmap", "w"
ENTRY(scode_pfn_bitmap)
	.fill	MODPFN_SIZE * PAGE_SIZE_4K, 1, 0
ENTRY(scode_pfn_bitmap_2M)
	.fill	PAGE_SIZE_4K, 1, 0

	.section "bss_init_dev_bit_vector", "w"
ENTRY(init_dev_bit_vector)
/* NOTE: The inital DEV bit vector covers all physical memory from address 0
 * to the last address of TrustVisor's physical memory. 
 */
	.fill ((VISOR_LOAD_START + VISOR_INIT_SIZE + VISOR_RUNTIME_SIZE) >> LG_BASE2_BYTES_PER_DEV_BIT)/8, 1, 0

	.section "bss_dev_bit_vector", "w"
ENTRY(dev_bit_vector)
/* Need to add 1 in order to compensate for not being able to represent
 * the number "4GB" in 32 bits
 */
	.fill ((LAST_PHY_ADDR >> LG_BASE2_BYTES_PER_DEV_BIT) + 1)/8, 1, 0

	.section "visor_stack_seg", "w"
ENTRY(stack)
	.fill	STACK_SIZE, 1, 0

	.section "visor_startup_stack", "w"
ENTRY(startup_stack)
	.fill	STARTUP_STACK_SIZE, 1, 0
