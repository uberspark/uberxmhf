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

/* Linker Script for creating TrustVisor
 * Adapted from Xen's xen.lds.S by Arvind Seshadri
 */

#include <visor.h>
#include <paging.h>
#include <svm.h>
#undef ENTRY	
#undef ALIGN 
		
OUTPUT_FORMAT("elf32-i386", "elf32-i386", "elf32-i386")
OUTPUT_ARCH(i386)
/* The first executable instruction of the program is labelled start */
ENTRY(start)
/* We want only one ELF program header called text for ld's purposes.
 * This program header describes a segment loaded from a file 
 * (the PT_LOAD argument)
 */
PHDRS
{
  text PT_LOAD ;
}
SECTIONS
{
  . = VISOR_LOAD_START; /* relocate location counter */
  _visor_init_start = .;
  _init_text : {
    *(_init_text)
  } :text =0x9090
  _visor_init_data_start = ALIGN(4);
  _init_data ALIGN(4): {
    *(visor_boot_static_data)
    *(_init_data)
  } :text =0x0000
  _visor_init_edata = .;
  _init_bss ALIGN(PAGE_SIZE_4K): {
    *(bss_init_dev_bit_vector)
  } :text =0x0000
  /* if the bottom of stack overlaps with the bss, then the stack can 
   * clobber part of the SLB. we need to check for this condition at 
   * compile time. see boot/chk_init_size.c for the program that
   * performs this check.
   */
  . = VISOR_LOAD_START + SKINIT_SLB_SIZE - STARTUP_STACK_SIZE;
  _init_stack : {
    *(visor_startup_stack)
  } :text =0x0000
  _visor_init_end = .;

  . = VISOR_RUNTIME_START;  /* relocate location counter to start of runtime */
  _visor_text = .;
  .text : {
    *(.text)
  } :text =0x9090 /* .text goes into PHDR text. NOPs fill empty space */
  _visor_etext = .;

/* IMPORTANT: ALIGN only returns a value which is the location counter aligned
 * on the requested boundary. It does NOT relocate the location counter. Use
 * the optional section attribute to place the section on a required boundary.
 */
  _visor_data_start = ALIGN(PAGE_SIZE_4K); 
  /* Start static data segment on new page */
  .data ALIGN(PAGE_SIZE_4K): {
    *(visor_static_data)
    . = ALIGN(4);
    *(visor_idt)
    . = ALIGN(4);
    *(.data)
  } :text =0x0000 /* .data goes into PHDR text. zeros fill empty space */
  _visor_data_end = .;

/* bss starts on a new page due to alignment requirements of CPU structures*/
  _visor_bss_start = ALIGN(PAGE_SIZE_4K);
  .bss ALIGN(PAGE_SIZE_4K): {
    *(bss_page_table)
    *(bss_scode)
    *(bss_visor_vmcb)
    *(bss_visor_vm_hsave_area)
    *(bss_visor_io_perm_bitmap)
    *(bss_visor_msr_perm_bitmap)
    *(bss_scode_pfn_bitmap)
    *(bss_dev_bit_vector)
    *(.bss)
  } :text =0x0000 /* .bss goes into PHDR text. zeros fill empty space */
  _visor_bss_end = .;
/* stack starts aligned on STACK_SIZE */
  _visor_stack_start = ALIGN(STACK_SIZE) ;
  .stack ALIGN(STACK_SIZE): {
    *(visor_stack_seg)
  } : text =0x0000 /*stack goes into PHDR text. zeros fill empty space */
  _visor_end = .;
  /DISCARD/ : {
  *(.text.exit)
  *(.data.exit)
  *(.exitcall.exit)
  }
	
/* Stabs debugging sections.  */ 
  .stab 0 : { *(.stab) }
  .stabstr 0 : { *(.stabstr) }
  .stab.excl 0 : { *(.stab.excl) }
  .stab.exclstr 0 : { *(.stab.exclstr) }
  .stab.index 0 : { *(.stab.index) }
  .stab.indexstr 0 : { *(.stab.indexstr) }
  .comment 0 : { *(.comment) }
}
