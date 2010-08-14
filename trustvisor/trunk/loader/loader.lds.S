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

/* linker script for creating Pioneer
 * Adapted from TrustVisor's visor.lds.S for Pioneer by Arvind Seshadri
 */

#include <loader.h>
#include <paging.h>

#undef ENTRY
#undef ALIGN

OUTPUT_FORMAT("elf32-i386", "elf32-i386", "elf32-i386")
OUTPUT_ARCH(i386)
/* The first executable instruction of the program is lablled start */
ENTRY(loader)
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
  . = LOADER_START; /* relocate location counter */
  _text = .;
  .text : {
    *(loader_text)
    *(_init_text)
    *(.text)
  } :text =0x9090 /* .text goes into PHDR text. NOPs fill empty space */
  _etext = .;

/* IMPORTANT: ALIGN only returns a value which is the location counter aligned
 * on the requested boundary. It does NOT relocate the location counter. Use
 * the optional section attribute to place the section on a required boundary.
 */
  _data_start = ALIGN(PAGE_SIZE_4K); 
  /* Start static data segment on new page */
  .data ALIGN(PAGE_SIZE_4K): {
    *(loader_static_data)
    *(_init_data)
    *(.data)
  } :text =0x0000 /* .data goes into PHDR text. zeros fill empty space */
  _data_end = .;

/* stack starts aligned on LOADER_STACK_SIZE */
  _stack_start = ALIGN(LOADER_STACK_SIZE);
  .stack ALIGN(LOADER_STACK_SIZE): {
    *(loader_stack_seg)
  } : text =0x0000 /*stack goes into PHDR text. zeros fill empty space */
  _end = .;
	
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
