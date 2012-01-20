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

/**
 * rntm-x86-data.c
 * EMHF runtime data definitions - x86 specific
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <emhf.h> 

//runtime GDT
u64 x_gdt_start[] __attribute__(( section(".data"), aligned(16) )) = {
	0x0000000000000000ULL,
	0x00cf9a000000ffffULL,	
	0x00cf92000000ffffULL,	
	0x0000000000000000ULL	
};

//runtime GDT descriptor
arch_x86_gdtdesc_t x_gdt __attribute__(( section(".data"), aligned(16) )) = {
	.size=sizeof(x_gdt_start)-1,
	.base=(u32)&x_gdt_start,
};


//runtime PAE page tables
u8 x_3level_pdpt[PAGE_SIZE_4K] __attribute__(( section(".palign_data") ));
u8 x_3level_pdt[PAE_PTRS_PER_PDPT * PAGE_SIZE_4K] __attribute__(( section(".palign_data") ));
		
//runtime stack
u8 x_init_stack[RUNTIME_STACK_SIZE] __attribute__(( section(".stack") ));

