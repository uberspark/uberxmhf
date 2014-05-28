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

#include <xmhf-core.h>

/*
 * slab header
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

extern void entry_cr3(void);

// this is in xmhf-slab.lscript
extern u8 slab_rodata_start[];
extern u8 slab_rodata_end[];
extern u8 slab_rwdata_start[];
extern u8 slab_rwdata_end[];
extern u8 slab_code_start[];
extern u8 slab_code_end[];
extern u8 slab_stack_start[];
extern u8 slab_stack_end[];

extern u8 _slab_region_shared_rodata[];
slab_table_t *g_slab_table = (slab_table_t *)&_slab_region_shared_rodata;


__attribute__ ((section(".stack"))) static u8 _slab_stack[XMHF_SLAB_STACKSIZE];

 
__attribute__ ((section(".slabrodata"))) slab_header_t slab_header = {
	.slab_index = 0,
	.slab_macmid = 0,
	.slab_privilegemask = 0,
	.slab_tos = ((u32)(&_slab_stack) + sizeof(_slab_stack)), 
	.slab_rodata.start = &slab_rodata_start,
	.slab_rodata.end = (u32)&slab_rodata_end,
	.slab_rwdata.start = &slab_rwdata_start,
	.slab_rwdata.end = (u32)&slab_rwdata_end,
	.slab_code.start = (u32)&slab_code_start,
	.slab_code.end = (u32)&slab_code_end,
	.slab_stack.start = (u32)&slab_stack_start,
	.slab_stack.end = (u32)&slab_stack_end,
	.entry_cr3 = &entry_cr3,
};


