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

/**
 * XMHF secureloader x86-vmx entry module
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
 
#include <xmhf.h>

/* sl stack, this is just a placeholder and ensures that the linker
 actually "allocates" the stack up until 0x10000*/
u8 _sl_stack[1] __attribute__((section(".sl_stack")));

__attribute__((naked)) void _xmhf_sl_entry(void) __attribute__(( section(".sl_header") )) __attribute__(( align(4096) )){
	
asm volatile ( 	".global _mle_page_table_start \r\n"
			   "_mle_page_table_start:\r\n"
			   ".fill 4096, 1, 0 \r\n" /* first page*/
			   ".global g_sl_protected_dmabuffer\r\n"
				"g_sl_protected_dmabuffer:\r\n"
				".fill 4096, 1, 0 \r\n" /* second page*/
				".fill 4096, 1, 0 \r\n" /* third page*/
				".global _mle_page_table_end \r\n"
				"_mle_page_table_end: \r\n"
				".global _mle_hdr \r\n"
				"_mle_hdr:\r\n"
				".fill 0x80, 1, 0x90\r\n" /* XXX TODO just a guess; should really be sizeof(mle_hdr_t) */
				".global _sl_start \r\n"
				"_sl_start: \r\n"
			    "movw %%ds, %%ax \r\n" 
				"movw %%ax, %%fs \r\n"
				"movw %%ax, %%gs \r\n"
			    "movw %%ax, %%ss \r\n"
			    "movl $0x10010000, %%esp \r\n" /* XXX TODO Get rid of magic number*/
			    :
			    :
		);

		xmhf_sl_main();

}
