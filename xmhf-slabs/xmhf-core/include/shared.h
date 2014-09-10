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
 *
 *  XMHF slab shared mapping decls.
 *
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */

#ifndef __SHARED_H__
#define __SHARED_H__


#ifndef __ASSEMBLY__

extern __attribute__(( aligned(16) )) __attribute__(( section(".section_archds") )) u64 _gdt_start[] ;
extern __attribute__(( aligned(16) )) __attribute__(( section(".section_archds") )) arch_x86_gdtdesc_t _gdt;
extern __attribute__(( aligned(4096) )) __attribute__(( section(".section_archds") )) u8 _tss[PAGE_SIZE_4K];
extern __attribute__(( aligned(16) )) __attribute__(( section(".section_archds") )) idtentry_t _idt_start[EMHF_XCPHANDLER_MAXEXCEPTIONS] ;
extern __attribute__(( aligned(16) )) __attribute__(( section(".section_archds") )) arch_x86_idtdesc_t _idt;
extern __attribute__(( section(".section_archds") )) u64 _exceptionstubs[];


// initialization phase CPU stacks
extern __attribute__(( aligned(4096) )) __attribute__(( section(".section_archds") )) u8 _init_cpustacks[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];
// CPU table: mapping from unique CPU id --> 0 based index (into CPU stack)
extern __attribute__(( section(".section_archds") )) xmhf_cputable_t _cputable[MAX_PLATFORM_CPUS];
// count of platform CPUs
extern __attribute__(( section(".section_archds") )) u32 _totalcpus;


//libxmhfdebug
extern __attribute__(( section(".libxmhfdebugdata") )) u32 libxmhfdebug_lock;


#endif	//__ASSEMBLY__


#endif //__SHARED_H__
