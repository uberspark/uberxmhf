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

// XMHF slab import library decls./defns.
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XG_BENCHGUEST_H__
#define __XG_BENCHGUEST_H__

#define 	__CS_CPL0 	    0x0008 	//guest slab CPL-0 code segment selector
#define 	__DS_CPL0 	    0x0010 	//guest slab CPL-0 data segment selector

#define GUEST_SLAB_HEADER_MAGIC     (0x76543210)

#ifndef __ASSEMBLY__

//guest slab header data type
typedef struct {
    u64 lvl2mempgtbl_pml4t[PAE_MAXPTRS_PER_PDPT];
    u64 lvl2mempgtbl_pdpt[PAE_MAXPTRS_PER_PDPT];
    u64 lvl2mempgtbl_pdts[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
    u32 magic;
    u64 gdt[16];
    u8 _filler0[3964]; //page-align the whole struct
} __attribute__((packed)) guest_slab_header_t;


extern void xcguestslab_do_vmcall(void);
extern void xcguestslab_do_testxhhyperdep(void);
extern void xcguestslab_do_testxhapprovexec(void);
extern __attribute__((aligned(4096))) void _xcguestslab_do_testxhssteptrace_func(void);
extern void xcguestslab_do_testxhsyscalllog(void);

#endif //__ASSEMBLY__


#endif //__XC_BENCHGUEST_H__
