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

#ifndef __XC_IHUB_H__
#define __XC_IHUB_H__

#define UAPI_XCIHUB_INSTALLICPTHANDLER    0


#ifndef __ASSEMBLY__

CASM_FUNCDECL(void xcihub_entry_icptstub(void *noparam));
void xcihub_entry_icpt(x86regs_t *r);
CASM_FUNCDECL(void xcihub_reticpt(x86regs_t *r));

void xcihub_icptmain(slab_params_t *sp);


/*@
	requires 0 <= cbtype <= XC_HYPAPPCB_MAXMASK;
@*/
uint32_t xc_hcbinvoke(uint32_t src_slabid, uint32_t cpuid, uint32_t cbtype, uint32_t cbqual, uint32_t guest_slab_index);

void xcihub_icptvmcall(uint32_t cpuid, uint32_t src_slabid);
void xcihub_icptcpuid(uint32_t cpuid);
void xcihub_icptwrmsr(uint32_t cpuid);
void xcihub_icptrdmsr(uint32_t cpuid);
void xcihub_icptcrx(uint32_t cpuid, uint32_t src_slabid);
void xcihub_icptxsetbv(uint32_t cpuid);
void xcihub_icptsipi(uint32_t cpuid);
void xcihub_halt(uint32_t cpuid, uint32_t info_vmexit_reason);

bool xcihub_rg_e820emulation(uint32_t cpuid, uint32_t src_slabid);

extern __attribute__(( section(".data") )) volatile uint32_t xcihub_smplock;




#endif //__ASSEMBLY__


#endif //__XC_IHUB_H__
