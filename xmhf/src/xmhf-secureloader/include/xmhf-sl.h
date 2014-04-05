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

// XMHF secure loader component declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHF_SL_H__
#define __XMHF_SL_H__

//XXX: the following is more platform specific, will need to be pushed
//into some backend
#define __TARGET_BASE_SL				0x10000000		//256MB
#define __TARGET_SIZE_SL				0x00200000
#define __TARGET_BASE_CORE				0x10200000		//258M


#ifndef __ASSEMBLY__



//----------------------------------------------------------------------
//exported DATA 
//----------------------------------------------------------------------
extern u8 xmhf_rpb_start[];


//----------------------------------------------------------------------
//exported FUNCTIONS 
//----------------------------------------------------------------------
void xmhf_sl_main(void);
void _xmhf_sl_entry(void);

//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------
void* xmhf_sl_arch_hva2sla(uintptr_t x);
u64 xmhf_sl_arch_sla2spa(void* x);
bool xmhf_sl_arch_integrity_check(u8* runtime_base_addr, size_t runtime_len);
void xmhf_sl_arch_sanitize_post_launch(void);
//void xmhf_sl_arch_early_dmaprot_init(u32 runtime_size);
void xmhf_sl_arch_early_dmaprot_init(u32 membase, u32 size);
void xmhf_sl_arch_xfer_control_to_runtime(RPB * rpb);
void xmhf_sl_arch_baseplatform_initialize(void);


//----------------------------------------------------------------------
//x86 ARCH. INTERFACES
//----------------------------------------------------------------------
u32 xmhf_sl_arch_x86_setup_runtime_paging(RPB * rpb, u32 runtime_spa, u32 runtime_sva, u32 totalsize);
void xmhf_sl_arch_x86_invoke_runtime_entrypoint(u32 gdtbase, u32 idtbase,
	u32 entrypoint, u32 stacktop, u32 cr3)__attribute__((cdecl)); 


//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//x86svm SUBARCH. INTERFACES
//----------------------------------------------------------------------
//extern u32 g_sl_protected_dmabuffer[]; //protected DMA-protection buffer 
									   //for early DMA protection 
									   //(only used for x86svm)
									   

#endif	//__ASSEMBLY__

#endif //__XMHF_SL_H__
