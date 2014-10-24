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

// XMHF hypapp callback declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHF_HYPAPP_H__
#define __XMHF_HYPAPP_H__

#ifndef __ASSEMBLY__

//hypapp sub-interface ids
#define XMHF_SLAB_HYPAPP_FNINITIALIZATION					1
#define XMHF_SLAB_HYPAPP_FNINITIALIZATION_SIZE				(sizeof(context_desc_t)+sizeof(hypapp_env_block_t))

#define XMHF_SLAB_HYPAPP_FNHANDLEHYPERCALL					2
#define XMHF_SLAB_HYPAPP_FNHANDLEHYPERCALL_SIZE				(sizeof(context_desc_t)+sizeof(u64)+sizeof(u64))

#define XMHF_SLAB_HYPAPP_FNHANDLEINTERCEPTHPTFAULT			3
#define XMHF_SLAB_HYPAPP_FNHANDLEINTERCEPTHPTFAULT_SIZE		(sizeof(context_desc_t)+sizeof(u64)+sizeof(u64)+sizeof(u64))

#define XMHF_SLAB_HYPAPP_FNHANDLEINTERCEPTTRAP				4
#define XMHF_SLAB_HYPAPP_FNHANDLEINTERCEPTTRAP_SIZE			(sizeof(context_desc_t)+sizeof(xc_hypapp_arch_param_t))

#define XMHF_SLAB_HYPAPP_FNSHUTDOWN							5
#define XMHF_SLAB_HYPAPP_FNSHUTDOWN_SIZE					(sizeof(context_desc_t))

#define XMHF_SLAB_HYPAPP_FNHANDLEQUIESCE					6
#define XMHF_SLAB_HYPAPP_FNHANDLEQUIESCE_SIZE				(sizeof(context_desc_t))

//generic catch-all app return codes
#define APP_SUCCESS     		(0x1)
#define APP_ERROR				(0x0)

//emhf app constant definitions
#define APP_TRAP_CHAIN   0xA0
#define APP_TRAP_SKIP    0xA1
#define APP_INIT_SUCCESS        0x0
#define APP_INIT_FAIL           0xFF

u32 xmhf_hypapp_initialization(context_desc_t context_desc, hypapp_env_block_t hypappenvb);
u32 xmhf_hypapp_handlehypercall(context_desc_t context_desc, u64 hypercall_id, u64 hypercall_param);
u32 xmhf_hypapp_handleintercept_hptfault(context_desc_t context_desc, u64 gpa, u64 gva, u64 error_code);
u32 xmhf_hypapp_handleintercept_trap(context_desc_t context_desc, xc_hypapp_arch_param_t xc_hypapp_arch_param);
void xmhf_hypapp_handleshutdown(context_desc_t context_desc);
void xmhf_hypapp_handlequiesce(context_desc_t context_desc);

#endif //__ASSEMBLY__

#endif	// __XMHF_HYPAPP_H__
