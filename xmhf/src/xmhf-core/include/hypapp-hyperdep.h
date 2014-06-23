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
 *  hyperdep hypapp slab decls.
 * 
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */

#ifndef __HYPAPP_HYPERDEP_H__
#define __HYPAPP_HYPERDEP_H__

#define XMHF_SLAB_HYPAPP_HYPERDEP_FNINITIALIZATION					0
#define XMHF_SLAB_HYPAPP_HYPERDEP_FNHANDLEHYPERCALL					1
#define XMHF_SLAB_HYPAPP_HYPERDEP_FNHANDLEINTERCEPTHPTFAULT			2
#define XMHF_SLAB_HYPAPP_HYPERDEP_FNHANDLEINTERCEPTTRAP				3
#define XMHF_SLAB_HYPAPP_HYPERDEP_FNSHUTDOWN						4


#ifndef __ASSEMBLY__

#ifdef __XMHF_SLAB_INTERNAL_USE__




#else  //!__XMHF_SLAB_INTERNAL_USE__

XMHF_SLAB_DEFIMPORTFN(u32 xmhf_hypapp_initialization(context_desc_t context_desc, hypapp_env_block_t hypappenvb)						,XMHF_SLAB_DEFIMPORTFNSTUB(XMHF_SLAB_HYPAPP_HYPERDEP_INDEX,	XMHF_SLAB_HYPAPP_HYPERDEP_FNINITIALIZATION			, (sizeof(context_desc_t)+sizeof(hypapp_env_block_t))			, 0	, XMHF_SLAB_FN_RETTYPE_NORMAL))
XMHF_SLAB_DEFIMPORTFN(u32 xmhf_hypapp_handlehypercall(context_desc_t context_desc, u64 hypercall_id, u64 hypercall_param)				,XMHF_SLAB_DEFIMPORTFNSTUB(XMHF_SLAB_HYPAPP_HYPERDEP_INDEX,	XMHF_SLAB_HYPAPP_HYPERDEP_FNHANDLEHYPERCALL			, (sizeof(context_desc_t)+sizeof(u64)+sizeof(u64))				, 0	, XMHF_SLAB_FN_RETTYPE_NORMAL))
XMHF_SLAB_DEFIMPORTFN(u32 xmhf_hypapp_handleintercept_hptfault(context_desc_t context_desc, u64 gpa, u64 gva, u64 error_code)			,XMHF_SLAB_DEFIMPORTFNSTUB(XMHF_SLAB_HYPAPP_HYPERDEP_INDEX,	XMHF_SLAB_HYPAPP_HYPERDEP_FNHANDLEINTERCEPTHPTFAULT	, (sizeof(context_desc_t)+sizeof(u64)+sizeof(u64)+sizeof(u64))	, 0	, XMHF_SLAB_FN_RETTYPE_NORMAL))
XMHF_SLAB_DEFIMPORTFN(u32 xmhf_hypapp_handleintercept_trap(context_desc_t context_desc, xc_hypapp_arch_param_t xc_hypapp_arch_param)	,XMHF_SLAB_DEFIMPORTFNSTUB(XMHF_SLAB_HYPAPP_HYPERDEP_INDEX,	XMHF_SLAB_HYPAPP_HYPERDEP_FNHANDLEINTERCEPTTRAP		, (sizeof(context_desc_t)+sizeof(xc_hypapp_arch_param_t))		, 0	, XMHF_SLAB_FN_RETTYPE_NORMAL))
XMHF_SLAB_DEFIMPORTFN(void xmhf_hypapp_handleshutdown(context_desc_t context_desc)														,XMHF_SLAB_DEFIMPORTFNSTUB(XMHF_SLAB_HYPAPP_HYPERDEP_INDEX,	XMHF_SLAB_HYPAPP_HYPERDEP_FNSHUTDOWN				, (sizeof(context_desc_t))										, 0	, XMHF_SLAB_FN_RETTYPE_NORMAL))

#endif //__XMHF_SLAB_INTERNAL_USE__


#endif	//__ASSEMBLY__


#endif //__HYPAPP_HYPERDEP_H__
