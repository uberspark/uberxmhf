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

#ifndef __TESTSLAB1_H__
#define __TESTSLAB1_H__


#define	XMHF_SLAB_TESTSLAB1_FNENTRY0		0
#define	XMHF_SLAB_TESTSLAB1_FNENTRY0_SIZE	0

#define	XMHF_SLAB_TESTSLAB1_FNENTRY1	1
#define XMHF_SLAB_TESTSLAB1_FNENTRY2	2
#define XMHF_SLAB_TESTSLAB1_FNENTRY3	3

#ifndef __ASSEMBLY__

slab_retval_t testslab1_interface(u32 src_slabid, u32 dst_slabid, u32 fn_id, ...);

#ifdef __XMHF_SLAB_CALLER_INDEX__ 

//XMHF_SLAB_P2P_DEFIMPORTFN(slab_retval_t, entry_0, (u32 src_slabid, u32 dst_slabid, u32 fn_id), XMHF_SLAB_P2P_DEFIMPORTFNSTUB((3*sizeof(u32))) )
//XMHF_SLAB_DEFIMPORTFN(slab_retval_t, entry_0, (void), XMHF_SLAB_DEFIMPORTFNSTUB(__XMHF_SLAB_CALLER_INDEX__, XMHF_SLAB_TESTSLAB1_INDEX, XMHF_SLAB_TESTSLAB1_FNENTRY0, (sizeof(u32)), sizeof(slab_retval_t), XMHF_SLAB_FN_RETTYPE_AGGREGATE))
XMHF_SLAB_DEFIMPORTFN(slab_retval_t, entry_1, (u32 param1, u32 param2), XMHF_SLAB_DEFIMPORTFNSTUB(__XMHF_SLAB_CALLER_INDEX__, XMHF_SLAB_TESTSLAB1_INDEX, XMHF_SLAB_TESTSLAB1_FNENTRY1, (sizeof(u32)+sizeof(u32)+sizeof(u32)), sizeof(slab_retval_t), XMHF_SLAB_FN_RETTYPE_AGGREGATE))
XMHF_SLAB_DEFIMPORTFN(slab_retval_t, entry_2, (u32 cpu_index, bool isbsp, u32 partition_index), XMHF_SLAB_DEFIMPORTFNSTUB(__XMHF_SLAB_CALLER_INDEX__, XMHF_SLAB_TESTSLAB1_INDEX, XMHF_SLAB_TESTSLAB1_FNENTRY2, (sizeof(u32)+sizeof(bool)+sizeof(u32)+sizeof(u32)), sizeof(slab_retval_t), XMHF_SLAB_FN_RETTYPE_AGGREGATE) )
XMHF_SLAB_DEFIMPORTFN(slab_retval_t, entry_3, (context_desc_t context_desc, xc_hypapp_arch_param_t archparam), XMHF_SLAB_DEFIMPORTFNSTUB(__XMHF_SLAB_CALLER_INDEX__, XMHF_SLAB_TESTSLAB1_INDEX, XMHF_SLAB_TESTSLAB1_FNENTRY3, (sizeof(context_desc_t)+sizeof(xc_hypapp_arch_param_t)+sizeof(u32)), sizeof(slab_retval_t), XMHF_SLAB_FN_RETTYPE_AGGREGATE))

#else 	//!__XMHF_SLAB_CALLER_INDEX__

slab_retval_t entry_0(u32 src_slabid, u32 dst_slabid, u32 fn_id);
slab_retval_t entry_1(u32 param1, u32 param2);
slab_retval_t entry_2(u32 cpu_index, bool isbsp, u32 partition_index);
slab_retval_t entry_3(context_desc_t context_desc, xc_hypapp_arch_param_t archparam);

#endif	//__XMHF_SLAB_CALLER_INDEX__


#endif //__ASSEMBLY__


#endif //__TESTSLAB1_H__
