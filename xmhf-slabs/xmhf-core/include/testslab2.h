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

#ifndef __TESTSLAB2_H__
#define __TESTSLAB2_H__

#define	XMHF_SLAB_TESTSLAB2_FNENTRY1		1
#define	XMHF_SLAB_TESTSLAB2_FNENTRY1_SIZE	0

#define	XMHF_SLAB_TESTSLAB2_FNENTRY2		2
#define	XMHF_SLAB_TESTSLAB2_FNENTRY2_SIZE	(2*sizeof(u32))

#define XMHF_SLAB_TESTSLAB2_FNENTRY3		3
#define XMHF_SLAB_TESTSLAB2_FNENTRY3_SIZE	(3*sizeof(u32))

#define XMHF_SLAB_TESTSLAB2_FNENTRY4		4
#define XMHF_SLAB_TESTSLAB2_FNENTRY4_SIZE	(sizeof(context_desc_t)+sizeof(xc_hypapp_arch_param_t))


#ifndef __ASSEMBLY__

slab_retval_t testslab2_interface(u32 src_slabid, u32 dst_slabid, u32 fn_id, ...);

void testslab2_entry1(void);
u32 testslab2_entry2(u32 param1, u32 param2);
context_desc_t testslab2_entry3(u32 cpu_index, bool isbsp, u32 partition_index);
xc_hypapp_arch_param_t testslab2_entry4(context_desc_t context_desc, xc_hypapp_arch_param_t archparam);

#endif //__ASSEMBLY__


#endif //__TESTSLAB2_H__
