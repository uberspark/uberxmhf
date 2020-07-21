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
#include <uberspark/include/uberspark.h>
/*
 * host CPU state uAPI
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_hcpustate.h>


/////
//@ ghost bool uhcpust_methodcall_rdmsr = false;
//@ ghost bool uhcpust_methodcall_wrmsr = false;
//@ ghost bool uhcpust_methodcall_invalid = false;
/*@
	requires \valid(sp);
	ensures ( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_WRMSR && sp->src_slabid < XMHFGEEC_TOTAL_SLABS) ==> (uhcpust_methodcall_wrmsr == true);
	ensures ( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_RDMSR && sp->src_slabid < XMHFGEEC_TOTAL_SLABS) ==> (uhcpust_methodcall_rdmsr == true);
	ensures !(
		( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_WRMSR && sp->src_slabid < XMHFGEEC_TOTAL_SLABS) ||
		( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_RDMSR && sp->src_slabid < XMHFGEEC_TOTAL_SLABS)
	) ==> (uhcpust_methodcall_invalid == true);
@*/

void slab_main(slab_params_t *sp){

	if(sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_WRMSR && sp->src_slabid < XMHFGEEC_TOTAL_SLABS){
		uhcpust_wrmsr(sp->src_slabid, (xmhf_uapi_hcpustate_msr_params_t *)sp->in_out_params);
		//@ghost uhcpust_methodcall_wrmsr = true;

	}else if(sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_RDMSR && sp->src_slabid < XMHFGEEC_TOTAL_SLABS){
		uhcpust_rdmsr((xmhf_uapi_hcpustate_msr_params_t *)sp->in_out_params);
		//@ghost uhcpust_methodcall_rdmsr = true;

	}else {
		//_XDPRINTF_("UAPI_HCPUSTATE[%u]: Unknown uAPI function %x. Halting!\n",(uint16_t)sp->cpuid, sp->dst_uapifn);
		//@ghost uhcpust_methodcall_invalid = true;

	}
}
