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
 * guest CPU state uAPI
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <uapi_gcpustate.h>


/////
//@ ghost bool ugcpust_methodcall_vmread = false;
//@ ghost bool ugcpust_methodcall_vmwrite = false;
//@ ghost bool ugcpust_methodcall_gprsread = false;
//@ ghost bool ugcpust_methodcall_gprswrite = false;
//@ ghost bool ugcpust_methodcall_msrread = false;
//@ ghost bool ugcpust_methodcall_msrwrite = false;
//@ ghost bool ugcpust_methodcall_invalid = false;
/*@
	requires \valid(sp);
	ensures ( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_VMREAD) ==> (ugcpust_methodcall_vmread == true);
	ensures ( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_VMWRITE && (u16)sp->src_slabid < XMHFGEEC_TOTAL_SLABS ) ==> (ugcpust_methodcall_vmwrite == true);
	ensures ( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD && (u16)sp->cpuid < MAX_PLATFORM_CPUS) ==> (ugcpust_methodcall_gprsread == true);
	ensures ( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE && (u16)sp->cpuid < MAX_PLATFORM_CPUS) ==> (ugcpust_methodcall_gprswrite == true);
	ensures ( sp->dst_uapifn == XMHFGEEC_UAPI_CPUSTATE_GUESTMSRREAD) ==> (ugcpust_methodcall_msrread == true);
	ensures ( sp->dst_uapifn == XMHFGEEC_UAPI_CPUSTATE_GUESTMSRWRITE) ==> (ugcpust_methodcall_msrwrite == true);
	ensures !(
		( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_VMREAD) ||
		( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_VMWRITE && (u16)sp->src_slabid < XMHFGEEC_TOTAL_SLABS ) ||
		( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD && (u16)sp->cpuid < MAX_PLATFORM_CPUS) ||
		( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE && (u16)sp->cpuid < MAX_PLATFORM_CPUS) ||
		( sp->dst_uapifn == XMHFGEEC_UAPI_CPUSTATE_GUESTMSRREAD) ||
		( sp->dst_uapifn == XMHFGEEC_UAPI_CPUSTATE_GUESTMSRWRITE)
	) ==> (ugcpust_methodcall_invalid == true);

@*/
void slab_main(slab_params_t *sp){
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite, VMCS_GUEST_CR0, 0);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite, VMCS_HOST_TR_SELECTOR, 0);

	if( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_VMREAD){
		ugcpust_vmread((xmhf_uapi_gcpustate_vmrw_params_t *)sp->in_out_params);
		//@ghost ugcpust_methodcall_vmread = true;

	}else if( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_VMWRITE && (u16)sp->src_slabid < XMHFGEEC_TOTAL_SLABS ){
		ugcpust_vmwrite(sp->src_slabid, (xmhf_uapi_gcpustate_vmrw_params_t *)sp->in_out_params);
		//@ghost ugcpust_methodcall_vmwrite = true;

        }else if( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD && (u16)sp->cpuid < MAX_PLATFORM_CPUS){
		ugcpust_gprsread((u16)sp->cpuid, (xmhf_uapi_gcpustate_gprs_params_t *)sp->in_out_params);
		//@ghost ugcpust_methodcall_gprsread = true;

        }else if( sp->dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE && (u16)sp->cpuid < MAX_PLATFORM_CPUS){
		ugcpust_gprswrite((u16)sp->cpuid, (xmhf_uapi_gcpustate_gprs_params_t *)sp->in_out_params);
		//@ghost ugcpust_methodcall_gprswrite = true;

        }else if( sp->dst_uapifn == XMHFGEEC_UAPI_CPUSTATE_GUESTMSRREAD){
		ugcpust_msrread((xmhf_uapi_gcpustate_msrrw_params_t *)sp->in_out_params);
		//@ghost ugcpust_methodcall_msrread = true;

        }else if (sp->dst_uapifn == XMHFGEEC_UAPI_CPUSTATE_GUESTMSRWRITE){
		ugcpust_msrwrite((xmhf_uapi_gcpustate_msrrw_params_t *)sp->in_out_params);
		//@ghost ugcpust_methodcall_msrwrite = true;

        }else{
		//_XDPRINTF_("UAPI_GCPUSTATE[%u]: Unknown uAPI function %x. Halting!\n", (u16)sp->cpuid, sp->dst_uapifn);
		//@ghost ugcpust_methodcall_invalid = true;
	}
}
