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

#include <xmhf.h>
#include <xmhfgeec.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <xc_ihub.h>
#include <uapi_gcpustate.h>
//#include <uapi_hcpustate.h>
//#include <xh_hyperdep.h>
//#include <xh_syscalllog.h>
//#include <xh_ssteptrace.h>
//#include <xh_approvexec.h>

/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

//////
//XMHF_SLAB_INTERCEPT(xcihub)




void slab_main(slab_params_t *sp){
	u32 info_vmexit_reason;
	u32 hcb_status;
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;
	xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs = (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
	//xmhf_uapi_hcpustate_msr_params_t *hcpustate_msrp = (xmhf_uapi_hcpustate_msr_params_t *)spl.in_out_params;

	_XDPRINTF_("XCIHUB[%u]: Got control: src=%u, dst=%u, esp=%08x, eflags=%08x\n",
		(u16)sp->cpuid, sp->src_slabid, sp->dst_slabid, CASM_FUNCCALL(read_esp,CASM_NOPARAM),
			CASM_FUNCCALL(read_eflags, CASM_NOPARAM));

	spl.cpuid = sp->cpuid;
	spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;


	//store GPRs
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE;
	memcpy(&gcpustate_gprs->gprs, &sp->in_out_params[0], sizeof(x86regs_t));
	XMHF_SLAB_CALLNEW(&spl);

	//grab exit reason
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
	gcpustate_vmrwp->encoding = VMCS_INFO_VMEXIT_REASON;
	XMHF_SLAB_CALLNEW(&spl);
	info_vmexit_reason = gcpustate_vmrwp->value;

	if(info_vmexit_reason == VMX_VMEXIT_VMCALL){
		hcb_status = xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, sp->cpuid, XC_HYPAPPCB_HYPERCALL, 0, sp->src_slabid);
		if(hcb_status == XC_HYPAPPCB_CHAIN)	xcihub_icptvmcall((u16)sp->cpuid);


	}else if (info_vmexit_reason == VMX_VMEXIT_EPT_VIOLATION){
		hcb_status = xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, sp->cpuid, XC_HYPAPPCB_MEMORYFAULT, 0, sp->src_slabid);
		//if(hcb_status == XC_HYPAPPCB_CHAIN)	xcihub_halt((u16)sp->cpuid, info_vmexit_reason);


	}else if (info_vmexit_reason == VMX_VMEXIT_INIT || info_vmexit_reason == VMX_VMEXIT_TASKSWITCH){
		hcb_status = xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, sp->cpuid, XC_HYPAPPCB_SHUTDOWN, 0, sp->src_slabid);
		//if(hcb_status == XC_HYPAPPCB_CHAIN)	xcihub_halt((u16)sp->cpuid, info_vmexit_reason);

	//}else if (info_vmexit_reason == VMX_VMEXIT_IOIO){


	}else if (info_vmexit_reason == VMX_VMEXIT_CPUID){
		hcb_status = xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, sp->cpuid, XC_HYPAPPCB_TRAP_INSTRUCTION,
			    XC_HYPAPPCB_TRAP_INSTRUCTION_CPUID, sp->src_slabid);
		if(hcb_status == XC_HYPAPPCB_CHAIN) xcihub_icptcpuid((u16)sp->cpuid);


	}else if (info_vmexit_reason == VMX_VMEXIT_WRMSR){
		hcb_status =  xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, sp->cpuid,
			    XC_HYPAPPCB_TRAP_INSTRUCTION, XC_HYPAPPCB_TRAP_INSTRUCTION_WRMSR, sp->src_slabid);
		if(hcb_status == XC_HYPAPPCB_CHAIN)	xcihub_icptwrmsr((u16)sp->cpuid);


	}else if (info_vmexit_reason == VMX_VMEXIT_RDMSR){
		hcb_status = xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, sp->cpuid, XC_HYPAPPCB_TRAP_INSTRUCTION,
			    XC_HYPAPPCB_TRAP_INSTRUCTION_RDMSR, sp->src_slabid);
		if(hcb_status == XC_HYPAPPCB_CHAIN) xcihub_icptrdmsr((u16)sp->cpuid);


	}else if (info_vmexit_reason == VMX_VMEXIT_EXCEPTION){
		hcb_status = xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, sp->cpuid, XC_HYPAPPCB_TRAP_EXCEPTION, 0, sp->src_slabid);
		//if(hcb_status == XC_HYPAPPCB_CHAIN)	xcihub_halt((u16)sp->cpuid, info_vmexit_reason);


	}else {
		  xcihub_halt((u16)sp->cpuid, info_vmexit_reason);

	}


	//load GPRs
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
	XMHF_SLAB_CALLNEW(&spl);
	memcpy(&sp->in_out_params[0], &gcpustate_gprs->gprs, sizeof(x86regs_t));


	_XDPRINTF_("XCIHUB[%u]: Resuming guest, esp=%08x\n", (u16)sp->cpuid, CASM_FUNCCALL(read_esp,CASM_NOPARAM));


	//resume guest slab
	return;
}







