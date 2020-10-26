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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xc_ihub.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/uapi_gcpustate.h>

/*
 * xcihub_icptvmcall -- rich guest VMCALL interfacing
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
void xcihub_icptvmcall(uint32_t cpuid, uint32_t src_slabid){
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;
	uint32_t guest_rip;
	uint32_t info_vmexit_instruction_length;

	//_XDPRINTF_("%s[%u]: VMX_VMEXIT_VMCALL\n", __func__, cpuid);

	//check to see if we need to handle rich guest E820 emulation, if so handle
	//emulation, else rotate through hypapp callbacks
	if (!xcihub_rg_e820emulation(cpuid, src_slabid)){

		xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, cpuid, XC_HYPAPPCB_HYPERCALL, 0, src_slabid);

		//skip over VMCALL by updating guest RIP
		//TODO: halt if we don't handle the VMCALL instead of just ignoring it
		spl.cpuid = cpuid;
		spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
		spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;

		gcpustate_vmrwp->encoding = VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH;
		gcpustate_vmrwp->value=0;
		XMHF_SLAB_CALLNEW(&spl);
		info_vmexit_instruction_length = gcpustate_vmrwp->value;

		gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
		gcpustate_vmrwp->value=0;
		XMHF_SLAB_CALLNEW(&spl);
		guest_rip = gcpustate_vmrwp->value;
		guest_rip+=info_vmexit_instruction_length;

		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
		gcpustate_vmrwp->value = guest_rip;
		XMHF_SLAB_CALLNEW(&spl);

		//write interruptibility = 0
		gcpustate_vmrwp->encoding = VMCS_GUEST_INTERRUPTIBILITY;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		//_XDPRINTF_("%s[%u]: no-E820 adjusted guest_rip=%08x\n", __func__, cpuid, guest_rip);
	}
}



