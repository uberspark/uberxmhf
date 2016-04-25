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

/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

bool xcihub_rg_e820emulation(u32 cpuid, u32 src_slabid){
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;
	xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs = (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
	u32 g_cs_base, g_eip;
	u32 g_es_base;
	x86regs_t r;

	//read CS base and RIP
	spl.cpuid = cpuid;
	spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;

	gcpustate_vmrwp->encoding = VMCS_GUEST_CS_BASE;
	XMHF_SLAB_CALLNEW(&spl);
	g_cs_base= gcpustate_vmrwp->value;

	gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
	XMHF_SLAB_CALLNEW(&spl);
	g_eip = gcpustate_vmrwp->value;


	//check if this is a E820 emulation VMCALL, if not return false
	if ( !( (g_cs_base == (VMX_UG_E820HOOK_CS << 4)) && (g_eip == VMX_UG_E820HOOK_IP) ) )
		return false;

	//read ES.base
	gcpustate_vmrwp->encoding = VMCS_GUEST_ES_BASE;
	XMHF_SLAB_CALLNEW(&spl);
	g_es_base= gcpustate_vmrwp->value;

	//read GPRs
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
	XMHF_SLAB_CALLNEW(&spl);
	memcpy(&r, &gcpustate_gprs->gprs, sizeof(x86regs_t));

	//if memmap
	//	write gprs
	//	write rip
	//else
	//	write cs
	//	write rip

	//write interruptibility = 0
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
	gcpustate_vmrwp->encoding = VMCS_GUEST_INTERRUPTIBILITY;
	gcpustate_vmrwp->value = 0;
	XMHF_SLAB_CALLNEW(&spl);

	_XDPRINTF_("%s[%u]: E820 emulation: WIP. Halting!\n", __func__, cpuid);
	HALT();


	//we handled a VMCALL which was E820 emulation
	return true;
}



