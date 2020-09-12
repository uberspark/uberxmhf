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
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_ihub.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_gcpustate.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_hcpustate.h>

/*
 * xcihub_icptsipi -- rich guest SMP bootup handling
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
void xcihub_icptsipi(uint32_t cpuid){
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;
	uint32_t info_vmexit_instruction_length;
	uint32_t info_exit_qualification;
	uint32_t sipivector;

	uberspark_uobjrtl_crt__memset(&spl, 0, sizeof(spl));
	spl.cpuid = cpuid;
	spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;

	//read exit qualification
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
	gcpustate_vmrwp->encoding = VMCS_INFO_EXIT_QUALIFICATION;
	XMHF_SLAB_CALLNEW(&spl);
	info_exit_qualification = gcpustate_vmrwp->value;

	//compute SIPI vector
	sipivector = (uint8_t)info_exit_qualification;
	_XDPRINTF_("%s[%u]: SIPI intercept, vector=0x%08x\n", __func__, cpuid, sipivector);

	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;

	//set guest CS:RIP to value specified by the SIPI vector
	gcpustate_vmrwp->encoding = VMCS_GUEST_CS_SELECTOR;
	gcpustate_vmrwp->value = ((sipivector * PAGE_SIZE_4K) >> 4);
	XMHF_SLAB_CALLNEW(&spl);

	gcpustate_vmrwp->encoding = VMCS_GUEST_CS_BASE;
	gcpustate_vmrwp->value = (sipivector * PAGE_SIZE_4K);
	XMHF_SLAB_CALLNEW(&spl);

	gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
	gcpustate_vmrwp->value = 0;
	XMHF_SLAB_CALLNEW(&spl);

	//set CPU activity state to active
	gcpustate_vmrwp->encoding = VMCS_GUEST_ACTIVITY_STATE;
	gcpustate_vmrwp->value = 0;
	XMHF_SLAB_CALLNEW(&spl);

	//clear interruptibility
	gcpustate_vmrwp->encoding = VMCS_GUEST_INTERRUPTIBILITY;
	gcpustate_vmrwp->value = 0;
	XMHF_SLAB_CALLNEW(&spl);
}



