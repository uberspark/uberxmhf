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
 * xcihub_halt -- halt on unhandled rich guest intercepts
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#if 1
void xcihub_halt_eptviolation(uint32_t cpuid, uint32_t info_vmexitreason){
         	uint64_t errorcode;
         	uint64_t gpa;
         	uint64_t gva;
         	slab_params_t spl;
       	    xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp =
                (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;


         	spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
         	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
         	spl.cpuid = cpuid;
            spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;

            gcpustate_vmrwp->encoding = VMCS_INFO_EXIT_QUALIFICATION;
            ugcpust_slab_main(&spl);
            errorcode = gcpustate_vmrwp->value;

            gcpustate_vmrwp->encoding = VMCS_INFO_GUEST_PADDR_FULL;
            ugcpust_slab_main(&spl);
            gpa = gcpustate_vmrwp->value;

            gcpustate_vmrwp->encoding = VMCS_INFO_GUEST_LINEAR_ADDRESS;
            ugcpust_slab_main(&spl);
            gva = gcpustate_vmrwp->value;

        	_XDPRINTF_("%s[%u]: EPT violation gpa=0x%016llx\n", __func__, cpuid, gpa);
        	_XDPRINTF_("%s[%u]: EPT violation gva=0x%016llx\n", __func__, cpuid, gva);
        	_XDPRINTF_("%s[%u]: EPT violation error_code=0x%016llx\n", __func__, cpuid, errorcode);
}
#endif



void xcihub_halt(uint32_t cpuid, uint32_t info_vmexit_reason){
#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_DEBUG_SERIAL__)
	//initialize debugging early on
	uberspark_uobjrtl_debug__init(NULL);
	//[debug] print relevant startup info.
	_XDPRINTF_("%s: xcihub_halt: reinitted UART...\n", __func__);
#endif


	_XDPRINTF_("%s[%u]: unhandled intercept %x. Halting!\n", __func__, cpuid, info_vmexit_reason);
#if 1
	if(info_vmexit_reason == 0x30){
		xcihub_halt_eptviolation(cpuid, info_vmexit_reason);
	}
#endif
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
}

