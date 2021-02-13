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

#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/uobjs/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/uobjs/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/uobjs/uapi_gcpustate.h>

void ugcpust_msrread(xmhf_uapi_gcpustate_msrrw_params_t *msrrwp){
		if(msrrwp->msr < GCPUSTATE_MSR_TOTAL){
			msrrwp->value = guestmsrs[msrrwp->msr];

			 //TODO: make core specific guestmsrs load
			 CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, guestmsrs);
			 CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_HIGH, 0);
			 CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, GCPUSTATE_MSR_TOTAL);
			 CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, guestmsrs);
			 CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_HIGH, 0);
			 CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, GCPUSTATE_MSR_TOTAL);
		}
}
