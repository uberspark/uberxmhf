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

#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/uobjs/uapi_gcpustate.h>


//@ghost bool ugcpust_vmwrite_callvmwrite = false;
/*@
	requires \valid(vmrwp);
	requires 0 <= srcslabid < XMHFGEEC_TOTAL_SLABS;

	behavior fromprime:
		assumes (srcslabid == XMHFGEEC_SLAB_GEEC_PRIME);
		ensures (ugcpust_vmwrite_callvmwrite == true);


	behavior notfromprime_valid:
		assumes !(srcslabid == XMHFGEEC_SLAB_GEEC_PRIME);
		assumes !(vmrwp->encoding == VMCS_CONTROL_VMX_SECCPU_BASED	||
			vmrwp->encoding == VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL	||
			vmrwp->encoding == VMCS_CONTROL_IO_BITMAPA_ADDRESS_HIGH	||
			vmrwp->encoding == VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL	||
			vmrwp->encoding == VMCS_CONTROL_IO_BITMAPB_ADDRESS_HIGH	||
			vmrwp->encoding == VMCS_CONTROL_EPT_POINTER_FULL	||
			vmrwp->encoding == VMCS_CONTROL_EPT_POINTER_HIGH	||
			vmrwp->encoding == VMCS_HOST_CR0			||
			vmrwp->encoding == VMCS_HOST_CR3			||
			vmrwp->encoding == VMCS_HOST_CR4			||
			vmrwp->encoding == VMCS_HOST_FS_BASE			||
			vmrwp->encoding == VMCS_HOST_GS_BASE			||
			vmrwp->encoding == VMCS_HOST_TR_BASE			||
			vmrwp->encoding == VMCS_HOST_GDTR_BASE			||
			vmrwp->encoding == VMCS_HOST_IDTR_BASE			||
			vmrwp->encoding == VMCS_HOST_SYSENTER_ESP		||
			vmrwp->encoding == VMCS_HOST_SYSENTER_EIP		||
			vmrwp->encoding == VMCS_HOST_RSP			||
			vmrwp->encoding == VMCS_HOST_RIP			||
			vmrwp->encoding == VMCS_HOST_SYSENTER_CS		||
			vmrwp->encoding == VMCS_HOST_IA32_EFER_FULL		||
			vmrwp->encoding == VMCS_HOST_ES_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_CS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_SS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_DS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_FS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_GS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_TR_SELECTOR);
		ensures (ugcpust_vmwrite_callvmwrite == true);

	behavior notfromprime_invalid:
		assumes !(srcslabid == XMHFGEEC_SLAB_GEEC_PRIME);
		assumes (vmrwp->encoding == VMCS_CONTROL_VMX_SECCPU_BASED	||
			vmrwp->encoding == VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL	||
			vmrwp->encoding == VMCS_CONTROL_IO_BITMAPA_ADDRESS_HIGH	||
			vmrwp->encoding == VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL	||
			vmrwp->encoding == VMCS_CONTROL_IO_BITMAPB_ADDRESS_HIGH	||
			vmrwp->encoding == VMCS_CONTROL_EPT_POINTER_FULL	||
			vmrwp->encoding == VMCS_CONTROL_EPT_POINTER_HIGH	||
			vmrwp->encoding == VMCS_HOST_CR0			||
			vmrwp->encoding == VMCS_HOST_CR3			||
			vmrwp->encoding == VMCS_HOST_CR4			||
			vmrwp->encoding == VMCS_HOST_FS_BASE			||
			vmrwp->encoding == VMCS_HOST_GS_BASE			||
			vmrwp->encoding == VMCS_HOST_TR_BASE			||
			vmrwp->encoding == VMCS_HOST_GDTR_BASE			||
			vmrwp->encoding == VMCS_HOST_IDTR_BASE			||
			vmrwp->encoding == VMCS_HOST_SYSENTER_ESP		||
			vmrwp->encoding == VMCS_HOST_SYSENTER_EIP		||
			vmrwp->encoding == VMCS_HOST_RSP			||
			vmrwp->encoding == VMCS_HOST_RIP			||
			vmrwp->encoding == VMCS_HOST_SYSENTER_CS		||
			vmrwp->encoding == VMCS_HOST_IA32_EFER_FULL		||
			vmrwp->encoding == VMCS_HOST_ES_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_CS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_SS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_DS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_FS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_GS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_TR_SELECTOR);
		ensures (ugcpust_vmwrite_callvmwrite == false);

	complete behaviors;
	disjoint behaviors;
@*/
void ugcpust_vmwrite(uint32_t srcslabid, xmhf_uapi_gcpustate_vmrw_params_t *vmrwp){
	if(srcslabid == XMHFGEEC_SLAB_GEEC_PRIME){
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite, vmrwp->encoding, vmrwp->value);
		//@ghost ugcpust_vmwrite_callvmwrite = true;

	}else{

		if(	!(vmrwp->encoding == VMCS_CONTROL_VMX_SECCPU_BASED	||
			vmrwp->encoding == VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL	||
			vmrwp->encoding == VMCS_CONTROL_IO_BITMAPA_ADDRESS_HIGH	||
			vmrwp->encoding == VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL	||
			vmrwp->encoding == VMCS_CONTROL_IO_BITMAPB_ADDRESS_HIGH	||
			vmrwp->encoding == VMCS_CONTROL_EPT_POINTER_FULL	||
			vmrwp->encoding == VMCS_CONTROL_EPT_POINTER_HIGH	||
			vmrwp->encoding == VMCS_HOST_CR0			||
			vmrwp->encoding == VMCS_HOST_CR3			||
			vmrwp->encoding == VMCS_HOST_CR4			||
			vmrwp->encoding == VMCS_HOST_FS_BASE			||
			vmrwp->encoding == VMCS_HOST_GS_BASE			||
			vmrwp->encoding == VMCS_HOST_TR_BASE			||
			vmrwp->encoding == VMCS_HOST_GDTR_BASE			||
			vmrwp->encoding == VMCS_HOST_IDTR_BASE			||
			vmrwp->encoding == VMCS_HOST_SYSENTER_ESP		||
			vmrwp->encoding == VMCS_HOST_SYSENTER_EIP		||
			vmrwp->encoding == VMCS_HOST_RSP			||
			vmrwp->encoding == VMCS_HOST_RIP			||
			vmrwp->encoding == VMCS_HOST_SYSENTER_CS		||
			vmrwp->encoding == VMCS_HOST_IA32_EFER_FULL		||
			vmrwp->encoding == VMCS_HOST_ES_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_CS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_SS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_DS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_FS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_GS_SELECTOR		||
			vmrwp->encoding == VMCS_HOST_TR_SELECTOR)
		){
			CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite, vmrwp->encoding, vmrwp->value);
			//@ghost ugcpust_vmwrite_callvmwrite = true;

		}else{
			//disallowed, do nothing
			//@ghost ugcpust_vmwrite_callvmwrite = false;
		}
	}
}
