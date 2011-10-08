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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

// EMHF memory protection component
// implementation
// author: amit vasudevan (amitvasudevan@acm.org)

#include <target.h>

// initialize memory protection structures for a given core (vcpu)
void emhf_memprot_initialize(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){ 
		struct vmcb_struct *vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;
		_svm_nptinitialize(vcpu->npt_vaddr_ptr, 
			vcpu->npt_vaddr_pdts, vcpu->npt_vaddr_pts);
		vmcb->h_cr3 = __hva2spa__(vcpu->npt_vaddr_ptr);
		vmcb->np_enable |= (1ULL << NP_ENABLE);
		vmcb->guest_asid = vcpu->npt_asid;
		printf("\nCPU(0x%02x): Activated SVM NPTs.", vcpu->id);
	}else{	//CPU_VENDOR_INTEL
		_vmx_gathermemorytypes(vcpu);
		_vmx_setupEPT(vcpu);
		vcpu->vmcs.control_VMX_seccpu_based |= (1 << 1); //enable EPT
		vcpu->vmcs.control_VMX_seccpu_based |= (1 << 5); //enable VPID
		vcpu->vmcs.control_vpid = 1; //VPID=0 is reserved for hypervisor
		vcpu->vmcs.control_EPT_pointer_high = 0;
		vcpu->vmcs.control_EPT_pointer_full = __hva2spa__((u32)vcpu->vmx_vaddr_ept_pml4_table) | 0x1E; //page walk of 4 and WB memory
		vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 15); //disable CR3 load exiting
		vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 16); //disable CR3 store exiting
		printf("\nCPU(0x%02x): Activated VMX EPTs.", vcpu->id);
	}
}
