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

// EMHF symmetric multiprocessor (SMP) guest component
// implementation
// author: amit vasudevan (amitvasudevan@acm.org)

#include <emhf.h> 

// we implement the smp guest component in a way that if
// we run a uniprocessor guest then we can safely do away
// with this component

// functions exported
// 1. g_isl->hvm_apic_setup(vcpu); //runtime
// 2. vmx/svm_lapic_access_handler(vcpu, gpa, errorcode); //eventhub
// 3. vmx/svm_lapic_access_dbexception(vcpu, r); //eventhub


//initialize SMP guest logic
void emhf_smpguest_initialize(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){ 
		emhf_smpguest_arch_x86svm_initialize(vcpu);
		printf("\nCPU(0x%02x): setup x86svm SMP guest capabilities", vcpu->id);
	}else{	//CPU_VENDOR_INTEL
		emhf_smpguest_arch_x86vmx_initialize(vcpu);
		printf("\nCPU(0x%02x): setup x86vmx SMP guest capabilities", vcpu->id);
	}
}

//handle LAPIC access #DB (single-step) exception event
void emhf_smpguest_eventhandler_dbexception(VCPU *vcpu, 
	struct regs *r){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){ 
		emhf_smpguest_arch_x86svm_eventhandler_dbexception(vcpu, r);
	}else{	//CPU_VENDOR_INTEL
		emhf_smpguest_arch_x86vmx_eventhandler_dbexception(vcpu, r);
	}
}

//handle LAPIC access #NPF (nested page fault) event
void emhf_smpguest_eventhandler_hwpgtblviolation(VCPU *vcpu, u32 gpa, u32 errorcode){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){ 
		emhf_smpguest_arch_x86svm_eventhandler_hwpgtblviolation(vcpu, gpa, errorcode);
	}else{	//CPU_VENDOR_INTEL
		emhf_smpguest_arch_x86vmx_eventhandler_hwpgtblviolation(vcpu, gpa, errorcode);
	}	
	
}

//quiesce interface to switch all guest cores into hypervisor mode
void emhf_smpguest_quiesce(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){ 
		emhf_smpguest_arch_x86svm_quiesce(vcpu);
	}else{	//CPU_VENDOR_INTEL
		emhf_smpguest_arch_x86vmx_quiesce(vcpu);
	}	
}

//endquiesce interface to resume all guest cores after a quiesce
void emhf_smpguest_endquiesce(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){ 
		emhf_smpguest_arch_x86svm_endquiesce(vcpu);
	}else{	//CPU_VENDOR_INTEL
		emhf_smpguest_arch_x86vmx_endquiesce(vcpu);
	}		
}


