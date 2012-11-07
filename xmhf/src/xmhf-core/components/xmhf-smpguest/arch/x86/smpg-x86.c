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

// EMHF symmetric multiprocessor (SMP) guest component
// x86 arch. backend implementation
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h> 

//initialize SMP guest logic
void emhf_smpguest_arch_initialize(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);

#if defined(__MP_VERSION__)	
	//TODOs:
	//1. conceal g_midtable_numentries behind "baseplatform" component interface
	//2. remove g_isl dependency
	//if we are the BSP and platform has more than 1 CPU, setup SIPI interception to tackle SMP guests
	if(vcpu->isbsp && (g_midtable_numentries > 1)){
		if(vcpu->cpu_vendor == CPU_VENDOR_AMD){ 
			emhf_smpguest_arch_x86svm_initialize(vcpu);
			printf("\nCPU(0x%02x): setup x86svm SMP guest capabilities", vcpu->id);
		}else{	//CPU_VENDOR_INTEL
			emhf_smpguest_arch_x86vmx_initialize(vcpu);
			printf("\nCPU(0x%02x): setup x86vmx SMP guest capabilities", vcpu->id);
		}
	}else{ //we are an AP, so just wait for SIPI signal
			printf("\nCPU(0x%02x): AP, waiting for SIPI signal...", vcpu->id);
			while(!vcpu->sipireceived);
			printf("\nCPU(0x%02x): SIPI signal received, vector=0x%02x", vcpu->id, vcpu->sipivector);
	
			//g_isl->hvm_initialize_csrip(vcpu, ((vcpu->sipivector * PAGE_SIZE_4K) >> 4),
			//	 (vcpu->sipivector * PAGE_SIZE_4K), 0x0ULL);
			
			//perform required setup after a guest awakens a new CPU
			emhf_smpguest_arch_x86_postCPUwakeup(vcpu);
	}
#else
	//UP version, we just let the BSP continue and stall the APs
	if(vcpu->isbsp)
		return;
	
	//we are an AP, so just lockup
	printf("\nCPU(0x%02x): AP, locked!", vcpu->id);
	while(1);
#endif

	
}


//handle LAPIC access #DB (single-step) exception event
void emhf_smpguest_arch_x86_eventhandler_dbexception(VCPU *vcpu, 
	struct regs *r){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){ 
		emhf_smpguest_arch_x86svm_eventhandler_dbexception(vcpu, r);
	}else{	//CPU_VENDOR_INTEL
		emhf_smpguest_arch_x86vmx_eventhandler_dbexception(vcpu, r);
	}
}

//handle LAPIC access #NPF (nested page fault) event
void emhf_smpguest_arch_x86_eventhandler_hwpgtblviolation(VCPU *vcpu, u32 gpa, u32 errorcode){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){ 
		emhf_smpguest_arch_x86svm_eventhandler_hwpgtblviolation(vcpu, gpa, errorcode);
	}else{	//CPU_VENDOR_INTEL
		emhf_smpguest_arch_x86vmx_eventhandler_hwpgtblviolation(vcpu, gpa, errorcode);
	}	
	
}

//quiescing handler for #NMI (non-maskable interrupt) exception event
void emhf_smpguest_arch_x86_eventhandler_nmiexception(VCPU *vcpu, struct regs *r){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){ 
		emhf_smpguest_arch_x86svm_eventhandler_nmiexception(vcpu, r);
	}else{	//CPU_VENDOR_INTEL
		emhf_smpguest_arch_x86vmx_eventhandler_nmiexception(vcpu, r);
	}		
}	

//perform required setup after a guest awakens a new CPU
void emhf_smpguest_arch_x86_postCPUwakeup(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		emhf_smpguest_arch_x86svm_postCPUwakeup(vcpu);
	}else{ //CPU_VENDOR_INTEL
		emhf_smpguest_arch_x86vmx_postCPUwakeup(vcpu);
	}
	
}

//walk guest page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
u8 * emhf_smpguest_arch_walk_pagetables(VCPU *vcpu, u32 vaddr){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		return emhf_smpguest_arch_x86svm_walk_pagetables(vcpu, vaddr);
	}else{ //CPU_VENDOR_INTEL
		return emhf_smpguest_arch_x86vmx_walk_pagetables(vcpu, vaddr);
	}
}

//quiesce interface to switch all guest cores into hypervisor mode
void emhf_smpguest_arch_quiesce(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){ 
		emhf_smpguest_arch_x86svm_quiesce(vcpu);
	}else{	//CPU_VENDOR_INTEL
		emhf_smpguest_arch_x86vmx_quiesce(vcpu);
	}	
}

//endquiesce interface to resume all guest cores after a quiesce
void emhf_smpguest_arch_endquiesce(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){ 
		emhf_smpguest_arch_x86svm_endquiesce(vcpu);
	}else{	//CPU_VENDOR_INTEL
		emhf_smpguest_arch_x86vmx_endquiesce(vcpu);
	}		
}
