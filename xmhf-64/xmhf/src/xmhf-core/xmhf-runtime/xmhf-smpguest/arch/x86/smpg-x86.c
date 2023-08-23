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
void xmhf_smpguest_arch_initialize(VCPU *vcpu){
	HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);

	/*
	 * When DRT is enabled, hypervisor will block NMIs. This may cause failures
	 * in quiescing. So unblock NMIs here (regardless of DRT to be safe).
	 */
	if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
		xmhf_smpguest_arch_x86vmx_unblock_nmi();
	}

#if defined(__MP_VERSION__)
	//TODOs:
	//1. conceal g_midtable_numentries behind "baseplatform" component interface
	//2. remove g_isl dependency
	// Only 1 CPU available, just make sure we are BSP and do nothing
	if (g_midtable_numentries <= 1) {
		HALT_ON_ERRORCOND(vcpu->isbsp);
		if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
			/* Not implmented */
			HALT();
		}else{	//CPU_VENDOR_INTEL
			xmhf_smpguest_arch_x86vmx_initialize(vcpu, 0);
			printf("CPU(0x%02x): x86vmx SMP but only one CPU\n", vcpu->id);
		}
		return;
	}

	//if we are the BSP and platform has more than 1 CPU, setup SIPI interception to tackle SMP guests
	if(vcpu->isbsp){
		if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
			xmhf_smpguest_arch_x86svm_initialize(vcpu);
			printf("CPU(0x%02x): setup x86svm SMP guest capabilities\n", vcpu->id);
		}else{	//CPU_VENDOR_INTEL
			xmhf_smpguest_arch_x86vmx_initialize(vcpu, 1);
			printf("CPU(0x%02x): setup x86vmx SMP guest capabilities\n", vcpu->id);
		}
	}else{ //we are an AP, so just wait for SIPI signal
			printf("CPU(0x%02x): AP, waiting for SIPI signal...\n", vcpu->id);
			#ifndef __XMHF_VERIFICATION__
			while (!vcpu->sipireceived) {
				xmhf_cpu_relax();
			}
			#endif
			printf("CPU(0x%02x): SIPI signal received, vector=0x%02x\n", vcpu->id, vcpu->sipivector);

			//g_isl->hvm_initialize_csrip(vcpu, ((vcpu->sipivector * PAGE_SIZE_4K) >> 4),
			//	 (vcpu->sipivector * PAGE_SIZE_4K), 0x0ULL);

			//perform required setup after a guest awakens a new CPU
			xmhf_smpguest_arch_x86_postCPUwakeup(vcpu);
	}
#else
	//UP version, we just let the BSP continue and stall the APs
	if(vcpu->isbsp)
		return;

	//we are an AP, so just lockup
	printf("CPU(0x%02x): AP, locked!\n", vcpu->id);
	while(1);
#endif


}


//handle LAPIC access #DB (single-step) exception event
void xmhf_smpguest_arch_x86_eventhandler_dbexception(VCPU *vcpu,
	struct regs *r){
	HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		xmhf_smpguest_arch_x86svm_eventhandler_dbexception(vcpu, r);
	}else{	//CPU_VENDOR_INTEL
		xmhf_smpguest_arch_x86vmx_eventhandler_dbexception(vcpu, r);
	}
}

//handle LAPIC access #NPF (nested page fault) event
void xmhf_smpguest_arch_x86_eventhandler_hwpgtblviolation(VCPU *vcpu, u32 gpa, u32 errorcode){
	HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		xmhf_smpguest_arch_x86svm_eventhandler_hwpgtblviolation(vcpu, gpa, errorcode);
	}else{	//CPU_VENDOR_INTEL
		xmhf_smpguest_arch_x86vmx_eventhandler_hwpgtblviolation(vcpu, gpa, errorcode);
	}

}

//quiescing handler for #NMI (non-maskable interrupt) exception event
void xmhf_smpguest_arch_x86_eventhandler_nmiexception(VCPU *vcpu, struct regs *r, u32 from_guest){
	HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		xmhf_smpguest_arch_x86svm_eventhandler_nmiexception(vcpu, r);
	}else{	//CPU_VENDOR_INTEL
		xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(vcpu, r, from_guest);
	}
}

//perform required setup after a guest awakens a new CPU
void xmhf_smpguest_arch_x86_postCPUwakeup(VCPU *vcpu){
	HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);

	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		xmhf_smpguest_arch_x86svm_postCPUwakeup(vcpu);
	}else{ //CPU_VENDOR_INTEL
		xmhf_smpguest_arch_x86vmx_postCPUwakeup(vcpu);
	}

}

//walk guest page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
u8 * xmhf_smpguest_arch_walk_pagetables(VCPU *vcpu, u32 vaddr){
	HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);

	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		return xmhf_smpguest_arch_x86svm_walk_pagetables(vcpu, vaddr);
	}else{ //CPU_VENDOR_INTEL
		return xmhf_smpguest_arch_x86vmx_walk_pagetables(vcpu, vaddr);
	}
}

//quiesce interface to switch all guest cores into hypervisor mode
void xmhf_smpguest_arch_quiesce(VCPU *vcpu){
	HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		xmhf_smpguest_arch_x86svm_quiesce(vcpu);
	}else{	//CPU_VENDOR_INTEL
		xmhf_smpguest_arch_x86vmx_quiesce(vcpu);
	}
}

//endquiesce interface to resume all guest cores after a quiesce
void xmhf_smpguest_arch_endquiesce(VCPU *vcpu){
	HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		xmhf_smpguest_arch_x86svm_endquiesce(vcpu);
	}else{	//CPU_VENDOR_INTEL
		xmhf_smpguest_arch_x86vmx_endquiesce(vcpu);
	}
}

// Inject NMI to the guest when the guest is ready to receive it (i.e. when the
// guest is not running NMI handler)
// The NMI window VMEXIT is used to make sure the guest is able to receive NMIs
//
// This function should be called in intercept handlers (a.k.a. VMEXIT
// handlers). Otherwise, the caller needs to make sure that this function is
// called after xmhf_smpguest_arch_x86vmx_mhv_nmi_disable().
void xmhf_smpguest_arch_inject_nmi(VCPU *vcpu)
{
	HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		HALT_ON_ERRORCOND(0 && "AMD not supported");
	}else{	//CPU_VENDOR_INTEL
		xmhf_smpguest_arch_x86vmx_inject_nmi(vcpu);
	}
}

// Block NMIs using software
// This function must be called in intercept handlers (a.k.a. VMEXIT handlers),
// because it edits VMCS through vcpu->vmcs and expects the intercept handler
// to write the update to the hardware VMCS later.
void xmhf_smpguest_arch_nmi_block(VCPU *vcpu)
{
	HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		HALT_ON_ERRORCOND(0 && "AMD not supported");
	}else{	//CPU_VENDOR_INTEL
		xmhf_smpguest_arch_x86vmx_nmi_block(vcpu);
	}
}

// Unblock NMIs using software
// This function must be called in intercept handlers (a.k.a. VMEXIT handlers),
// because it edits VMCS through vcpu->vmcs and expects the intercept handler
// to write the update to the hardware VMCS later.
void xmhf_smpguest_arch_nmi_unblock(VCPU *vcpu)
{
	HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
		HALT_ON_ERRORCOND(0 && "AMD not supported");
	}else{	//CPU_VENDOR_INTEL
		xmhf_smpguest_arch_x86vmx_nmi_unblock(vcpu);
	}
}
