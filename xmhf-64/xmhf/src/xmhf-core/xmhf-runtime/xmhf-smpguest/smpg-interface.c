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
// implementation
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>

// we implement the smp guest component in a way that if
// we run a uniprocessor guest then we can safely do away
// with this component

// functions exported
// 1. g_isl->hvm_apic_setup(vcpu); //runtime
// 2. vmx/svm_lapic_access_handler(vcpu, gpa, errorcode); //eventhub
// 3. vmx/svm_lapic_access_dbexception(vcpu, r); //eventhub


//initialize SMP guest logic
void xmhf_smpguest_initialize(VCPU *vcpu){
	xmhf_smpguest_arch_initialize(vcpu);
}


//quiesce interface to switch all guest cores into hypervisor mode
static void xmhf_smpguest_quiesce(VCPU *vcpu) __attribute__((unused));
static void xmhf_smpguest_quiesce(VCPU *vcpu){
	xmhf_smpguest_arch_quiesce(vcpu);
}

//endquiesce interface to resume all guest cores after a quiesce
static void xmhf_smpguest_endquiesce(VCPU *vcpu) __attribute__((unused));
static void xmhf_smpguest_endquiesce(VCPU *vcpu){
	xmhf_smpguest_arch_endquiesce(vcpu);
}


//walk guest page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
u8 * xmhf_smpguest_walk_pagetables(VCPU *vcpu, u32 vaddr){
	return xmhf_smpguest_arch_walk_pagetables(vcpu, vaddr);
}

// Inject NMI to the guest when the guest is ready to receive it (i.e. when the
// guest is not running NMI handler)
// The NMI window VMEXIT is used to make sure the guest is able to receive NMIs
//
// This function should be called in intercept handlers (a.k.a. VMEXIT
// handlers). Otherwise, the caller needs to make sure that this function is
// called after xmhf_smpguest_arch_x86vmx_mhv_nmi_disable().
void xmhf_smpguest_inject_nmi(VCPU *vcpu)
{
	xmhf_smpguest_arch_inject_nmi(vcpu);
}

// Block NMIs using software
// This function must be called in intercept handlers (a.k.a. VMEXIT handlers),
// because it edits VMCS through vcpu->vmcs and expects the intercept handler
// to write the update to the hardware VMCS later.
void xmhf_smpguest_nmi_block(VCPU *vcpu)
{
	xmhf_smpguest_arch_nmi_block(vcpu);
}

// Unblock NMIs using software
// This function must be called in intercept handlers (a.k.a. VMEXIT handlers),
// because it edits VMCS through vcpu->vmcs and expects the intercept handler
// to write the update to the hardware VMCS later.
void xmhf_smpguest_nmi_unblock(VCPU *vcpu)
{
	xmhf_smpguest_arch_nmi_unblock(vcpu);
}
