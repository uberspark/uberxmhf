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

// EMHF SMP guest component 
// declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_SMPGUEST_H__
#define __EMHF_SMPGUEST_H__

//bring in arch. specific declarations
//#include <arch/xmhf-smpguest-arch.h>


#ifndef __ASSEMBLY__

void xmhf_richguest_initialize(u32 index_cpudata_bsp);
void xmhf_richguest_arch_initialize(u32 index_cpudata_bsp);

//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------

//initialize SMP guest logic
//void xmhf_smpguest_arch_initialize(VCPU *vcpu);
void xmhf_smpguest_arch_initialize(context_desc_t context_desc);


//walk guest page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
u8 * xmhf_smpguest_arch_walk_pagetables(context_desc_t context_desc, u32 vaddr);

//perform required setup after a guest awakens a new CPU
//void xmhf_smpguest_arch_postCPUwakeup(VCPU *vcpu);
void xmhf_smpguest_arch_postCPUwakeup(context_desc_t context_desc);

//handle LAPIC access #DB (single-step) exception event
void xmhf_smpguest_arch_eventhandler_dbexception(context_desc_t context_desc, 
	struct regs *r);

//handle LAPIC access #NPF (nested page fault) event
void xmhf_smpguest_arch_eventhandler_hwpgtblviolation(context_desc_t context_desc, u32 gpa, u32 errorcode);


//----------------------------------------------------------------------
//exported DATA 
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//exported FUNCTIONS 
//----------------------------------------------------------------------




//initialize SMP guest logic
//void xmhf_smpguest_initialize(VCPU *vcpu);
void xmhf_smpguest_initialize(context_desc_t context_desc);

//quiesce interface to switch all guest cores into hypervisor mode
//void xmhf_smpguest_quiesce(VCPU *vcpu);

//endquiesce interface to resume all guest cores after a quiesce
//void xmhf_smpguest_endquiesce(VCPU *vcpu);

//walk guest page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
u8 * xmhf_smpguest_walk_pagetables(context_desc_t context_desc, u32 vaddr);



#endif	//__ASSEMBLY__

#endif //__EMHF_SMPGUEST_H__
