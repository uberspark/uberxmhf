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

// EMHF memory protection component
// implementation
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>

// initialize memory protection structures for a given core (vcpu)
void xmhf_memprot_initialize(VCPU *vcpu){
	xmhf_memprot_arch_initialize(vcpu);
}

// get level-1 page map address
u64 * xmhf_memprot_get_lvl1_pagemap_address(VCPU *vcpu){
	return xmhf_memprot_arch_get_lvl1_pagemap_address(vcpu);
}

//get level-2 page map address
u64 * xmhf_memprot_get_lvl2_pagemap_address(VCPU *vcpu){
	return xmhf_memprot_arch_get_lvl2_pagemap_address(vcpu);
}

//get level-3 page map address
u64 * xmhf_memprot_get_lvl3_pagemap_address(VCPU *vcpu){
	return xmhf_memprot_arch_get_lvl3_pagemap_address(vcpu);
}

//get level-4 page map address
u64 * xmhf_memprot_get_lvl4_pagemap_address(VCPU *vcpu){
	return xmhf_memprot_arch_get_lvl4_pagemap_address(vcpu);
}

//get default root page map address
u64 * xmhf_memprot_get_default_root_pagemap_address(VCPU *vcpu){
	return xmhf_memprot_arch_get_default_root_pagemap_address(vcpu);
}

//flush the TLB of all nested page tables in the current core
void xmhf_memprot_flushmappings_localtlb(VCPU *vcpu, u32 flags){
	//printf("CPU(0x%02x): <xmhf_memprot_flushmappings_localtlb>\n", vcpu->id);
	xmhf_memprot_arch_flushmappings_localtlb(vcpu, flags);
}

// flush the TLB of all nested page tables in all cores
// Requirement: Other cores has been quiesced
void xmhf_memprot_flushmappings_alltlb(VCPU *vcpu, u32 flags)
{
    HALT_ON_ERRORCOND(g_vmx_quiesce);

    // Notice all cores to flush EPT TLB
	g_vmx_flush_all_tlb_signal = flags;

	// TODO: can move this call to xmhf_smpguest_arch_x86vmx_endquiesce(), save
	// a little bit of time.
	xmhf_memprot_flushmappings_localtlb(vcpu, flags);
}

//set protection for a given physical memory address
void xmhf_memprot_setprot(VCPU *vcpu, u64 gpa, u32 prottype){
#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
	assert ( (vcpu != NULL) );
	assert ( ( (gpa < rpb->XtVmmRuntimePhysBase) ||
							 (gpa >= (rpb->XtVmmRuntimePhysBase + rpb->XtVmmRuntimeSize))
						   ) );
	assert ( ( (prottype > 0)	&&
	                         (prottype <= MEMP_PROT_MAXVALUE)
	                       ) );
	assert (
	 (prottype == MEMP_PROT_NOTPRESENT) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READONLY) && (prottype & MEMP_PROT_EXECUTE)) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READWRITE) && (prottype & MEMP_PROT_EXECUTE)) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READONLY) && (prottype & MEMP_PROT_NOEXECUTE)) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READWRITE) && (prottype & MEMP_PROT_NOEXECUTE))
	);
#endif

	xmhf_memprot_arch_setprot(vcpu, gpa, prottype);
}


//get protection for a given physical memory address
u32 xmhf_memprot_getprot(VCPU *vcpu, u64 gpa){
	return xmhf_memprot_arch_getprot(vcpu, gpa);
}

// Is the given system paddr belong to mHV (XMHF + hypapp)?
bool xmhf_is_mhv_memory(spa_t spa)
{
	u64 base = rpb->XtVmmRuntimePhysBase;
	size_t size = rpb->XtVmmRuntimeSize;

	if((spa >= base) && (spa < base + size))
		return true;

	return false;
}

// On 32bit machine, we always return 0 - 4G as the machine physical address range, no matter how many memory is installed
// On 64-bit machine, the function queries the E820 map for the used memory region.
bool xmhf_get_machine_paddr_range(spa_t* machine_base_spa, spa_t* machine_limit_spa)
{
    return xmhf_arch_get_machine_paddr_range(machine_base_spa, machine_limit_spa);
}
