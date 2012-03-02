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

#include <emhf.h> 

// initialize memory protection structures for a given core (vcpu)
void emhf_memprot_initialize(VCPU *vcpu){
	emhf_memprot_arch_initialize(vcpu);
}

// get level-1 page map address
u64 * emhf_memprot_get_lvl1_pagemap_address(VCPU *vcpu){
	return emhf_memprot_arch_get_lvl1_pagemap_address(vcpu);
}

//get level-2 page map address
u64 * emhf_memprot_get_lvl2_pagemap_address(VCPU *vcpu){
	return emhf_memprot_arch_get_lvl2_pagemap_address(vcpu);
}

//get level-3 page map address
u64 * emhf_memprot_get_lvl3_pagemap_address(VCPU *vcpu){
	return emhf_memprot_arch_get_lvl3_pagemap_address(vcpu);
}

//get level-4 page map address
u64 * emhf_memprot_get_lvl4_pagemap_address(VCPU *vcpu){
	return emhf_memprot_arch_get_lvl4_pagemap_address(vcpu);
}

//get default root page map address
u64 * emhf_memprot_get_default_root_pagemap_address(VCPU *vcpu){
	return emhf_memprot_arch_get_default_root_pagemap_address(vcpu);
} 


//flush hardware page table mappings (TLB) 
void emhf_memprot_flushmappings(VCPU *vcpu){
	emhf_memprot_arch_flushmappings(vcpu);
}


//set protection for a given physical memory address
void emhf_memprot_setprot(VCPU *vcpu, u64 gpa, u32 prottype){
	EV_FNCONTRACT_DOMAIN ( (vcpu != NULL) );
	EV_FNCONTRACT_DOMAIN ( ( (gpa < rpb->XtVmmRuntimePhysBase) || 
							 (gpa >= (rpb->XtVmmRuntimePhysBase + rpb->XtVmmRuntimeSize)) 
						   ) );
	EV_FNCONTRACT_DOMAIN ( ( (prottype > 0)	&& 
	                         (prottype <= MEMP_PROT_MAXVALUE) 
	                       ) );						
	EV_FNCONTRACT_DOMAIN(
	 (prottype == MEMP_PROT_NOTPRESENT) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READONLY) && (prottype & MEMP_PROT_EXECUTE)) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READWRITE) && (prottype & MEMP_PROT_EXECUTE)) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READONLY) && (prottype & MEMP_PROT_NOEXECUTE)) ||
	 ((prottype & MEMP_PROT_PRESENT) && (prottype & MEMP_PROT_READWRITE) && (prottype & MEMP_PROT_NOEXECUTE)) 
	);

	emhf_memprot_arch_setprot(vcpu, gpa, prottype);
}


//get protection for a given physical memory address
u32 emhf_memprot_getprot(VCPU *vcpu, u64 gpa){
	return emhf_memprot_arch_getprot(vcpu, gpa);
}


