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
// declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_MEMPROT_H__
#define __EMHF_MEMPROT_H__


#ifndef __ASSEMBLY__

// memory protection types
#define MEMP_PROT_NOTPRESENT	(1)	// page not present
#define	MEMP_PROT_PRESENT		(2)	// page present
#define MEMP_PROT_READONLY		(4)	// page read-only
#define MEMP_PROT_READWRITE		(8) // page read-write
#define MEMP_PROT_EXECUTE		(16) // page execute
#define MEMP_PROT_NOEXECUTE		(32) // page no-execute

//----------------------------------------------------------------------
//exported DATA 
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//exported FUNCTIONS 
//----------------------------------------------------------------------

//initialize memory protection for a core
void emhf_memprot_initialize(VCPU *vcpu);

// get level-1 page map address
u64 * emhf_memprot_get_lvl1_pagemap_address(VCPU *vcpu);

//get level-2 page map address
u64 * emhf_memprot_get_lvl2_pagemap_address(VCPU *vcpu);

//get level-3 page map address
u64 * emhf_memprot_get_lvl3_pagemap_address(VCPU *vcpu);

//get level-4 page map address
u64 * emhf_memprot_get_lvl4_pagemap_address(VCPU *vcpu);

//get default root page map address
u64 * emhf_memprot_get_default_root_pagemap_address(VCPU *vcpu);

//flush hardware page table mappings (TLB) 
void emhf_memprot_flushmappings(VCPU *vcpu);

//set protection for a given physical memory address
void emhf_memprot_setprot(VCPU *vcpu, u64 gpa, u32 prottype);

//get protection for a given physical memory address
u32 emhf_memprot_getprot(VCPU *vcpu, u64 gpa);


//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------

//initialize memory protection for a core
void emhf_memprot_arch_initialize(VCPU *vcpu);

// get level-1 page map address
u64 * emhf_memprot_arch_get_lvl1_pagemap_address(VCPU *vcpu);

//get level-2 page map address
u64 * emhf_memprot_arch_get_lvl2_pagemap_address(VCPU *vcpu);

//get level-3 page map address
u64 * emhf_memprot_arch_get_lvl3_pagemap_address(VCPU *vcpu);

//get level-4 page map address
u64 * emhf_memprot_arch_get_lvl4_pagemap_address(VCPU *vcpu);

//get default root page map address
u64 * emhf_memprot_arch_get_default_root_pagemap_address(VCPU *vcpu);

//flush hardware page table mappings (TLB) 
void emhf_memprot_arch_flushmappings(VCPU *vcpu);

//set protection for a given physical memory address
void emhf_memprot_arch_setprot(VCPU *vcpu, u64 gpa, u32 prottype);

//get protection for a given physical memory address
u32 emhf_memprot_arch_getprot(VCPU *vcpu, u64 gpa);


//----------------------------------------------------------------------
//x86 ARCH. INTERFACES
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------
void emhf_memprot_arch_x86vmx_initialize(VCPU *vcpu);	//initialize memory protection for a core
void emhf_memprot_arch_x86vmx_flushmappings(VCPU *vcpu); //flush hardware page table mappings (TLB) 
void emhf_memprot_arch_x86vmx_setprot(VCPU *vcpu, u64 gpa, u32 prottype); //set protection for a given physical memory address
u32 emhf_memprot_arch_x86vmx_getprot(VCPU *vcpu, u64 gpa); //get protection for a given physical memory address
u64 emhf_memprot_arch_x86vmx_get_EPTP(VCPU *vcpu); // get or set EPTP (only valid on Intel)
void emhf_memprot_arch_x86vmx_set_EPTP(VCPU *vcpu, u64 eptp);

//----------------------------------------------------------------------
//x86svm SUBARCH. INTERFACES
//----------------------------------------------------------------------

void emhf_memprot_arch_x86svm_initialize(VCPU *vcpu);	//initialize memory protection for a core
void emhf_memprot_arch_x86svm_flushmappings(VCPU *vcpu); //flush hardware page table mappings (TLB) 
void emhf_memprot_arch_x86svm_setprot(VCPU *vcpu, u64 gpa, u32 prottype); //set protection for a given physical memory address
u32 emhf_memprot_arch_x86svm_getprot(VCPU *vcpu, u64 gpa); //get protection for a given physical memory address
u64 emhf_memprot_arch_x86svm_get_h_cr3(VCPU *vcpu); // get or set host cr3 (only valid on AMD)
void emhf_memprot_arch_x86svm_set_h_cr3(VCPU *vcpu, u64 hcr3);















#endif	//__ASSEMBLY__

#endif //__EMHF_MEMPROT_H__
