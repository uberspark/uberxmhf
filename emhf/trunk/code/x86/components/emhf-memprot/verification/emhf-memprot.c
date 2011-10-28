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

#define	CONST_LVL1_PAGEMAP_ADDRESS	0x00400000

#define CONST_EMHF_START_ADDRESS	0x00200000
#define CONST_EMHF_END_ADDRESS		0x00800000

// initialize memory protection structures for a given core (vcpu)
void emhf_memprot_initialize(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);

/*
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD){ 
		emhf_memprot_arch_svm_initialize(vcpu);
		printf("\nCPU(0x%02x): Activated SVM NPTs.", vcpu->id);
	}else{	//CPU_VENDOR_INTEL
		emhf_memprot_arch_vmx_initialize(vcpu);
		printf("\nCPU(0x%02x): Activated VMX EPTs.", vcpu->id);
	}
*/

}

// get level-1 page map address
inline hpt_pme_t* emhf_memprot_get_lvl1_pagemap_address(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);

/*	if (vcpu->cpu_vendor == CPU_VENDOR_AMD)
		return (hpt_pme_t*)vcpu->npt_vaddr_pts;
	else //CPU_VENDOR_INTEL
		return (hpt_pme_t*)vcpu->vmx_vaddr_ept_p_tables;
*/

	return (hpt_pme_t*)CONST_LVL1_PAGEMAP_ADDRESS;
}

//get level-2 page map address
inline hpt_pme_t* emhf_memprot_get_lvl2_pagemap_address(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);

/*	if (vcpu->cpu_vendor == CPU_VENDOR_AMD)
		return (hpt_pme_t*)vcpu->npt_vaddr_pdts;
	else //CPU_VENDOR_INTEL
		return (hpt_pme_t*)vcpu->vmx_vaddr_ept_pd_tables;
*/
	return (hpt_pme_t*)0;
}

//get level-3 page map address
inline hpt_pme_t* emhf_memprot_get_lvl3_pagemap_address(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD || vcpu->cpu_vendor == CPU_VENDOR_INTEL);

/*	if (vcpu->cpu_vendor == CPU_VENDOR_AMD)
		return (hpt_pme_t*)vcpu->npt_vaddr_ptr;
	else //CPU_VENDOR_INTEL
		return (hpt_pme_t*)vcpu->vmx_vaddr_ept_pdp_table;*/
		
	return (hpt_pme_t*)0;
}

//get level-4 page map address
inline hpt_pme_t* emhf_memprot_get_lvl4_pagemap_address(VCPU *vcpu){
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_INTEL);	//we don;t have a level-4 pagemap for AMD

    /*return (hpt_pme_t*)vcpu->vmx_vaddr_ept_pml4_table;*/
    return (hpt_pme_t*)0;
}

//set protection for a given page map entry
inline hpt_pme_t emhf_memprot_pagemapentry_setprot(hpt_type_t t, int lvl, hpt_pme_t entry, hpt_prot_t perms){
	hpt_pme_t rv=entry;
	ASSERT(hpt_lvl_is_valid(t, lvl));
	ASSERT(hpt_prot_is_valid(t, lvl, perms));

	/*if (t == HPT_TYPE_NORM) {
		rv = BR64_SET_BIT(rv, HPT_NORM_P_L21_MP_BIT, perms & HPT_PROT_READ_MASK);
		rv = BR64_SET_BIT(rv, HPT_NORM_RW_L21_MP_BIT, perms & HPT_PROT_WRITE_MASK);
	} else if (t == HPT_TYPE_PAE) {
		rv = BR64_SET_BIT(rv, HPT_PAE_P_L321_MP_BIT, perms & HPT_PROT_READ_MASK);
		if (lvl == 2 || lvl == 1) {
		  rv = BR64_SET_BIT(rv, HPT_PAE_RW_L21_MP_BIT, perms & HPT_PROT_WRITE_MASK);
		  rv = BR64_SET_BIT(rv, HPT_PAE_NX_L21_MP_BIT, !(perms & HPT_PROT_EXEC_MASK));
		}
	} else if (t == HPT_TYPE_LONG) {
		rv = BR64_SET_BIT(rv, HPT_LONG_P_L4321_MP_BIT, perms & HPT_PROT_READ_MASK);
		rv = BR64_SET_BIT(rv, HPT_LONG_RW_L4321_MP_BIT, perms & HPT_PROT_WRITE_MASK);
		rv = BR64_SET_BIT(rv, HPT_LONG_NX_L4321_MP_BIT, !(perms & HPT_PROT_EXEC_MASK));
	} else if (t == HPT_TYPE_EPT) {
		rv = BR64_SET_BR(rv, HPT_EPT_PROT_L4321_MP, perms);
	} else {
		ASSERT(0);
	}*/

	return rv;	
}

//get protection for a given page map entry
inline hpt_prot_t emhf_memprot_pagemapentry_getprot(hpt_type_t t, int lvl, hpt_pme_t entry){
	hpt_prot_t rv=HPT_PROTS_NONE;
	//bool r,w,x;
	ASSERT(hpt_lvl_is_valid(t, lvl));

	/*if (t == HPT_TYPE_NORM) {
		r= entry & MASKBIT64(HPT_NORM_P_L21_MP_BIT);
		w= entry & MASKBIT64(HPT_NORM_RW_L21_MP_BIT);
		x= r;
	} else if (t == HPT_TYPE_PAE) {
		r= entry & MASKBIT64(HPT_PAE_P_L321_MP_BIT);
		if (lvl == 2 || lvl == 1) {
			w= entry & MASKBIT64(HPT_PAE_RW_L21_MP_BIT);
			x= !(entry & MASKBIT64(HPT_PAE_NX_L21_MP_BIT));;
		} else {
			w=r;
			x=r;
		}
	} else if (t == HPT_TYPE_LONG) {
		r=entry & MASKBIT64(HPT_LONG_P_L4321_MP_BIT);
		w=entry & MASKBIT64(HPT_LONG_RW_L4321_MP_BIT);
		x=!(entry & MASKBIT64(HPT_LONG_NX_L4321_MP_BIT));
	} else if (t == HPT_TYPE_EPT) {
		r=entry & MASKBIT64(HPT_EPT_R_L4321_MP_BIT);
		w=entry & MASKBIT64(HPT_EPT_W_L4321_MP_BIT);
		x=entry & MASKBIT64(HPT_EPT_X_L4321_MP_BIT);
	} else {
		ASSERT(0);
	}
	
	rv = HPT_PROTS_NONE;
	rv = rv | (r ? HPT_PROT_READ_MASK : 0);
	rv = rv | (w ? HPT_PROT_WRITE_MASK : 0);
	rv = rv | (x ? HPT_PROT_EXEC_MASK : 0);*/

	return rv;
}

//----------------------------------------------------------------------
//verification driver function
//invoked using:
//cbmc emhf-memprot.c 
//-I<emhfcore>/trunk/code/x86/include -D__EMHF_VERIFICATION__ -D__NESTED_PAGING__ 
//--bounds-check --pointer-check
//where <emhfcore> is where the emhf repo is checked out
void main() {
	VCPU vcpu;
	u32 gpa=0, pfn;
	u64 *pt = emhf_memprot_get_lvl1_pagemap_address(&vcpu);

	assert( !(gpa >= CONST_EMHF_START_ADDRESS && gpa < CONST_EMHF_END_ADDRESS) );
	pfn = gpa >> 12;
	//emhf_memprot_pagemapentry_setprot needs to return a non-NULL
	//value else cbmc barfs:
	//Violated property:
	//file emhf-memprot.c line 148 function main
	//dereference failure: NULL plus offset pointer
	// !(SAME-OBJECT(pt, NULL))
	
	pt[pfn] = emhf_memprot_pagemapentry_setprot(HPT_TYPE_PAE, 1, pt[pfn], HPT_PROTS_R);
}
//----------------------------------------------------------------------
