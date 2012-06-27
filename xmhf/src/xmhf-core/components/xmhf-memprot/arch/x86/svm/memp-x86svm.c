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
// AMD SVM arch. backend implementation
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h> 

//----------------------------------------------------------------------
// local (static) support function forward declarations
static void _svm_nptinitialize(u32 npt_pdpt_base, u32 npt_pdts_base, u32 npt_pts_base);

//======================================================================
// global interfaces (functions) exported by this component

// initialize memory protection structures for a given core (vcpu)
void emhf_memprot_arch_x86svm_initialize(VCPU *vcpu){
	struct _svm_vmcbfields *vmcb = (struct _svm_vmcbfields *)vcpu->vmcb_vaddr_ptr;
	
	ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD);
	
	_svm_nptinitialize(vcpu->npt_vaddr_ptr, vcpu->npt_vaddr_pdts, vcpu->npt_vaddr_pts);
	vmcb->n_cr3 = hva2spa((void*)vcpu->npt_vaddr_ptr);
	vmcb->np_enable |= 1ULL;
	vmcb->guest_asid = vcpu->npt_asid;
}

//----------------------------------------------------------------------
// local (static) support functions follow
//---npt initialize-------------------------------------------------------------
static void _svm_nptinitialize(u32 npt_pdpt_base, u32 npt_pdts_base, u32 npt_pts_base){
	pdpt_t pdpt;
	pdt_t pdt;
	pt_t pt;
	u32 paddr=0, i, j, k, y, z;
	u64 flags;

	printf("\n%s: pdpt=0x%08x, pdts=0x%08x, pts=0x%08x",
	__FUNCTION__, npt_pdpt_base, npt_pdts_base, npt_pts_base);

	pdpt=(pdpt_t)npt_pdpt_base;

	for(i = 0; i < PAE_PTRS_PER_PDPT; i++){
		y = (u32)hva2spa((void*)(npt_pdts_base + (i << PAGE_SHIFT_4K)));
		flags = (u64)(_PAGE_PRESENT);
		pdpt[i] = pae_make_pdpe((u64)y, flags);
		pdt=(pdt_t)((u32)npt_pdts_base + (i << PAGE_SHIFT_4K));
			
		for(j=0; j < PAE_PTRS_PER_PDT; j++){
			z=(u32)hva2spa((void*)(npt_pts_base + ((i * PAE_PTRS_PER_PDT + j) << (PAGE_SHIFT_4K))));
			flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER);
			pdt[j] = pae_make_pde((u64)z, flags);
			pt=(pt_t)((u32)npt_pts_base + ((i * PAE_PTRS_PER_PDT + j) << (PAGE_SHIFT_4K)));
			
			for(k=0; k < PAE_PTRS_PER_PT; k++){
				//the EMHF memory region includes the secure loader +
				//the runtime (core + app). this runs from 
				//(rpb->XtVmmRuntimePhysBase - PAGE_SIZE_2M) with a size
				//of (rpb->XtVmmRuntimeSize+PAGE_SIZE_2M)
				//make EMHF physical pages inaccessible
				if( (paddr >= (rpb->XtVmmRuntimePhysBase - PAGE_SIZE_2M)) &&
					(paddr < (rpb->XtVmmRuntimePhysBase + rpb->XtVmmRuntimeSize)) )
					flags = 0;	//not-present
				else
					flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER);	//present
				pt[k] = pae_make_pte((u64)paddr, flags);
				paddr+= PAGE_SIZE_4K;
			}
		}
	}
	
}

//flush hardware page table mappings (TLB) 
void emhf_memprot_arch_x86svm_flushmappings(VCPU *vcpu){
	((struct _svm_vmcbfields *)(vcpu->vmcb_vaddr_ptr))->tlb_control=VMCB_TLB_CONTROL_FLUSHALL;	
}

//set protection for a given physical memory address
void emhf_memprot_arch_x86svm_setprot(VCPU *vcpu, u64 gpa, u32 prottype){
  u32 pfn;
  u64 *pt;
  u64 flags=0;
  
  pfn = (u32)gpa / PAGE_SIZE_4K;	//grab page frame number
  pt = (u64 *)vcpu->npt_vaddr_pts;
 
  //default is not-present, read-only, no-execute	
  flags = (u64)0x8000000000000000ULL;

  //map high level protection type to NPT protection bits
  if(prottype & MEMP_PROT_PRESENT){
	flags |= 0x1;	//present 
	
	if(prottype & MEMP_PROT_READWRITE)
		flags |= 0x2; //read-write
		
	if(prottype & MEMP_PROT_EXECUTE)
		flags &= ~(u64)0x8000000000000000ULL; //execute
  }
  	
  pt[pfn] &= ~(u64)0x8000000000000003ULL; //clear all previous flags
  pt[pfn] |= flags; 					  //set new flags
}
	
//get protection for a given physical memory address
u32 emhf_memprot_arch_x86svm_getprot(VCPU *vcpu, u64 gpa){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;	//grab page frame number
  //u64 *pt = (u64 *)(u32)emhf_memprot_arch_x86svm_get_h_cr3(vcpu); //TODO: push into svm sub arch. backend
  u64 *pt = (u64 *)vcpu->npt_vaddr_pts;
  
  u64 entry = pt[pfn];
  u32 prottype;
  
  if(! (entry & 0x1) ){
	prottype = MEMP_PROT_NOTPRESENT;
	return prottype;
  }
 
  prottype = MEMP_PROT_PRESENT;
  
  if( entry & 0x2 )
	prottype |= MEMP_PROT_READWRITE;
  else
	prottype |= MEMP_PROT_READONLY;

  if( !(entry & 0x8000000000000000ULL) )
	prottype |= MEMP_PROT_EXECUTE;
  else
	prottype |= MEMP_PROT_NOEXECUTE;

  return prottype;
}

u64 emhf_memprot_arch_x86svm_get_h_cr3(VCPU *vcpu)
{
  ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD);
  return ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->n_cr3; 
}
void emhf_memprot_arch_x86svm_set_h_cr3(VCPU *vcpu, u64 n_cr3)
{
  ASSERT(vcpu->cpu_vendor == CPU_VENDOR_AMD);
  ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->n_cr3 = n_cr3;
}
