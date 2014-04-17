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
// intel VMX arch. backend implementation
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf-core.h> 
#include <xc-x86.h>
#include <xc-x86vmx.h>


// initialize memory protection structures for a given core (vcpu)
static void xmhf_memprot_arch_x86vmx_initialize(VCPU *vcpu){
	HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_INTEL);

/*	if(vcpu->isbsp){
	 printf("\n%s: BSP initializing HPT", __FUNCTION__);
	_vmx_gathermemorytypes(vcpu);
#ifndef __XMHF_VERIFICATION__	
	_vmx_setupEPT(vcpu);
#endif
	}
*/

	vcpu->vmcs.control_VMX_seccpu_based |= (1 << 1); //enable EPT
	vcpu->vmcs.control_VMX_seccpu_based |= (1 << 5); //enable VPID
	vcpu->vmcs.control_vpid = 1; //VPID=0 is reserved for hypervisor
	vcpu->vmcs.control_EPT_pointer_high = 0;
	vcpu->vmcs.control_EPT_pointer_full = hva2spa((void*)vcpu->vmx_vaddr_ept_pml4_table) | 0x1E; //page walk of 4 and WB memory
	vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 15); //disable CR3 load exiting
	vcpu->vmcs.control_VMX_cpu_based &= ~(1 << 16); //disable CR3 store exiting
}

//flush hardware page table mappings (TLB) 
void xmhf_memprot_arch_x86vmx_flushmappings(VCPU * vcpu){
  __vmx_invept(VMX_INVEPT_SINGLECONTEXT, 
          (u64)vcpu->vmcs.control_EPT_pointer_full);
}


u64 xmhf_memprot_arch_x86vmx_get_EPTP(VCPU *vcpu)
{
  HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_INTEL);
  return
    ((u64)(vcpu->vmcs.control_EPT_pointer_high) << 32)
    | (u64)(vcpu->vmcs.control_EPT_pointer_full);
}
void xmhf_memprot_arch_x86vmx_set_EPTP(VCPU *vcpu, u64 eptp)
{
  HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_INTEL);
  vcpu->vmcs.control_EPT_pointer_full = (u32)eptp;
  vcpu->vmcs.control_EPT_pointer_high = (u32)(eptp >> 32);
}

//set protection for a given physical memory address
void xmhf_memprot_arch_x86vmx_setprot(VCPU *vcpu, u64 gpa, u32 prottype){
  u32 pfn;
  u64 *pt;
  u32 flags =0;
  
#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
   	assert ( (vcpu != NULL) );
	assert ( ( (gpa < xcbootinfo->physmem_base) || 
							 (gpa >= (xcbootinfo->physmem_base + xcbootinfo->size)) 
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
  
  pfn = (u32)gpa / PAGE_SIZE_4K;	//grab page frame number
  pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
  
  //default is not-present, read-only, no-execute	
  pt[pfn] &= ~(u64)7; //clear all previous flags

  //map high level protection type to EPT protection bits
  if(prottype & MEMP_PROT_PRESENT){
	flags=1;	//present is defined by the read bit in EPT
	
	if(prottype & MEMP_PROT_READWRITE)
		flags |= 0x2;
		
	if(prottype & MEMP_PROT_EXECUTE)
		flags |= 0x4;
  }
  	
  //set new flags
  pt[pfn] |= flags; 
}

//get protection for a given physical memory address
u32 xmhf_memprot_arch_x86vmx_getprot(VCPU *vcpu, u64 gpa){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;	//grab page frame number
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
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

  if( entry & 0x4 )
	prottype |= MEMP_PROT_EXECUTE;
  else
	prottype |= MEMP_PROT_NOEXECUTE;

  return prottype;
}

//======================================================================
// global interfaces (functions) exported by this component

// initialize memory protection structures for a given core (vcpu)
//void xmhf_memprot_arch_initialize(VCPU *vcpu){
void xmhf_memprot_arch_initialize(u32 index_cpudata){
	VCPU *vcpu = (VCPU *)&g_bplt_vcpu[index_cpudata];
		xmhf_memprot_arch_x86vmx_initialize(vcpu);
}

// get level-1 page map address
u64 * xmhf_memprot_arch_get_lvl1_pagemap_address(context_desc_t context_desc){
	VCPU *vcpu = (VCPU *)&g_bplt_vcpu[context_desc.cpu_desc.id];
		return (u64 *)vcpu->vmx_vaddr_ept_p_tables;
}

//get level-2 page map address
u64 * xmhf_memprot_arch_get_lvl2_pagemap_address(context_desc_t context_desc){
	VCPU *vcpu = (VCPU *)&g_bplt_vcpu[context_desc.cpu_desc.id];

		return (u64 *)vcpu->vmx_vaddr_ept_pd_tables;
}

//get level-3 page map address
u64 * xmhf_memprot_arch_get_lvl3_pagemap_address(context_desc_t context_desc){
	VCPU *vcpu = (VCPU *)&g_bplt_vcpu[context_desc.cpu_desc.id];

		return (u64 *)vcpu->vmx_vaddr_ept_pdp_table;
}

//get level-4 page map address
u64 * xmhf_memprot_arch_get_lvl4_pagemap_address(context_desc_t context_desc){
	VCPU *vcpu = (VCPU *)&g_bplt_vcpu[context_desc.cpu_desc.id];

    return (u64 *)vcpu->vmx_vaddr_ept_pml4_table;
}

//get default root page map address
u64 * xmhf_memprot_arch_get_default_root_pagemap_address(context_desc_t context_desc){
	VCPU *vcpu = (VCPU *)&g_bplt_vcpu[context_desc.cpu_desc.id];
		return (u64*)vcpu->vmx_vaddr_ept_pml4_table;
} 

//flush hardware page table mappings (TLB) 
void xmhf_memprot_arch_flushmappings(context_desc_t context_desc){
    VCPU *vcpu = (VCPU *)&g_bplt_vcpu[context_desc.cpu_desc.id];
		xmhf_memprot_arch_x86vmx_flushmappings(vcpu);

}



//set protection for a given physical memory address
void xmhf_memprot_arch_setprot(context_desc_t context_desc, u64 gpa, u32 prottype){
	VCPU *vcpu = (VCPU *)&g_bplt_vcpu[context_desc.cpu_desc.id];
		xmhf_memprot_arch_x86vmx_setprot(vcpu, gpa, prottype);
}



//get protection for a given physical memory address
u32 xmhf_memprot_arch_getprot(context_desc_t context_desc, u64 gpa){
	VCPU *vcpu = (VCPU *)&g_bplt_vcpu[context_desc.cpu_desc.id];
		return xmhf_memprot_arch_x86vmx_getprot(vcpu, gpa);
}


void xmhf_memprot_arch_setsingularhpt(u64 hpt){
		u32 i;
		
		printf("\n%s: starting...", __FUNCTION__);
        for( i=0 ; i<g_midtable_numentries; i++ )  {
				xmhf_memprot_arch_x86vmx_set_EPTP((VCPU *)g_midtable[i].vcpu_vaddr_ptr, hpt);

			printf("\n CPU %02x: set HPT to %x",  i, (u32)hpt);
        }
		printf("\n%s: done.", __FUNCTION__);
}

//get HPT root pointer
u64 xmhf_memprot_arch_getHPTroot(context_desc_t context_desc){
	VCPU *vcpu = (VCPU *)&g_bplt_vcpu[context_desc.cpu_desc.id];
	return xmhf_memprot_arch_x86vmx_get_EPTP(vcpu);
}


//set HPT entry
void xmhf_memprot_arch_hpt_setentry(context_desc_t context_desc, u64 hpt_paddr, u64 entry){
	VCPU *vcpu = (VCPU *)&g_bplt_vcpu[context_desc.cpu_desc.id];
	u64 *hpt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
	u32 hpt_index = (u32)hpt_paddr / PAGE_SIZE_4K;
	
	hpt[hpt_index] = entry;

	return;
}
