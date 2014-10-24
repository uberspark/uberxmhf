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

// XMHF core API -- x86vmx arch. backend
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcapi.h>
#include <xcihub.h>

///////////////////////////////////////////////////////////////////////////////
//HPT related core APIs

__attribute__((aligned(4096))) static xc_partition_hptdata_x86vmx_t _hpt_data[MAX_PRIMARY_PARTITIONS];

u64 xc_api_hpt_arch_gethptroot(context_desc_t context_desc){
    return (u64)&_hpt_data[context_desc.partition_desc.partition_index].vmx_ept_pml4_table;
}

void xc_api_hpt_arch_establishshape(u32 partition_index){
	u64 *pml4_table, *pdp_table, *pd_table;
	u32 i, j, paddr=0;

	pml4_table = (u64 *)_hpt_data[partition_index].vmx_ept_pml4_table;
	pml4_table[0] = (u64) (hva2spa((void*)_hpt_data[partition_index].vmx_ept_pdp_table) | 0x7);

	pdp_table = (u64 *)_hpt_data[partition_index].vmx_ept_pdp_table;

	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		pdp_table[i] = (u64) ( hva2spa((void*)_hpt_data[partition_index].vmx_ept_pd_tables + (PAGE_SIZE_4K * i)) | 0x7 );
		pd_table = (u64 *)  ((u32)_hpt_data[partition_index].vmx_ept_pd_tables + (PAGE_SIZE_4K * i)) ;

		for(j=0; j < PAE_PTRS_PER_PDT; j++){
			pd_table[j] = (u64) ( hva2spa((void*)_hpt_data[partition_index].vmx_ept_p_tables + (PAGE_SIZE_4K * ((i*PAE_PTRS_PER_PDT)+j))) | 0x7 );
		}
	}
}


void xc_api_hpt_arch_flushcaches(context_desc_t context_desc){

    __vmx_invept(VMX_INVEPT_SINGLECONTEXT,
          (u64)xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_EPT_POINTER_FULL));
        return;
}

u64 xc_api_hpt_arch_getentry(context_desc_t context_desc, u64 gpa){
	u64 entry;

	HALT_ON_ERRORCOND( context_desc.partition_desc.partition_index != XC_PARTITION_INDEX_INVALID );

	{
		u64 *hpt = (u64 *)_hpt_data[context_desc.partition_desc.partition_index].vmx_ept_p_tables;
		u32 hpt_index = (u32)gpa / PAGE_SIZE_4K;

		entry = hpt[hpt_index];
	}

	return entry;
}

void xc_api_hpt_arch_setentry(context_desc_t context_desc, u64 gpa, u64 entry){
	HALT_ON_ERRORCOND( context_desc.partition_desc.partition_index != XC_PARTITION_INDEX_INVALID );

	{
		u64 *hpt = (u64 *)_hpt_data[context_desc.partition_desc.partition_index].vmx_ept_p_tables;
		u32 hpt_index = (u32)gpa / PAGE_SIZE_4K;

		hpt[hpt_index] = entry;
	}

	return;
}


u32 xc_api_hpt_arch_getprot(context_desc_t context_desc, u64 gpa){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;	//grab page frame number
  u64 *pt = (u64 *)_hpt_data[context_desc.partition_desc.partition_index].vmx_ept_p_tables;
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

void xc_api_hpt_arch_setprot(context_desc_t context_desc, u64 gpa, u32 prottype){
  u32 pfn;
  u64 *pt;
  u32 flags =0;

  pfn = (u32)gpa / PAGE_SIZE_4K;	//grab page frame number
  pt = (u64 *)_hpt_data[context_desc.partition_desc.partition_index].vmx_ept_p_tables;

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


//walk level 2 page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
u64 xc_api_hpt_arch_lvl2pagewalk(context_desc_t context_desc, u64 gva){

   //_XDPRINTF_("%s(%u): gva=%016llx, starting...\n", __FUNCTION__, context_desc.cpu_desc.cpu_index);

  //if paging is disabled then physical address is the
  //supplied virtual address itself
	if( !((xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0) & CR0_PE) && (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0) & CR0_PG)) ){
	   //_XDPRINTF_("%s(%u): no paging in guest, return=%016llx...\n", __FUNCTION__, context_desc.cpu_desc.cpu_index,
       //        (u8 *)gpa2hva(gva));
		return (u8 *)gpa2hva(gva);
    }

  if((u32)xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR4) & CR4_PAE ){
    //PAE paging used by guest
    u32 kcr3 = (u32)xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR3);
    u32 pdpt_index, pd_index, pt_index, offset;
    u64 paddr;
    pdpt_t kpdpt;
    pdt_t kpd;
    pt_t kpt;
    u32 pdpt_entry, pd_entry, pt_entry;
    u32 tmp;

    // get fields from virtual addr
    pdpt_index = pae_get_pdpt_index(gva);
    pd_index = pae_get_pdt_index(gva);
    pt_index = pae_get_pt_index(gva);
    offset = pae_get_offset_4K_page(gva);

    //grab pdpt entry
    tmp = pae_get_addr_from_32bit_cr3(kcr3);
    kpdpt = (pdpt_t)((u32)tmp);
    pdpt_entry = kpdpt[pdpt_index];

    //grab pd entry
    if( !(pae_get_flags_from_pdpe(pdpt_entry) & _PAGE_PRESENT) ){
        //_XDPRINTF_("%s(%u): PAE (no-PD), return=%016llx...\n", __FUNCTION__, context_desc.cpu_desc.cpu_index,
        //       (u8 *)0xFFFFFFFFUL);
		return (u8 *)0xFFFFFFFFUL;
    }
    tmp = pae_get_addr_from_pdpe(pdpt_entry);
    kpd = (pdt_t)((u32)tmp);
    pd_entry = kpd[pd_index];

    if( !(pae_get_flags_from_pde(pd_entry) & _PAGE_PRESENT) ){
        //_XDPRINTF_("%s(%u): PAE (no-PT), return=%016llx...\n", __FUNCTION__, context_desc.cpu_desc.cpu_index,
        //       (u8 *)0xFFFFFFFFUL);

		return (u8 *)0xFFFFFFFFUL;
    }

    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (u32)pae_get_addr_from_pde(pd_entry);
      kpt = (pt_t)((u32)tmp);
      pt_entry  = kpt[pt_index];

	  if( !(pae_get_flags_from_pte(pt_entry) & _PAGE_PRESENT) ){
        //_XDPRINTF_("%s(%u): PAE (no-PTE), return=%016llx...\n", __FUNCTION__, context_desc.cpu_desc.cpu_index,
        //      (u8 *)0xFFFFFFFFUL);

		return (u8 *)0xFFFFFFFFUL;
	  }

      // find physical page base addr from page table entry
      paddr = (u64)pae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 2MB page
      offset = pae_get_offset_big(gva);
      paddr = (u64)pae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }

    //_XDPRINTF_("%s(%u): PAE), return=%016llx...\n", __FUNCTION__, context_desc.cpu_desc.cpu_index,
    //           (u8 *)gpa2hva(paddr));

    return (u8 *)gpa2hva(paddr);

  }else{
    //non-PAE 2 level paging used by guest
    u32 kcr3 = (u32)xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR3);
    u32 pd_index, pt_index, offset;
    u64 paddr;
    npdt_t kpd;
    npt_t kpt;
    u32 pd_entry, pt_entry;
    u32 tmp;

    // get fields from virtual addr
    pd_index = npae_get_pdt_index(gva);
    pt_index = npae_get_pt_index(gva);
    offset = npae_get_offset_4K_page(gva);

    // grab pd entry
    tmp = npae_get_addr_from_32bit_cr3(kcr3);
    kpd = (npdt_t)((u32)tmp);
    pd_entry = kpd[pd_index];


    if( !(npae_get_flags_from_pde(pd_entry) & _PAGE_PRESENT) ){
	    //_XDPRINTF_("%s(%u): non-PAE (no-PD), return=%016llx...\n", __FUNCTION__, context_desc.cpu_desc.cpu_index,
        //       (u8 *)0xFFFFFFFFUL);

		return (u8 *)0xFFFFFFFFUL;
    }

    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (u32)npae_get_addr_from_pde(pd_entry);
      kpt = (npt_t)((u32)tmp);
      pt_entry  = kpt[pt_index];

      if( !(npae_get_flags_from_pte(pt_entry) & _PAGE_PRESENT) ){
	    //_XDPRINTF_("%s(%u): non-PAE (no-PTE), return=%016llx...\n", __FUNCTION__, context_desc.cpu_desc.cpu_index,
        //       (u8 *)0xFFFFFFFFUL);

		return (u8 *)0xFFFFFFFFUL;
      }

      // find physical page base addr from page table entry
      paddr = (u64)npae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 4MB page
      offset = npae_get_offset_big(gva);
      paddr = (u64)npae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }

    //_XDPRINTF_("%s(%u): non-PAE, return=%016llx...\n", __FUNCTION__, context_desc.cpu_desc.cpu_index,
    //           (u8 *)gpa2hva(paddr));

    return (u8 *)gpa2hva(paddr);
  }
}












