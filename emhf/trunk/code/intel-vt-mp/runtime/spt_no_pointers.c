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

//------------------------------------------------------------------------------
// shadow_paging_npae.c
//
// intel vt-x hypervisor memory isolation using shadow paging (non-PAE mode)
//
// author: amit vasudevan (amitvasudevan@acm.org)

#include <types.h>
//#include <target.h>
#include <print.h>
//#include <processor.h>
//#include <msr.h>
//#include <vtx.h>
#include <paging.h>
//#include <io.h>
#include <str.h>
//#include <machine.h> 
//#include <error.h>
#include <shadow_paging_npae.h>
#include "../common/string.c"

//change the following two defines to suit your needs
//note: the limits MUST be page-aligned i.e multiple of 4096

//GPL is the maximum physical memory address that is valid during the validity check
//Original value 512*1024*1024
#define GUEST_PHYSICALMEMORY_LIMIT	 (4096*2)  //4MB guest PA


// GUEST_VIRTUALMEMORY_LIMIT allows you to tweak the number of iterations in loops in
// shadow_new_context and shadow_alloc_pt
// Max value is 4096*1024*1024
#define GUEST_VIRTUALMEMORY_LIMIT		 (4096*2)	//4GB guest VA 

u32 __shadow_npae_pd_table[1024];
u32 __shadow_npae_p_tables[1024];
u32 shadow_guest_CR3=0;

/*------------ Start for verification ------------*/

u32 nondet_u32();
u32* nondet_u32_ptr();
int nondet_int();


void main() {

  /* Initial Condition */
  u32 s_pdt_entry = __shadow_npae_pd_table[0];
  __CPROVER_assume( __shadow_npae_pd_table[0] == 0); // XXX define number of pages
  __CPROVER_assume(__shadow_npae_p_tables[0]==0);  // XXX define number of pages

  //nondet calls
  int choice = nondet_int();

  u32 restrict_addrs_4K  = 0x00000FFF;

  if (choice == 0) {
    shadow_new_context(nondet_u32() & restrict_addrs_4K);
  } else if (choice == 1) {
    shadow_invalidate_page(nondet_u32() & restrict_addrs_4K);
  } else {
    shadow_page_fault(nondet_u32() & restrict_addrs_4K, nondet_u32() & restrict_addrs_4K);
  }

  /* VERIF Condition */
  s_pdt_entry =  __shadow_npae_pd_table[0];

  if( (s_pdt_entry & _PAGE_PRESENT) ) {
    if (s_pdt_entry & _PAGE_PSE) {
      assert(npae_get_addr_from_pde(s_pdt_entry) < GUEST_PHYSICALMEMORY_LIMIT);
    }else {
      //this is a regular page directory entry, so get the page table
      u32 pt_entry = __shadow_npae_p_tables[0];
      
      if( (pt_entry & _PAGE_PRESENT) ) {
	assert(npae_get_addr_from_pte(pt_entry) < GUEST_PHYSICALMEMORY_LIMIT);
      }
    }
  }
}
/* ------------ End for verification ------------ */


//------------------------------------------------------------------------------
//return pointers to the 32-bit SHADOW pde and pte for a given guest
//virtual address
//an entry will be null (0) if not present or applicable
void shadow_get_shadowentry(u32 gva, u32 **pdt_entry, u32 **pt_entry){
  u32 index_pdt, index_pt; 
  //npdt_t s_pdt = (npdt_t)(u32)__shadow_npae_pd_table;
  npt_t s_pt;
  u32 s_pdt_entry, s_pt_entry;

  index_pdt= (gva >> 22);

  index_pt  = ((gva & (u32)0x003FFFFF) >> 12);
	
  *pdt_entry = *pt_entry = (u32 *)0;	//zero all
  assert(index_pdt == 0);
  assert(index_pt == 0);
	
  s_pdt_entry = __shadow_npae_pd_table[index_pdt];
  //*pdt_entry = (u32 *)&s_pdt[index_pdt];
  *pdt_entry = (u32 *)&__shadow_npae_pd_table[index_pdt];

  if( !(s_pdt_entry & _PAGE_PRESENT) )
    return; 
	
  if(s_pdt_entry & _PAGE_PSE)
    return; //this is a 4M page directory entry, so there is no pt
		
  //this is a regular page directory entry, so get the page table
  //s_pt = (npt_t)(u32)npae_get_addr_from_pde(s_pdt_entry);
  //*pt_entry = (u32 *)&s_pt[index_pt]; 
  *pt_entry =  (u32 *) &__shadow_npae_p_tables[index_pt];
  return;
}

//------------------------------------------------------------------------------
//return pointers to  32-bit GUEST pde and pte for a given guest VA
//an entry will be null (0) if not present or applicable
/* void shadow_get_guestentry(u32 gva, u32 gCR3, u32 **pdt_entry, u32 **pt_entry){ */
/*   u32 index_pdt, index_pt; */
/*   //npdt_t g_pdt= (npdt_t)(u32)npae_get_addr_from_32bit_cr3(gCR3); */
/*   npt_t g_pt; */
/*   u32 g_pdt_entry, g_pt_entry; */
	
/*   index_pdt= (gva >> 22); */
/*   index_pt  = ((gva & (u32)0x003FFFFF) >> 12); */
	
/*   *pdt_entry = *pt_entry = (u32 *)0;	//zero all */
	
/*   g_pdt_entry = __g_pdt[index_pdt]; */
/*   *pdt_entry = (u32 *)&__g_pdt[index_pdt]; */

/*   if( !(g_pdt_entry & _PAGE_PRESENT) ) */
/*     return; */

/*   if(g_pdt_entry & _PAGE_PSE) */
/*     return; //this is a 4M page directory entry, so no pt present */
		
/*   //this is a regular page directory entry, so get the page table */
/*   //g_pt = (npt_t)(u32)pae_get_addr_from_pde(g_pdt_entry); */
	
/*   *pt_entry = (u32 *)&__g_pt[index_pt]; */
/*   return; */
/* } */


//allocate, zero and return the address of a page table
u32 shadow_alloc_pt(u32 gva, u32 guest_virtualmemory_limit){
  u32 index_pdt;
  u32 *ptable;
  u32 ptable_vabasepointedto;

  //zero out the entire page-table
  for (int i= 0; i < 1024; i++) {
    __shadow_npae_p_tables[i]= (u32) 0;
  }
  

  //return the allocated page-table
  return (u32)__shadow_npae_p_tables;
}


//returns 1 if the page is present in guest, else 0
u32 is_present_guest(u32 *gPDE, u32 *gPTE){
  if( !(*gPDE & _PAGE_PRESENT) )
    return 0;
	
  if( *gPDE & _PAGE_PSE )
    return 1;
	
  if( !(*gPTE & _PAGE_PRESENT) )
    return 0;
  else
    return 1;
}

//never called for a non-present guest page
void shadow_updateshadowentries(u32 gva, u32 **sPDE, u32 **sPTE,
				u32 **gPDE, u32 **gPTE){
	
  u32 index_pdt, index_pt; 
  u32 flags;
  u32 paddr;

  index_pdt = (gva >> 22);
  index_pt  = ((gva & (u32)0x003FFFFF) >> 12);

  if( **gPDE & _PAGE_PSE){	//4M page
    //copy the entire entry into shadow	

    if( npae_get_addr_from_pde(**gPDE) < GUEST_PHYSICALMEMORY_LIMIT){
      **sPDE = **gPDE;
    }else{
      __CPROVER_assume(0); // HALT
    }

  }else{	//4K page table
    flags=npae_get_flags_from_pde(**gPDE); 
    paddr=npae_get_addr_from_pde(**sPDE);

    //propagate guest PDE flags to shadow PDE
    **sPDE = npae_make_pde(paddr, flags);

    //check if we have a valid shadow PT
    if(*sPTE == (u32 *)0){	//no shadow PT, so assign one
      paddr = shadow_alloc_pt(gva, GUEST_VIRTUALMEMORY_LIMIT);
      assert (paddr == (u32)__shadow_npae_p_tables);
 
      **sPDE = npae_make_pde(paddr, flags);
      //*sPTE = (u32 *)(paddr + (index_pt * sizeof(u32)));
      *sPTE = (u32 *) &(__shadow_npae_p_tables[index_pt]);
    }	
			
    //copy the entire entry into shadow	
    if( npae_get_addr_from_pte(**gPTE) < GUEST_PHYSICALMEMORY_LIMIT){
      **sPTE = **gPTE;
    }else{
      __CPROVER_assume(0);	//HALT
    }
  }

}


//------------------------------------------------------------------------------
// #PF handling
//should return VMX_EVENT_INJECT if the page-fault has to be
//injected into the guest, else VMX_EVENT_CANCEL
u32 shadow_page_fault(u32 cr2, u32 error_code){
  u32 gPDentry = nondet_u32();
  u32 gPTentry = nondet_u32();

  u32 *gPDE = &gPDentry;
  u32 *gPTE = &gPTentry;

  u32 *sPDE, *sPTE;
	
/*   //[scheck] RSVD bit set, should never happen during normal execution */
/*   if(error_code & PFERR_RSVD_MASK){ */
/*     __CPROVER_assume(0); // HALT */
/*   } */
  
  //get SHADOW and GUEST paging entries for the fault-address (CR2)
  //shadow_get_guestentry(cr2, shadow_guest_CR3, &gPDE, &gPTE);
  shadow_get_shadowentry(cr2, &sPDE, &sPTE);

  if( !(error_code & PFERR_PRESENT_MASK) ){
    if(is_present_guest(gPDE, gPTE)){
      shadow_updateshadowentries(cr2, &sPDE, &sPTE, &gPDE, &gPTE);
      return VMX_EVENT_CANCEL;
    }else{
      return VMX_EVENT_INJECT;
    }
  }else if (error_code & PFERR_WR_MASK){
    return VMX_EVENT_INJECT;
  }else{
    return VMX_EVENT_INJECT;
  }

}

//------------------------------------------------------------------------------
//invalidate a shadow paging structure
void shadow_invalidate_page(u32 address){

  //u32 *gPDE, *gPTE;
  u32 *sPDE, *sPTE;
  u32 gPDentry = nondet_u32();
  u32 gPTentry = nondet_u32();

  u32 *gPDE = &gPDentry;
  u32 *gPTE = &gPTentry;

  assert(address < GUEST_VIRTUALMEMORY_LIMIT);

  //shadow_get_guestentry(address, shadow_guest_CR3, &gPDE, &gPTE);
  shadow_get_shadowentry(address, &sPDE, &sPTE);

  if( !(*sPDE & _PAGE_PRESENT) )
    return;
	
  if( !(*gPDE & _PAGE_PRESENT) ){
    *sPDE = 0;
  }else{
    if( ((*gPDE & _PAGE_PSE) && !(*sPDE & _PAGE_PSE)) ||
	(!(*gPDE & _PAGE_PSE) && (*sPDE & _PAGE_PSE)) ){
      //mismatch in guest and shadow structures 4M vs 4K
      *sPDE = 0;
    }else{
      //both guest and shadow are same structure
      if(sPTE){
	*sPTE=0;
      }else{
	//ASSERT(*sPDE & _PAGE_PSE);
	*sPDE=0;
      }		
    }
  }
  return;
}


//------------------------------------------------------------------------------
//new context, CR3 load
//returns our shadow page table root
//we always get here only when CR4.PAE is enabled 
u32 shadow_new_context(u32 guest_CR3){
	
  //store original guest CR3 in our shadow variable
  shadow_guest_CR3 = guest_CR3;

  /* XXX removed for verif */
  //memset((void *)__shadow_npae_pd_table, 0, PAGE_SIZE_4K);

  {
    u32 num_pagedir_entries;
    //u32 *pgdir =((u32 *)((u32)__shadow_npae_pd_table)); 
    num_pagedir_entries = GUEST_VIRTUALMEMORY_LIMIT / (4096*1023);
    for (u32 i= 0; i < num_pagedir_entries; i++) {
      __shadow_npae_pd_table[i] = 0;
    }
  }

  //return our shadow pd table address which will be the new CR3
  //for the guest
  return (u32)__shadow_npae_pd_table; 

}

