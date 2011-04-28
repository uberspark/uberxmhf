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
// minimal_sp_ptr_free_norets.c modification by Jason Franklin
// 
// author: amit vasudevan (amitvasudevan@acm.org)

#include <types.h>
#include <paging.h>
#include <shadow_paging_npae.h>
//#include <vtx.h>

/*------------ Start for verification ------------*/

#define GUEST_PHYSICALMEMORY_LIMIT	 (4096*2)  //4MB guest PA
#define GUEST_VIRTUALMEMORY_LIMIT	 (4096*2)  //4GB guest VA 

u32 s_pd_t[1024];
u32 __shadow_npae_p_tables[1024];

u32 shadow_guest_CR3=0;

u32 nondet_u32();
int nondet_int();
u32* nondet_u32_ptr();

u32 shadow_new_context(u32 guest_CR3);
void shadow_invalidate_page(u32 address);
u32 shadow_page_fault(u32 cr2, u32 error_code);

void main() {
  /* Initial Condition */
  __CPROVER_assume(s_pd_t[0] == 0); // XXX define number of pages

  //u32 *ptable = (u32 *)((u32)__shadow_npae_p_tables);
  __CPROVER_assume(s_pd_t[0]==0);  // XXX define number of pages


  /* Interface */
  int choice = nondet_int();

  if (choice == 0) {
    //shadow_new_context(nondet_u32());
  } else if (choice == 1) {
    //shadow_invalidate_page(nondet_u32());
  } else {
    shadow_page_fault(nondet_u32(), nondet_u32());
  }

  /* VERIF Condition (ONLY checks 0 entries of pdt and pt) */
  if( ( s_pd_t[0] & _PAGE_PRESENT) ) {
    if ( s_pd_t[0] & _PAGE_PSE) {
      assert(npae_get_addr_from_pde( s_pd_t[0] ) + PAGE_SIZE_4M < GUEST_PHYSICALMEMORY_LIMIT);
    }else {
      //this is a regular page directory entry, so get the page table
      npt_t s_pt = (npt_t)(u32)npae_get_addr_from_pde( s_pd_t[0] );
      u32 pt_entry = s_pt[0];
      
      if( (pt_entry & _PAGE_PRESENT) ) {
	assert(npae_get_addr_from_pte(pt_entry) + PAGE_SIZE_4K < GUEST_PHYSICALMEMORY_LIMIT);
      }
    }
  }

}


u32 shadow_page_fault(u32 cr2, u32 error_code){

  u32 index_pdt, index_pt; 
  u32 flags, paddr;
  npt_t s_pt;

  u32 gPDE = nondet_u32();
  u32 gPTE = nondet_u32();


  index_pdt = (cr2 >> 22);
  index_pt  = ((cr2 & (u32)0x003FFFFF) >> 12);

  
  if( (s_pd_t[index_pdt] & _PAGE_PRESENT) && !(s_pd_t[index_pdt] & _PAGE_PSE)) {
    s_pt = (npt_t)(u32)((u32)(s_pd_t[index_pdt]) & (~((u32)PAGE_SIZE_4K - 1)));
  }


  /* page fault for page directory entry  */
  if ((gPDE & _PAGE_PRESENT) && (gPDE & _PAGE_PSE) ) {

    if( (  ((u32)(gPDE) & (~((u32)PAGE_SIZE_4K - 1))) + PAGE_SIZE_4M) < GUEST_PHYSICALMEMORY_LIMIT){
      s_pd_t[index_pdt] = gPDE;
    }

/*  else{ */
/*       __CPROVER_assume(0); // HALT */
/*     } */
  }


  /* page fault for page table entry */
  if ( (gPDE & _PAGE_PRESENT) && (!(gPDE & _PAGE_PSE) ) && (gPTE & _PAGE_PRESENT)) {

    flags = ((u32)(gPDE) & ((u32)PAGE_SIZE_4K - 1));
    paddr = ((u32)(s_pd_t[index_pdt]) & (~((u32)PAGE_SIZE_4K - 1)));
	
    s_pd_t[index_pdt] = ((u32)(paddr) & (~(((u32)PAGE_SIZE_4K - 1)))) | (u32)(flags);

    if( (((u32)(gPTE) & (~((u32)PAGE_SIZE_4K - 1))) + PAGE_SIZE_4K) < GUEST_PHYSICALMEMORY_LIMIT){
      s_pt[index_pt] = gPTE; 
    }

/*  else{ */
/*       __CPROVER_assume(0);	//HALT */
/*     } */
  }
}


//invalidate a shadow paging structure
void shadow_invalidate_page(u32 address){
  
  npt_t s_pt;

  u32 gPDE = nondet_u32();
  u32 gPTE = nondet_u32();

  u32 index_pdt = (address >> 22);
  u32 index_pt  = ((address & (u32)0x003FFFFF) >> 12);
  

  if ((s_pd_t[index_pdt] & _PAGE_PRESENT) && (gPDE & _PAGE_PRESENT) &&     
      (!(gPDE & _PAGE_PSE)) && (!(s_pd_t[index_pdt] & _PAGE_PSE)) )  {
    s_pt = (npt_t)(u32)((u32)(s_pdt_t[index_pdt]) & (~((u32)PAGE_SIZE_4K - 1)));
    s_pt[index_pt] = 0;

  }


  if( ((s_pd_t[index_pdt] & _PAGE_PRESENT) && (!(gPDE & _PAGE_PRESENT))) || 
      
      ((s_pd_t[index_pdt] & _PAGE_PRESENT) && (gPDE & _PAGE_PRESENT) &&     
       ((gPDE & _PAGE_PSE) || ( s_pd_t[index_pdt] & _PAGE_PSE)))        ) {

    s_pd_t[index_pdt] = 0;

  }
  
}


//new context, CR3 load
u32 shadow_new_context(u32 guest_CR3){

  shadow_guest_CR3 = guest_CR3;

  u32 num_pagedir_entries = GUEST_VIRTUALMEMORY_LIMIT / (4096*1023);
  
  for (u32 i= 0; i < num_pagedir_entries; i++) {
    s_pd_t[i] = 0;
  }

  //return (u32)s_pd_t; 
}

