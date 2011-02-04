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
#include <target.h>
#include <print.h>
#include <processor.h>
#include <msr.h>
//#include <vtx.h>
#include <paging.h>
#include <io.h>
#include <str.h>
//#include <machine.h> 
#include <error.h>
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
//#define __shadow_npae_pd_table  0xdeadbeef

u32 __shadow_npae_p_tables[1024];
//#define __shadow_npae_p_tables 0xddddffff

#define gpa_to_hpa(x) x

u16 guest_GDTR_limit;
u16 guest_IDTR_limit;
u16 guest_TR_limit;
u32 guest_GDTR_base;
u32 guest_IDTR_base;
u32 guest_TR_base;


u32 shadow_guest_CR3=0x00001111;

/*
	A note of all events that cause TLB flushes on the IA-32
	
	1. Writing to a MTRR with WRMSR -> ALL TLB 
	2. Writing to CR0 to modify PG or PE flags -> ALL TLB
	3. Writing to CR4 to modify PSE, PGE or PAE flags -> ALL TLB
	4. INVLPG ->  TLB of address including global
	5. MOV to CR3 -> ALL TLB except global
	6. Task Switch changing value of CR3 -> ALL TLB except global
	7. VMX transitions -> ALL TLB 
*/




/*------------ Start for verification ------------*/


u32 nondet_u32();
int nondet_int();

u32 shadow_new_context(u32 guest_CR3);
void shadow_invalidate_page(u32 address);
u32 shadow_page_fault(u32 cr2, u32 error_code);

void main() {

  /* Initial Condition */
  npdt_t s_pdt = (npdt_t)(u32)__shadow_npae_pd_table;
  //assert (s_pdt == (npdt_t)(u32)__shadow_npae_pd_table);
  u32 s_pdt_entry =  s_pdt[0];
  __CPROVER_assume(s_pdt[0] == 0); // XXX define number of pages
  //__CPROVER_assume(pgdir > GUEST_PHYSICALMEMORY_LIMIT);

  u32 *ptable = (u32 *)((u32)__shadow_npae_p_tables);
  __CPROVER_assume(ptable[0]==0);  // XXX define number of pages

  //nondet calls
  int choice = nondet_int();

  // u32 restrict_addrs_4K  = 0x00000FFF;
  // XXX can change this without changing verification
  // since verification condition only mentions 0 entries of pdt and pt
  u32 restrict_addrs_4K  = 0xFFFFFFFF; 

  if (choice == 0) {
    //shadow_new_context(nondet_u32() & restrict_addrs_4K);
  } else if (choice == 1) {
    //shadow_invalidate_page(nondet_u32() & restrict_addrs_4K);
  } else {
    shadow_page_fault(nondet_u32() & restrict_addrs_4K, nondet_u32());
  }

  /* VERIF Condition (ONLY checks 0 entries of pdt and pt) */
  s_pdt = (npdt_t)(u32)__shadow_npae_pd_table;
  s_pdt_entry =  s_pdt[0];

  if( (s_pdt_entry & _PAGE_PRESENT) ) {
    if (s_pdt_entry & _PAGE_PSE) {
      assert(npae_get_addr_from_pde(s_pdt_entry) < GUEST_PHYSICALMEMORY_LIMIT);
    }else {
      //this is a regular page directory entry, so get the page table
      npt_t s_pt = (npt_t)(u32)npae_get_addr_from_pde(s_pdt_entry);
      u32 pt_entry = s_pt[0]; 
      
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
  // XXX this line causes warnings, I don't understand why
  //npdt_t s_pdt = (npdt_t)(u32)__shadow_npae_pd_table; 

  npt_t s_pt;
  u32 s_pdt_entry, s_pt_entry;
	
  index_pdt= (gva >> 22);
  index_pt  = ((gva & (u32)0x003FFFFF) >> 12);
	
  *pdt_entry = *pt_entry = (u32 *)0;	//zero all
	
  s_pdt_entry = __shadow_npae_pd_table[index_pdt];
  *pdt_entry = (u32 *)&__shadow_npae_pd_table[index_pdt];

  if( !(s_pdt_entry & _PAGE_PRESENT) )
    return; 
	
  if(s_pdt_entry & _PAGE_PSE)
    return; //this is a 4M page directory entry, so there is no pt
		
  //this is a regular page directory entry, so get the page table
  s_pt = (npt_t)(u32)npae_get_addr_from_pde(s_pdt_entry);
  *pt_entry = (u32 *)&s_pt[index_pt]; 
  return;
}

//------------------------------------------------------------------------------
//return pointers to the 32-bit GUEST pde and pte for a given guest
//virtual address
//an entry will be null (0) if not present or applicable
//set the ACCESSED bit
//as we traverse the guest paging structures 
void shadow_get_guestentry(u32 gva, u32 gCR3, u32 **pdt_entry, u32 **pt_entry){
  u32 index_pdt, index_pt; 
  //npdt_t g_pdt=(npdt_t)gpa_to_hpa((u32)npae_get_addr_from_32bit_cr3(gCR3));
  npdt_t g_pdt=(npdt_t)gpa_to_hpa((u32)npae_get_addr_from_32bit_cr3(gCR3));
  npt_t g_pt;
  u32 g_pdt_entry, g_pt_entry;
	
  index_pdt= (gva >> 22);
  index_pt  = ((gva & (u32)0x003FFFFF) >> 12);
	
  *pdt_entry = *pt_entry = (u32 *)0;	//zero all
	
  g_pdt_entry = g_pdt[index_pdt];
  *pdt_entry = (u32 *)&g_pdt[index_pdt];


  if( !(g_pdt_entry & _PAGE_PRESENT) )
    return; 

  //set ACCESSED bit on this pdt entry
  //g_pdt[index_pdt] |= _PAGE_ACCESSED;

  if(g_pdt_entry & _PAGE_PSE)
    return; //this is a 4M page directory entry, so no pt present
		
  //this is a regular page directory entry, so get the page table
  g_pt = (npt_t)gpa_to_hpa((u32)pae_get_addr_from_pde(g_pdt_entry));

	
  //set ACCESSED bit on this pt entry
  //if(g_pt[index_pt] & _PAGE_PRESENT)
  //	g_pt[index_pt] |= _PAGE_ACCESSED;
	
	
  *pt_entry = (u32 *)&g_pt[index_pt]; 
  return;
}


//allocate, zero and return the address of a page table
u32 shadow_alloc_pt(u32 gva, u32 guest_virtualmemory_limit){
  u32 index_pdt;
  u32 *ptable;
  u32 ptable_vabasepointedto;

  index_pdt= (gva >> 22);	//grab page-directory index from guest virtual address
  assert(index_pdt == 0);

  //get a pointer to the page-table that we are allocating
  ptable = (u32 *)((index_pdt * PAGE_SIZE_4K) + (u32)__shadow_npae_p_tables);
  //assert (ptable == (u32 *)(u32)__shadow_npae_p_tables);
	
  //this is the 4MB aligned virtual address base that the page-table will
  //address (patable_vabasepointedto to patable_vabasepointedto+4MB)
  //ptable_vabasepointedto = index_pdt * (PAGE_SIZE_4K * 1024); 
	
  //memset( (void *)((index_pdt * PAGE_SIZE_4K) + (u32)__shadow_npae_p_tables), 0, PAGE_SIZE_4K);
  
  //sanity check
  //assert(guest_virtualmemory_limit > ptable_vabasepointedto);
	
  //if(guest_virtualmemory_limit - ptable_vabasepointedto > (PAGE_SIZE_4K * 1024) ) {
    //we need to zero out the entire page-table
  for (int i= 0; i < 1024; i++) {
      ptable[i]= (u32) 0;
  }
  
  
/*   }else{ */
/*     //we only need to zero out part of the page-table */
/*     u32 indexuntil =  (guest_virtualmemory_limit - ptable_vabasepointedto) / PAGE_SIZE_4K; */
/*     for (int i= 0; i < indexuntil; i++) { */
/*       ptable[i]= (u32) 0; */
/*     }			 */
/*   } */

  //we need to zero out the entire page-table 
  // XXX COMMENTED THIS OUT AND VERIFICATION HOLDS 
  //for (int i= 0; i < 1024; i++) {
    //ptable[i]= (u32) 0;
  //}

  //return the allocated page-table
  return ( (u32)ptable );
}


//returns 1 if the page is present in guest, else 0
u32 is_present_guest(u32 *gPDE, u32 *gPTE){
  //ASSERT ( gPDE != (u32 *)0 );
	
  if( !(*gPDE & _PAGE_PRESENT) )
    return 0;
	
  if( *gPDE & _PAGE_PSE )
    return 1;
	
  //ASSERT ( gPTE != (u32 *)0 );
	
  if( !(*gPTE & _PAGE_PRESENT) )
    return 0;
  else
    return 1;
}


void set_guestentry_accessed(u32 *gPDE, u32 *gPTE){
  u32 *guest_entry;
	
  //ASSERT( gPDE != (u32 *)0 );
	
  if( ! (*gPDE & _PAGE_PRESENT) )
    return;

  *gPDE |= _PAGE_ACCESSED;
	
  if(*gPDE & _PAGE_PSE)
    return;
		
  //ASSERT( gPTE != (u32 *)0 );
	
  if ( *gPTE & _PAGE_PRESENT)
    *gPTE |= _PAGE_ACCESSED;
	
}


//never called for a non-present guest page
void shadow_updateshadowentries(u32 gva, u32 **sPDE, u32 **sPTE,
				u32 **gPDE, u32 **gPTE){
	
  u32 index_pdt, index_pt; 
  u32 flags;
  u32 paddr;

  index_pdt= (gva >> 22);
  index_pt  = ((gva & (u32)0x003FFFFF) >> 12);
	
  //printf("\n	index_pdt=%u, index_pt=%u", index_pdt, index_pt);
	
  //ASSERT( *gPDE != (u32 *)0 ); //gPDE MUST be valid, either a 4M page or point to a PT
  //ASSERT( **gPDE & _PAGE_PRESENT );

  if( **gPDE & _PAGE_PSE){	//4M page
    //copy the entire entry into shadow	
    if( npae_get_addr_from_pde(**gPDE) < GUEST_PHYSICALMEMORY_LIMIT){
      **sPDE = **gPDE;
    }else{
      printf("\nillegal mapping!");
      __CPROVER_assume(0); // HALT
    }
  }else{	//4K page table
    flags=npae_get_flags_from_pde(**gPDE); 

    paddr=npae_get_addr_from_pde(**sPDE);
    //propagate guest PDE flags to shadow PDE
    **sPDE = npae_make_pde(paddr, flags);


			
    //ASSERT( *gPTE != (u32 *)0 ); //gPTE MUST be valid and present
    //ASSERT( **gPTE & _PAGE_PRESENT );

    //check if we have a valid shadow PT
    if(*sPTE == (u32 *)0){	//no shadow PT, so assign one
      //ASSERT(paddr == 0);
      paddr = shadow_alloc_pt(gva, GUEST_VIRTUALMEMORY_LIMIT);
      //assert (paddr == (u32)__shadow_npae_p_tables);
      **sPDE = npae_make_pde(paddr, flags);
      *sPTE = (u32 *)(paddr + (index_pt * sizeof(u32)));
    }	
			
    //copy the entire entry into shadow	
    if( npae_get_addr_from_pte(**gPTE) < GUEST_PHYSICALMEMORY_LIMIT){
      **sPTE = **gPTE;
    }else{
      //printf("\nillegal mapping!");
      __CPROVER_assume(0);	//HALT
      
    }
  }

  //SECURITY PROPERTY
  if (**gPDE & _PAGE_PSE) {
    u32 temp_addr =  npae_get_addr_from_pde(**sPDE);
    assert(  npae_get_addr_from_pde(**sPDE) <= GUEST_PHYSICALMEMORY_LIMIT);
  } else {
    assert(  npae_get_addr_from_pte(**sPTE) <= GUEST_PHYSICALMEMORY_LIMIT);
  }

}


//[DEBUG]: dump the page table entries for both shadow and guest
void sdbg_dumpentries(u32 *gPDE, u32 *gPTE,
		      u32 *sPDE, u32 *sPTE){
  //ASSERT( (gPDE != (u32 *)0 && sPDE != (u32 *)0) );
  printf("\n	__s_pd=0x%08x, __s_pt=0x%08x", 
	 (u32)__shadow_npae_pd_table, (u32)__shadow_npae_p_tables);
  printf("\n	PDEs: g=0x%08x, s=0x%08x", *gPDE, *sPDE);
	
  printf("\n	PTEs	: ");
  if(gPTE)
    printf("g=0x%08x, ", *gPTE);
  else
    printf("g=< NP     >, ");

  if(sPTE)
    printf("s=0x%08x", *sPTE);
  else
    printf("s=< NP     >");
	
  return;		
}

//[DEBUG]: dumps PF details
void sdbg_dumppfdetails(u32 cr2, u32 error_code){
  u32 index_pdt, index_pt;
	
  index_pdt= (cr2 >> 22);
  index_pt  = ((cr2 & (u32)0x003FFFFF) >> 12);

/*   printf("\n0x%04x:0x%08x: #PF (cr2=0x%08x, error_code=0x%08x), pair=%u,%u -> ",  */
/* 	 (unsigned short)guest_CS_selector, (unsigned int)guest_RIP,  */
/* 	 (unsigned int)cr2, (unsigned int)error_code, index_pdt, index_pt); */

  if(error_code & PFERR_US_MASK)
    printf("U,");
  else
    printf("S,");

  if(! (error_code & PFERR_PRESENT_MASK) )
    printf("NP,");
  else
    printf("P,");
		
  if(error_code & PFERR_WR_MASK)
    printf("W,");
  else
    printf("R,");
		
  if(error_code & PFERR_ID_MASK)
    printf("I,");
  else
    printf("D,");

  return;
}


//------------------------------------------------------------------------------
//helper function for propagating dirty bits to guest

//clear dirty-waiting bit in shadow page table entry referenced by
//sPDPTE/sPDE/sPTE and restore R/W bit from AVL bits
void clear_shadowentry_dirtywaiting(u32 *sPDE, u32 *sPTE){
  u32 original_rw_bit;
  u32 *shadow_entry;
	
  //grab original RW bit value 
  //and also determine which shadow entry we will use (PDE or PTE)
  //ASSERT( sPDE != (u32 *)0 );
  //ASSERT( *sPDE & _PAGE_PRESENT );
	
  if(*sPDE & _PAGE_PSE){	//4M page
    original_rw_bit = (*sPDE & _PAGE_SHADOW_ORIGINALRWBIT);
    shadow_entry = sPDE;
  }else{
    //ASSERT( sPTE != (u32 *)0 );
    //ASSERT( *sPTE & _PAGE_PRESENT );
    original_rw_bit = (*sPTE & _PAGE_SHADOW_ORIGINALRWBIT);
    shadow_entry = sPTE;
  }

  //clear dirty-waiting and restore original R/W bit
  *shadow_entry &= ~(_PAGE_SHADOW_DIRTYWAITING);
  if(original_rw_bit)
    *shadow_entry |= _PAGE_RW;	//R/W
  else
    *shadow_entry &= ~(_PAGE_RW);		//R

}


//return 1 if shadow page table entry referenced by
//sPDPTE/sPDE/sPTE is writable (i.e R/W bit is set)
u32 is_shadowentry_writable(u32 *sPDE, u32 *sPTE){
  u32 original_rw_bit;
  u32 *shadow_entry;
	
  //grab original RW bit value 
  //and also determine which shadow entry we will use (PDE or PTE)
  //ASSERT( sPDE != (u32 *)0 );
  //ASSERT( *sPDE & _PAGE_PRESENT );
	
  if(*sPDE & _PAGE_PSE){	//4M page
    shadow_entry = sPDE;
  }else{
    //ASSERT( sPTE != (u32 *)0 );
    //ASSERT( *sPTE & _PAGE_PRESENT );
    shadow_entry = sPTE;
  }

  //check R/W bit
  if(*shadow_entry & _PAGE_RW)
    return 1;
  else
    return 0;
}


//set dirty-waiting bit in shadow page table entry referenced by
//sPDPTE/sPDE/sPTE and store original R/W bit in AVL bits
void set_shadowentry_dirtywaiting(u32 *sPDE, u32 *sPTE,
				  u32 *gPDE, u32 *gPTE){
  u32 original_rw_bit;
  u32 *shadow_entry;
	
  //grab original RW bit value from guest paging structures
  //and also determine which shadow entry we will use (PDE or PTE)
  //ASSERT( gPDE != (u32 *)0 );
  //ASSERT( *gPDE & _PAGE_PRESENT );
	
  if(*gPDE & _PAGE_PSE){	//4M page
    original_rw_bit = (*gPDE & _PAGE_RW);
    shadow_entry = sPDE;
  }else{
    //ASSERT( gPTE != (u32 *)0 );
    //ASSERT( *gPTE & _PAGE_PRESENT );
    original_rw_bit = (*gPTE & _PAGE_RW);
    shadow_entry = sPTE;
  }
	
  //set dirty-waiting and store original R/W bit in shadow entry
  //clear R/W bit in shadow
  *shadow_entry |= _PAGE_SHADOW_DIRTYWAITING;
  *shadow_entry &= ~(_PAGE_RW);
  if(original_rw_bit)
    *shadow_entry |= _PAGE_SHADOW_ORIGINALRWBIT;	//R/W
  else
    *shadow_entry &= ~(_PAGE_SHADOW_ORIGINALRWBIT);		//R	

}

//returns 1, if a shadow page table entry referenced by sPDPTE/sPDE/sPTE
//is waiting to be dirty, else 0
u32 is_shadowentry_dirtywaiting(u32 *sPDE, u32 *sPTE){
  u32 *shadow_entry;
	
  //determine which shadow entry we will use (PDE or PTE)
  //ASSERT( sPDE != (u32 *)0 );
  //ASSERT( *sPDE & _PAGE_PRESENT );
	
  if(*sPDE & _PAGE_PSE){	//4M page
    shadow_entry = sPDE;
  }else{
    //ASSERT( sPTE != (u32 *)0 );
    //ASSERT( *sPTE & _PAGE_PRESENT );
    shadow_entry = sPTE;
  }

  //check for dirty-waiting
  if(*shadow_entry & _PAGE_SHADOW_DIRTYWAITING)
    return 1;
  else
    return 0;	
}

//set dirty bit in guest page table entry referenced by gPDPTE/gPDE/gPTE
void set_guestentry_dirty(u32 *gPDE, u32 *gPTE){
  u32 *guest_entry;
	
  //determine which GUEST entry we will use (PDE or PTE)
  //ASSERT( gPDE != (u32 *)0 );
  //ASSERT( *gPDE & _PAGE_PRESENT );
	
  if(*gPDE & _PAGE_PSE){	//4M page
    guest_entry = gPDE;
  }else{
    //ASSERT( gPTE != (u32 *)0 );
    //ASSERT( *gPTE & _PAGE_PRESENT );
    guest_entry = gPTE;
  }

  //mark dirty
  *guest_entry |= _PAGE_DIRTY;
}



//------------------------------------------------------------------------------
// #PF handling
//should return VMX_EVENT_INJECT if the page-fault has to be
//injected into the guest, else VMX_EVENT_CANCEL
u32 shadow_page_fault(u32 cr2, u32 error_code){

#if 1	//hook vs implementation control, 0=hook only with native chaining
  u32 *gPDE, *gPTE;
  u32 *sPDE, *sPTE;
	


  //[scheck] RSVD bit set, should never happen during normal execution
  if(error_code & PFERR_RSVD_MASK){
    printf("\nRSVD bit set on page-fault, Halt!");
    __CPROVER_assume(0); // HALT
  }


  //get SHADOW and GUEST paging entries for the fault-address (CR2)
  shadow_get_guestentry(cr2, shadow_guest_CR3, &gPDE, &gPTE);

  shadow_get_shadowentry(cr2, &sPDE, &sPTE);
  //sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE);


  //if(!shadow_checkcontext( (u32)npae_get_addr_from_32bit_cr3((u32)shadow_guest_CR3) ) ){
  //		printf("\nPF: Halting, reserved bits set in GUEST paging structures!");
  //		__CPROVER_assume(0);
  //}	

	
  if( !(error_code & PFERR_PRESENT_MASK) ){
    assert(0);
    if(is_present_guest(gPDE, gPTE)){
      //printf("\n	SHADOW-NOT-PRESENT (GUEST-PRESENT): syncing...");
      assert(0);

      shadow_updateshadowentries(cr2, &sPDE, &sPTE,&gPDE, &gPTE);
      /* Commented out for verif XXX */


      /* /\* // SECURITY PROPERTY *\/ */
      /* if (*gPDE & _PAGE_PSE) { */
      /*   assert(  npae_get_addr_from_pde(*sPDE) <= GUEST_PHYSICALMEMORY_LIMIT); */
      /* } else { */
      /*   assert(  npae_get_addr_from_pte(*sPTE) <= GUEST_PHYSICALMEMORY_LIMIT); */
      /* } */

				
      //set_guestentry_accessed(gPDE, gPTE);
      //set_shadowentry_dirtywaiting(sPDE, sPTE, gPDE, gPTE);
				
      /* if(!shadow_checkcontext((u32)__shadow_npae_pd_table)){ */
      /* 	//printf("\nPF: Halting, reserved bits set in SHADOW paging structures!"); */
      /* 	__CPROVER_assume(0); */
      /* }	 */

      //sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE);
      return VMX_EVENT_CANCEL;
    }else{
      //set_guestentry_accessed(gPDE, gPTE);
      //printf("\n	SHADOW-NOT-PRESENT (GUEST-NOT-PRESENT): injecting #PF into guest (NP fault).");
      return VMX_EVENT_INJECT;
    }
  }else if (error_code & PFERR_WR_MASK){
    //ASSERT(is_present_guest(gPDE, gPTE));

    //if(is_shadowentry_dirtywaiting(sPDE, sPTE)){
    //	printf("\n	SHADOW-PRESENT (GUEST-PRESENT): processing dirty-waiting...");
    //	clear_shadowentry_dirtywaiting(sPDE, sPTE);
    //	if(is_shadowentry_writable(sPDE, sPTE))
    //		set_guestentry_dirty(gPDE, gPTE);			
    //	set_guestentry_accessed(gPDE, gPTE);
    //	return VMX_EVENT_CANCEL;
    //}else{
				
    //printf("\n	SHADOW-PRESENT (GUEST-PRESENT): injecting #PF into guest (R/W fault).");
    //sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE);
    //set_guestentry_accessed(gPDE, gPTE);
    return VMX_EVENT_INJECT;
    //}
  }else{
    //printf("\n	SHADOW-PRESENT (GUEST-PRESENT): injecting #PF into guest (other fault).");
    //set_guestentry_accessed(gPDE, gPTE);
    return VMX_EVENT_INJECT;
  }

	
#else


  return VMX_EVENT_INJECT;
#endif
}

//------------------------------------------------------------------------------
//invalidate a shadow paging structure
void shadow_invalidate_page(u32 address){

#if 1	//hook vs implementation control, 0=hook only with native chaining
  u32 *gPDE, *gPTE;
  u32 *sPDE, *sPTE;

  //ASSERT(address < GUEST_VIRTUALMEMORY_LIMIT);
	
  //printf("\n0x%04x:0x%08x: INVLPG (address=0x%08x)", 
  //	(unsigned short)guest_CS_selector, (unsigned int)guest_RIP, 
  //	(unsigned int)address);

  shadow_get_guestentry(address, shadow_guest_CR3, &gPDE, &gPTE);
  shadow_get_shadowentry(address, &sPDE, &sPTE);
  //sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE);

  //ASSERT( gPDE != (u32 *)0 );
  //ASSERT( sPDE != (u32 *)0 );

#if 1	//control for conservative/actual policy of INVLPG 1=actual policy	
	//bail out if we dont have a SHADOW page-directory, we wil sync on
	//the page-fault
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

  //sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE);

  return;
#else

  *sPDE = 0;	
  return;
#endif	

#else //hook 
  return;
#endif
}



// assuming 36-bit physical addresses and PAT supported
//PDE reserved mask
//	4M pages
//		0000 0000 0011 1110 0000 0000 0000 0000
// = 0x003E0000UL
//  4K page table
//   0000 0000 0000 0000 0000 0000 0000 0000
// = 0x00000000UL
//PTE reserved mask
//   0000 0000 0000 0000 0000 0000 0000 0000
// = 0x00000000UL
//------------------------------------------------------------------------------
//dump paging structures pointed to by root
//return 1 on success, 0 on failure (as a side prints out all entries
//with RSVD bits set)
u32 shadow_checkcontext(u32 root){
  npdt_t pdt;
  npt_t pt;
  u32 i, j;
  u32 flags;
  u32 paddr;
  u32 status=1;

  pdt = (npdt_t)root;
	
  for(i=0; i < NPAE_PTRS_PER_PDT; i++){
    if(pdt[i] & _PAGE_PRESENT){
      //check RSVD bits
      if(pdt[i] & _PAGE_PSE){
	if (pdt[i] & 0x003E0000UL){
	  printf("\nRSVD bit set in PDE %u (0x%08x)", i, pdt[i]);
	  status=0;
	}
      }	
    }
  }	
	
  return status;	
}




//------------------------------------------------------------------------------
//new context, CR3 load
//returns our shadow page table root
//we always get here only when CR4.PAE is enabled 
u32 shadow_new_context(u32 guest_CR3){
  //(void)guest_CR3;
  //printf("\n0x%04x:0x%08x: MOV CR3, x (CR3 value=0x%08x)", 
  //	(unsigned short)guest_CS_selector, (unsigned int)guest_RIP, 
  //	(unsigned int)guest_CR3);
	
  //store original guest CR3 in our shadow variable
  shadow_guest_CR3 = guest_CR3;

#if 1	//hook vs implementation control, 0=hook only with native chaining

  /* XXX removed for verif */
  //memset((void *)__shadow_npae_pd_table, 0, PAGE_SIZE_4K);

  {
    u32 num_pagedir_entries;
    u32 *pgdir =((u32 *)((u32)__shadow_npae_pd_table)); 
    num_pagedir_entries = GUEST_VIRTUALMEMORY_LIMIT / (4096*1023);

    //for (u32 i= 0; i < num_pagedir_entries; i++) {
    //pgdir[i] = 0;
    //assert(0); // XXX this doesn't even execute
      //}
  }
  

  //we need to populate GDT, IDT and TSS memory pages as we dont want
  //them causing double/triple faults that we will need to process
  //NOTE: dirty bits for these structures are never used in any OS
  //as these structures are never paged-out!
  //UPDATE: 1/13/2010
  //Windows HAL uses PAE paging structures during initialization and
  //they do not contain the GDT/IDT/TR mapped!!
  /* { */
  /*   u32 start_va, end_va;	//pages from start_va to end_va inclusive */
  /*   u32 va; */
  /*   u32 *gPDE, *gPTE; */
  /*   u32 *sPDE, *sPTE; */

  /*   //printf("\n%s: pre-loading guest GDT, IDT and TR pages..."); */

  /*   start_va = PAGE_ALIGN_4K (guest_GDTR_base); */
  /*   end_va = PAGE_ALIGN_4K( (guest_GDTR_base + guest_GDTR_limit) ); */
  /*   //printf("\n	GDT pages=0x%08x-0x%08x inclusive",	start_va, end_va);  */

  /*   for(va=start_va; va <= end_va; va+= PAGE_SIZE_4K){ */
  /*     shadow_get_guestentry(va, shadow_guest_CR3, &gPDE, &gPTE); */
  /*     shadow_get_shadowentry(va, &sPDE, &sPTE); */
  /*     if(is_present_guest(gPDE, gPTE)){ */
  /* 	//printf("\n	Structures BEFORE:"); */
  /* 	//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE); */
  /* 	shadow_updateshadowentries(va, &sPDE, &sPTE, */
  /* 				   &gPDE, &gPTE); */
  /* 	//printf("\n	Structures AFTER:"); */
  /* 	//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE); */
  /*     }else{ */
  /* 	//printf("\n	GUEST NOT-PRESENT!"); */
  /*     } */
  /*   } */

  /*   start_va = PAGE_ALIGN_4K (guest_IDTR_base); */
  /*   end_va = PAGE_ALIGN_4K( (guest_IDTR_base + guest_IDTR_limit) ); */
  /*   //printf("\n	IDT pages=0x%08x-0x%08x inclusive",	start_va, end_va);  */

  /*   for(va=start_va; va <= end_va; va+= PAGE_SIZE_4K){ */
  /*     shadow_get_guestentry(va, shadow_guest_CR3, &gPDE, &gPTE); */
  /*     shadow_get_shadowentry(va, &sPDE, &sPTE); */
  /*     if(is_present_guest(gPDE, gPTE)){ */
  /* 	//printf("\n	Structures BEFORE:"); */
  /* 	//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE); */
  /* 	shadow_updateshadowentries(va, &sPDE, &sPTE, */
  /* 				   &gPDE, &gPTE); */
  /* 	//printf("\n	Structures AFTER:"); */
  /* 	//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE); */
  /*     }else{ */
  /* 	//printf("\n	GUEST NOT-PRESENT!"); */
  /*     } */
  /*   } */

  /*   start_va = PAGE_ALIGN_4K(guest_TR_base); */
  /*   end_va = PAGE_ALIGN_4K( (guest_TR_base + guest_TR_limit) ); */
  /*   //printf("\n	TR pages=0x%08x-0x%08x inclusive",	start_va, end_va);  */

  /*   for(va=start_va; va <= end_va; va+= PAGE_SIZE_4K){ */
  /*     shadow_get_guestentry(va, shadow_guest_CR3, &gPDE, &gPTE); */
  /*     shadow_get_shadowentry(va, &sPDE, &sPTE); */
  /*     if(is_present_guest(gPDE, gPTE)){ */
  /* 	//printf("\n	Structures BEFORE:"); */
  /* 	//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE); */
  /* 	shadow_updateshadowentries(va, &sPDE, &sPTE, */
  /* 				   &gPDE, &gPTE); */
  /* 	//printf("\n	Structures AFTER:"); */
  /* 	//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE); */
  /*     }else{ */
  /* 	//printf("\n	GUEST NOT-PRESENT!"); */
  /*     } */
  /*   } */
	
  /*} */

  //return our shadow pd table address which will be the new CR3
  //for the guest
  return (u32)__shadow_npae_pd_table; 
#else

  //if(!shadow_checkcontext( (u32)npae_get_addr_from_32bit_cr3((u32)guest_CR3) ) ){
  //	printf("\nHalting, reserved bits set in GUEST paging structures!");
  //	__CPROVER_assume(0);();
  //}	

  return guest_CR3;
	
#endif
}

