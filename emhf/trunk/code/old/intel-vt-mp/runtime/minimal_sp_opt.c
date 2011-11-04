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

//added 2/4/2011 1:37:32 PM by amit vasudevan
//this file is based on minimal_sp but adds pseudo-code for two of Xen's
//optimizations hereon called opt1 and opt2
//opt1 = context caching optimzation where each context within a VM 
//has its own shadow page tables
//opt2 = guest page-table write-protect to handle shadow page table
//synchronization

#include <types.h>
//#include <print.h>
#include <paging.h>
//#include <str.h>
#include <shadow_paging_npae.h>
#include <vtx.h>
//#include "../common/string.c"


/*------------ Start for verification ------------*/

#define GUEST_PHYSICALMEMORY_LIMIT	 (4096*2)  //4MB guest PA
#define GUEST_VIRTUALMEMORY_LIMIT	 (4096*2)	//4GB guest VA 

u32 __shadow_npae_pd_table[1024];
u32 __shadow_npae_p_tables[1024];


#define gpa_to_hpa(x) x

u32 shadow_guest_CR3=0;

u32 nondet_u32();
int nondet_int();
u32* nondet_u32_ptr();

u32 shadow_new_context(u32 guest_CR3);
void shadow_invalidate_page(u32 address);
u32 shadow_page_fault(u32 cr2, u32 error_code);

void main() {

  /* Initial Condition */
  npdt_t s_pdt = (npdt_t)(u32)__shadow_npae_pd_table;

  u32 s_pdt_entry =  s_pdt[0];
  __CPROVER_assume(s_pdt[0] == 0); // XXX define number of pages


  u32 *ptable = (u32 *)((u32)__shadow_npae_p_tables);
  __CPROVER_assume(ptable[0]==0);  // XXX define number of pages


  int choice = nondet_int();

  if (choice == 0) {
    //shadow_new_context(nondet_u32());
  } else if (choice == 1) {
    //shadow_invalidate_page(nondet_u32());
  } else {
    shadow_page_fault(nondet_u32(), nondet_u32());
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
      u32 temp = s_pdt_entry;
      u32 pt_entry = s_pt[0]; 
      
      if( (pt_entry & _PAGE_PRESENT) ) {
	assert(npae_get_addr_from_pte(pt_entry) < GUEST_PHYSICALMEMORY_LIMIT);
      }
    }
  }
}

/* ------------ End for verification ------------ */


//------------------------------------------------------------------------------
//return pointers to the 32-bit SHADOW pde and pte for a given guest va
void shadow_get_shadowentry(u32 gva, u32 **pdt_entry, u32 **pt_entry){
  u32 index_pdt, index_pt; 
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


u32 shadow_alloc_pt(u32 gva, u32 guest_virtualmemory_limit){
  u32 index_pdt;
  u32 *ptable;
  u32 ptable_vabasepointedto;

  index_pdt= (gva >> 22);	

  //get a pointer to the page-table that we are allocating
  ptable = (u32 *)((index_pdt * PAGE_SIZE_4K) + (u32)__shadow_npae_p_tables);
  //this is the 4MB aligned virtual address base that the page-table will
  //address (patable_vabasepointedto to patable_vabasepointedto+4MB)
  ptable_vabasepointedto = index_pdt * (PAGE_SIZE_4K * 1024); 
	
  //return the allocated page-table
  return ( (u32)ptable );
}


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


void shadow_updateshadowentries(u32 gva, u32 **sPDE, u32 **sPTE,
				u32 **gPDE, u32 **gPTE){
  u32 index_pdt, index_pt; 
  u32 flags;
  u32 paddr;



  index_pdt= (gva >> 22);
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

    **sPDE = npae_make_pde(paddr, flags);
			
    if(*sPTE == (u32 *)0){	//no shadow PT, so assign one
      paddr = shadow_alloc_pt(gva, GUEST_VIRTUALMEMORY_LIMIT);
      **sPDE = npae_make_pde(paddr, flags);
      *sPTE = (u32 *)(paddr + (index_pt * sizeof(u32)));
      __CPROVER_assume(*sPTE != 0);
    }	

    if( npae_get_addr_from_pte(**gPTE) < GUEST_PHYSICALMEMORY_LIMIT){
      **sPTE = **gPTE;
    }else{
      __CPROVER_assume(0);	//HALT
      
    }
  }
}

//instruction emulator pseudo-code
//returns 32-bit PDE and PTE entries that the guest is writing to its
//page table
void emulatewrite(u32 cr2, u32 **sPDE, u32 **sPTE, u32 *emulator_PDE, u32 *emulator_PTE){
	u32 insn_opcode;	//instruction opcode
	u32 insn_effective_operand;	//instruction effective operand value
	
	//decode the instruction at the current instruction pointer and store
	//instruction opcode and effective operand
	decode_instruction(get_csrip(), &insn_opcode, &insn_effective_operand); 

	switch(insn_opcode){
		//there can be three broad categories of writes, move, arithmetic operations
		//(e.g., ADD, SUB etc.) or an XCHG
		case MOVE_TO_MEM_OPCODE:
		case ARITH_MEM_OPCODE:
		case XCHG_MEM_OPCODE:
    	//get hold of the PDE and/or the PTE value written by the guest
			if(is_write_to_PDE(cr2, insn_effective_operand)){
    		*emulator_PDE = insn_effective_operand;	//guest wrote to a PDE 
    		*emulator_PTE = 0;    		
    	}else{
			 	*emulator_PTE = insn_effective_operand;	//guest wrote to a PTE
			 	*emulator_PDE = get_guest_PDE_entry_for_PTE(*emulator_PTE);	//fetch the corresponding PDE	 	
			} 
			
			//reflect the write to the guest page tables
 			propagate_write_to_guest(cr2, insn_effective_operand);

		default:
			printf("\nunhandled instruction category during emulation!");
			HALT();			
	}

}


u32 shadow_page_fault(u32 cr2, u32 error_code){

  
  u32 *sPDE, *sPTE;


  // XXX Non-deterministic adversary reduction
  //u32 *gPDE, *gPTE;
  u32 gPDentry = nondet_u32();
  u32 gPTentry = nondet_u32();
  u32 *gPDE = &gPDentry;
  u32 *gPTE = &gPTentry;


  //shadow_get_guestentry(cr2, shadow_guest_CR3, &gPDE, &gPTE);
  shadow_get_shadowentry(cr2, &sPDE, &sPTE);

  if( !(error_code & PFERR_PRESENT_MASK) ){
    if(is_present_guest(gPDE, gPTE)){

      shadow_updateshadowentries(cr2, &sPDE, &sPTE,&gPDE, &gPTE);

      return VMX_EVENT_CANCEL;
    }else{
      return VMX_EVENT_INJECT;
    }
  }else if (error_code & PFERR_WR_MASK){
    //[opt2]: we have a write fault, check to see if the guest is 
    //trying to modify its page-tables, if so we need to emulate the
    //instruction and propagate the value to the shadow
    if(is_write_to_guest_pagetable(gPDE, gPTE)){
			u32 emulator_PDE_value;
			u32 emulator_PTE_value;
			//call the instruction emulator to emulate the instruction 
			//doing the write, will return the 32-bit PDE value and/or the
			//PTE value that the guest was trying to write
			emulatewrite(cr2, &emulator_PDE_value, &emulator_PTE_value)
			
			//update the shadow entry
			shadow_updateshadowentries(cr2, &sPDE, &sPTE, emulator_PDE_value, emulator_PTE_value);
		
		}else{
			//this is a write-fault that the OS has to handle, pass it on...
			return VMX_EVENT_INJECT;
		}

  }else{
    return VMX_EVENT_INJECT;
  }
}


//invalidate a shadow paging structure
void shadow_invalidate_page(u32 address){
  
  u32 *sPDE, *sPTE;

  // XXX Non-deterministic adversary reduction
  //u32 *gPDE, *gPTE;
  u32 gPDentry = nondet_u32();
  u32 gPTentry = nondet_u32();
  u32 *gPDE = &gPDentry;
  u32 *gPTE = &gPTentry;


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
	*sPDE=0;
      }		
    }
  }
  return;
}


//new context, CR3 load
u32 shadow_new_context(u32 guest_CR3){
	//[opt1]
	list context_list;
	
	shadow_guest_CR3 = guest_CR3;

	//[opt1]: see if we have seen this guest context before
	for(i=0; i < number_of_vms; i++){
		context_list = vmlist[i].context_list;
		number_of_contexts = vmlist[i].number_of_contexts;
		for(j=0; j < number_of_contexts; j++){
			context_guestcr3 = contextlist[j].context_guestcr3;
			if(context_guestcr3 == guest_CR3)	//if we found a cached context, simply return its shadow pd table
				return contextlist[j].__shadow_npae_pd_table;
		}
	}
	
	
	//[opt1]: ok, this is a new context, so create room for it in the current vms context list
	vm_index = get_current_VM();
	vmlist[vm_index].number_of_contexts++;
	
	//[opt1]: store the guest_CR3 in the new context list entry
	context_list = vmlist[vm_index].context_list;
	context_list_index = vmlist[vm_index].number_of_contexts; 
	context_list[context_list_index].context_guestcr3 = guest_cr3;
	
	/*//[opt1]: zero out all the page table for this new context
	{
    u32 num_pagedir_entries;
    u32 *pgdir =((u32 *)(context_list[context_list_index].__shadow_npae_pd_table)); 
    num_pagedir_entries = GUEST_VIRTUALMEMORY_LIMIT / (4096*1023);

    for (u32 i= 0; i < num_pagedir_entries; i++) {
      pgdir[i] = 0;
    }
  }*/
  
  //[opt2]: scan all the guest paging entries and populate the shadow
  {
		u32 num_pagedir_entries;
		num_pagedir_entries = GUEST_VIRTUALMEMORY_LIMIT / (4096*1023);
		u32 *guest_pgdir = ((u32 *)(context_list[context_list_index].guest_CR3));	 
		u32 *shadow_pgdir = ((u32 *)(context_list[context_list_index].__shadow_npae_pd_table)); 
		u32 va=0;
		
    for (u32 i= 0; i < num_pagedir_entries; i++) {
      guest_pde = guest_pgdir[i];
      shadow_pde = shadow_pgdir[i];
    	
			u32 *guest_ptable = npae_get_paddr_from_pde(guest_pde);
			u32 *shadow_ptable = npae_get_paddr_from_pde(shadow_pde);
			for(u32 j=0; j < NPAE_PTRS_PER_PDT; j++){
				va += PAGE_SIZE_4K;
				guest_pte = guest_ptable[j];
				shadow_pte = shadow_ptable[j];
				shadow_updateshadowentries(va, guest_pde, guest_pte, shadow_pde, shadow_pte);
			}
    }
	}
  
  //[opt2] make guest page tables in the shadow read-only
  shadow_make_guest_pagetables_read_only(context_list[context_list_index].__shadow_npae_pd_table);
  
  //[opt1]: return the page directory of the new context
	return contextlist[context_list_index].__shadow_npae_pd_table; 
}

