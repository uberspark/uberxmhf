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
#include <vtx.h>
#include <paging.h>
#include <io.h>
#include <str.h>
#include <machine.h>
#include <error.h>
#include <shadow_paging_npae.h>

#define GUEST_PHYSICALMEMORY_LIMIT	(512*1024*1024) //512M guest physical limit

u32 shadow_guest_CR3=0;

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




/* /\* ------------ Start for verification ------------ *\/ */

/* u32 nondet_u32(); */
/* int nondet_int(); */

/* u32 shadow_new_context(u32 guest_CR3); */
/* void shadow_invalidate_page(u32 address); */
/* u32 shadow_page_fault(u32 cr2, u32 error_code); */

/* void init_visor() { */

/*     // Set initial state of guest and shadow pd */
/*     //spd = nondet_pdt();  */
/*     //gpd = nondet_pdt(); */

/*     //assume all mapped phy address are less than or equal protected_mem_start */
/*   __CPROVER_assume( npae_get_addr_from_pte(**gPTE) <= GUEST_PHYSICALMEMORY_LIMIT); */

/*     //nondet calls */
/*     int choice = nondet_int(); */

/*     if (choice == 0) { */
/*         shadow_new_context(nondet_u32()); */
/*     } else if (choice == 1) { */
/*         shadow_invalidate_page(nondet_u32()); */
/*     } else { */
/*         shadow_page_fault(nondet_u32(), nondet_u32()); */
/*     } */

/*     // SECURITY PROPERTY */
/*     assert( npae_get_addr_from_pte(**gPTE) <= GUEST_PHYSICALMEMORY_LIMIT); */
/* } */

/* /\* ------------ End for verification ------------ *\/ */



//------------------------------------------------------------------------------
//return pointers to the 32-bit SHADOW pde and pte for a given guest
//virtual address
//an entry will be null (0) if not present or applicable
void shadow_get_shadowentry(u32 gva, u32 **pdt_entry, u32 **pt_entry){
	u32 index_pdt, index_pt; 
	npdt_t s_pdt = (npdt_t)(u32)__shadow_npae_pd_table;
	npt_t s_pt;
	u32 s_pdt_entry, s_pt_entry;
	
	index_pdt= (gva >> 22);
	index_pt  = ((gva & (u32)0x003FFFFF) >> 12);
	
	*pdt_entry = *pt_entry = (u32 *)0;	//zero all
	
	s_pdt_entry = s_pdt[index_pdt];
	*pdt_entry = (u32 *)&s_pdt[index_pdt];

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
	npdt_t g_pdt=(npdt_t)gpa_to_hpa((u32)npae_get_addr_from_32bit_cr3(gCR3));;
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
u32 shadow_alloc_pt(u32 gva){
	u32 index_pdt;
	index_pdt= (gva >> 22);
	memset( (void *)((index_pdt * PAGE_SIZE_4K) + (u32)__shadow_npae_p_tables), 0, PAGE_SIZE_4K);
	return ( ((index_pdt * PAGE_SIZE_4K) + (u32)__shadow_npae_p_tables) );
}


//returns 1 if the page is present in guest, else 0
u32 is_present_guest(u32 *gPDE, u32 *gPTE){
	ASSERT ( gPDE != (u32 *)0 );
	
	if( !(*gPDE & _PAGE_PRESENT) )
		return 0;
	
	if( *gPDE & _PAGE_PSE )
		return 1;
	
	ASSERT ( gPTE != (u32 *)0 );
	
	if( !(*gPTE & _PAGE_PRESENT) )
		return 0;
	else
		return 1;
}


void set_guestentry_accessed(u32 *gPDE, u32 *gPTE){
	u32 *guest_entry;
	
	ASSERT( gPDE != (u32 *)0 );
	
	if( ! (*gPDE & _PAGE_PRESENT) )
		return;

	*gPDE |= _PAGE_ACCESSED;
	
	if(*gPDE & _PAGE_PSE)
		return;
		
	ASSERT( gPTE != (u32 *)0 );
	
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
	
	ASSERT( *gPDE != (u32 *)0 ); //gPDE MUST be valid, either a 4M page or point to a PT
	ASSERT( **gPDE & _PAGE_PRESENT );

	if( **gPDE & _PAGE_PSE){	//4M page
			//copy the entire entry into shadow
			**sPDE = **gPDE;			
	}else{	//4K page table
		flags=npae_get_flags_from_pde(**gPDE);
		paddr=npae_get_addr_from_pde(**sPDE);
		//propagate guest PDE flags to shadow PDE
		**sPDE = npae_make_pde(paddr, flags);
			
		ASSERT( *gPTE != (u32 *)0 ); //gPTE MUST be valid and present
		ASSERT( **gPTE & _PAGE_PRESENT );

		//check if we have a valid shadow PT
		if(*sPTE == (u32 *)0){	//no shadow PT, so assign one
			ASSERT(paddr == 0);
			paddr = shadow_alloc_pt(gva);
			**sPDE = npae_make_pde(paddr, flags);
			*sPTE = (u32 *)(paddr + (index_pt * sizeof(u32))); 			
		}	
			
		//copy the entire entry into shadow	
		if( npae_get_addr_from_pte(**gPTE) <= GUEST_PHYSICALMEMORY_LIMIT){
			**sPTE = **gPTE;
		}else{
			printf("\nillegal mapping!");
			HALT();				
		}

		//copy the entire entry into shadow	
		//**sPTE = **gPTE;	
	}

}


//[DEBUG]: dump the page table entries for both shadow and guest
void sdbg_dumpentries(u32 *gPDE, u32 *gPTE,
		u32 *sPDE, u32 *sPTE){
	ASSERT( (gPDE != (u32 *)0 && sPDE != (u32 *)0) );
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

	printf("\n0x%04x:0x%08x: #PF (cr2=0x%08x, error_code=0x%08x), pair=%u,%u -> ", 
		(unsigned short)guest_CS_selector, (unsigned int)guest_RIP, 
		(unsigned int)cr2, (unsigned int)error_code, index_pdt, index_pt);

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
	ASSERT( sPDE != (u32 *)0 );
	ASSERT( *sPDE & _PAGE_PRESENT );
	
	if(*sPDE & _PAGE_PSE){	//4M page
		original_rw_bit = (*sPDE & _PAGE_SHADOW_ORIGINALRWBIT);
		shadow_entry = sPDE;
	}else{
		ASSERT( sPTE != (u32 *)0 );
		ASSERT( *sPTE & _PAGE_PRESENT );
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
	ASSERT( sPDE != (u32 *)0 );
	ASSERT( *sPDE & _PAGE_PRESENT );
	
	if(*sPDE & _PAGE_PSE){	//4M page
		shadow_entry = sPDE;
	}else{
		ASSERT( sPTE != (u32 *)0 );
		ASSERT( *sPTE & _PAGE_PRESENT );
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
	ASSERT( gPDE != (u32 *)0 );
	ASSERT( *gPDE & _PAGE_PRESENT );
	
	if(*gPDE & _PAGE_PSE){	//4M page
		original_rw_bit = (*gPDE & _PAGE_RW);
		shadow_entry = sPDE;
	}else{
		ASSERT( gPTE != (u32 *)0 );
		ASSERT( *gPTE & _PAGE_PRESENT );
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
	ASSERT( sPDE != (u32 *)0 );
	ASSERT( *sPDE & _PAGE_PRESENT );
	
	if(*sPDE & _PAGE_PSE){	//4M page
		shadow_entry = sPDE;
	}else{
		ASSERT( sPTE != (u32 *)0 );
		ASSERT( *sPTE & _PAGE_PRESENT );
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
	ASSERT( gPDE != (u32 *)0 );
	ASSERT( *gPDE & _PAGE_PRESENT );
	
	if(*gPDE & _PAGE_PSE){	//4M page
		guest_entry = gPDE;
	}else{
		ASSERT( gPTE != (u32 *)0 );
		ASSERT( *gPTE & _PAGE_PRESENT );
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
	
	//[debug]
	//sdbg_dumppfdetails(cr2, error_code);
	
	//[scheck] RSVD bit set, should never happen during normal execution
	if(error_code & PFERR_RSVD_MASK){
		printf("\nRSVD bit set on page-fault, Halt!");
		HALT();
	}

	//[scheck] we assume CR0.WP=1 always
	ASSERT( ((guest_CR0 & CR0_WP) && (control_CR0_shadow & CR0_WP)) );

	//get SHADOW and GUEST paging entries for the fault-address (CR2)
	shadow_get_guestentry(cr2, shadow_guest_CR3, &gPDE, &gPTE);
	shadow_get_shadowentry(cr2, &sPDE, &sPTE);
	//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE);

	//if(!shadow_checkcontext( (u32)npae_get_addr_from_32bit_cr3((u32)shadow_guest_CR3) ) ){
	//		printf("\nPF: Halting, reserved bits set in GUEST paging structures!");
	//		HALT();
	//}	

	
	if( !(error_code & PFERR_PRESENT_MASK) ){
			if(is_present_guest(gPDE, gPTE)){
				//printf("\n	SHADOW-NOT-PRESENT (GUEST-PRESENT): syncing...");


				shadow_updateshadowentries(cr2, &sPDE, &sPTE,
					&gPDE, &gPTE);
				
				//set_guestentry_accessed(gPDE, gPTE);
				//set_shadowentry_dirtywaiting(sPDE, sPTE, gPDE, gPTE);
				
				if(!shadow_checkcontext((u32)__shadow_npae_pd_table)){
					//printf("\nPF: Halting, reserved bits set in SHADOW paging structures!");
					HALT();
				}	

				//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE);
				return VMX_EVENT_CANCEL;
			}else{
				//set_guestentry_accessed(gPDE, gPTE);
				//printf("\n	SHADOW-NOT-PRESENT (GUEST-NOT-PRESENT): injecting #PF into guest (NP fault).");
				return VMX_EVENT_INJECT;
			}
	}else if (error_code & PFERR_WR_MASK){
			ASSERT(is_present_guest(gPDE, gPTE));

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
	
	//printf("\n0x%04x:0x%08x: INVLPG (address=0x%08x)", 
	//	(unsigned short)guest_CS_selector, (unsigned int)guest_RIP, 
	//	(unsigned int)address);

	shadow_get_guestentry(address, shadow_guest_CR3, &gPDE, &gPTE);
	shadow_get_shadowentry(address, &sPDE, &sPTE);
	//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE);

	ASSERT( gPDE != (u32 *)0 );
	ASSERT( sPDE != (u32 *)0 );

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
				ASSERT(*sPDE & _PAGE_PSE);
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

	memset((void *)__shadow_npae_pd_table, 0, PAGE_SIZE_4K);

	//we need to populate GDT, IDT and TSS memory pages as we dont want
	//them causing double/triple faults that we will need to process
	//NOTE: dirty bits for these structures are never used in any OS
	//as these structures are never paged-out!
	//UPDATE: 1/13/2010
	//Windows HAL uses PAE paging structures during initialization and
	//they do not contain the GDT/IDT/TR mapped!!
	{
		u32 start_va, end_va;	//pages from start_va to end_va inclusive
		u32 va;
		u32 *gPDE, *gPTE;
		u32 *sPDE, *sPTE;

		//printf("\n%s: pre-loading guest GDT, IDT and TR pages...");

		start_va = PAGE_ALIGN_4K (guest_GDTR_base);
		end_va = PAGE_ALIGN_4K( (guest_GDTR_base + guest_GDTR_limit) );
		//printf("\n	GDT pages=0x%08x-0x%08x inclusive",	start_va, end_va); 

		for(va=start_va; va <= end_va; va+= PAGE_SIZE_4K){
			shadow_get_guestentry(va, shadow_guest_CR3, &gPDE, &gPTE);
			shadow_get_shadowentry(va, &sPDE, &sPTE);
			if(is_present_guest(gPDE, gPTE)){
				//printf("\n	Structures BEFORE:");
				//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE);
				shadow_updateshadowentries(va, &sPDE, &sPTE,
						&gPDE, &gPTE);
				//printf("\n	Structures AFTER:");
				//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE);
			}else{
				//printf("\n	GUEST NOT-PRESENT!");
			}
		}

		start_va = PAGE_ALIGN_4K (guest_IDTR_base);
		end_va = PAGE_ALIGN_4K( (guest_IDTR_base + guest_IDTR_limit) );
		//printf("\n	IDT pages=0x%08x-0x%08x inclusive",	start_va, end_va); 

		for(va=start_va; va <= end_va; va+= PAGE_SIZE_4K){
			shadow_get_guestentry(va, shadow_guest_CR3, &gPDE, &gPTE);
			shadow_get_shadowentry(va, &sPDE, &sPTE);
			if(is_present_guest(gPDE, gPTE)){
				//printf("\n	Structures BEFORE:");
				//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE);
				shadow_updateshadowentries(va, &sPDE, &sPTE,
						&gPDE, &gPTE);
				//printf("\n	Structures AFTER:");
				//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE);
			}else{
				//printf("\n	GUEST NOT-PRESENT!");
			}
		}

		start_va = PAGE_ALIGN_4K(guest_TR_base);
		end_va = PAGE_ALIGN_4K( (guest_TR_base + guest_TR_limit) );
		//printf("\n	TR pages=0x%08x-0x%08x inclusive",	start_va, end_va); 

		for(va=start_va; va <= end_va; va+= PAGE_SIZE_4K){
			shadow_get_guestentry(va, shadow_guest_CR3, &gPDE, &gPTE);
			shadow_get_shadowentry(va, &sPDE, &sPTE);
			if(is_present_guest(gPDE, gPTE)){
				//printf("\n	Structures BEFORE:");
				//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE);
				shadow_updateshadowentries(va, &sPDE, &sPTE,
						&gPDE, &gPTE);
				//printf("\n	Structures AFTER:");
				//sdbg_dumpentries(gPDE, gPTE, sPDE, sPTE);
			}else{
				//printf("\n	GUEST NOT-PRESENT!");
			}
		}
	
	}

	//return our shadow pd table address which will be the new CR3
	//for the guest
	return (u32)__shadow_npae_pd_table; 
#else

	//if(!shadow_checkcontext( (u32)npae_get_addr_from_32bit_cr3((u32)guest_CR3) ) ){
	//	printf("\nHalting, reserved bits set in GUEST paging structures!");
	//	HALT();
	//}	

	return guest_CR3;
	
#endif
}

