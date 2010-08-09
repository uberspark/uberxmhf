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
// shadow_paging.c
//
// intel vt-x hypervisor memory isolation using shadow paging (PAE-mode)
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
#include <shadow_paging.h>

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

//------------------------------------------------------------------------------
//return pointers to the 64-bit SHADOW pdpte, pde and pte for a given guest
//virtual address
//an entry will be null (0) if not present or applicable
void shadow_get_shadowentry(u32 gva, u64 **pdpt_entry, u64 **pdt_entry, u64 **pt_entry){
	u32 index_pdpt, index_pdt, index_pt; 
	pdpt_t s_pdpt = (pdpt_t)__shadow_pdp_table;
	pdt_t s_pdt;
	pt_t s_pt;
	u64 s_pdpt_entry, s_pdt_entry, s_pt_entry;
	
	index_pdpt= (gva >> 30);
	index_pdt = ((gva & (u32)0x3FFFFFFF) >> 21);
	index_pt  = ((gva & (u32)0x001FFFFF) >> 12);
	
	*pdpt_entry = *pdt_entry = *pt_entry = (u64 *)0;	//zero all
	
	s_pdpt_entry = s_pdpt[index_pdpt];
	*pdpt_entry = (u64 *)&s_pdpt[index_pdpt];
	if( !(s_pdpt_entry & _PAGE_PRESENT) )
		return; 
	
	s_pdt = (pdt_t)(u32)pae_get_addr_from_pdpe(s_pdpt_entry);
	
	s_pdt_entry = s_pdt[index_pdt];
	*pdt_entry = (u64 *)&s_pdt[index_pdt];
	if (! (s_pdt_entry & _PAGE_PRESENT) )
		return;
		
	if(s_pdt_entry & _PAGE_PSE)
		return; //this is a 2M page directory entry, so there is no pt
		
	//this is a regular page directory entry, so get the page table
	s_pt = (pt_t)(u32)pae_get_addr_from_pde(s_pdt_entry);
	*pt_entry = (u64 *)&s_pt[index_pt]; 
	return;
}

//------------------------------------------------------------------------------
//return pointers to the 64-bit SHADOW pdpte, pde and pte for a given guest
//virtual address
//an entry will be null (0) if not present or applicable
//set the ACCESSED bit
//as we traverse the guest paging structures 
void shadow_get_guestentry(u32 gva, u32 gCR3, u64 **pdpt_entry, u64 **pdt_entry, u64 **pt_entry){
	u32 index_pdpt, index_pdt, index_pt; 
	pdpt_t g_pdpt = (pdpt_t)gpa_to_hpa((u32)pae_get_addr_from_32bit_cr3(gCR3));
	pdt_t g_pdt;
	pt_t g_pt;
	u64 g_pdpt_entry, g_pdt_entry, g_pt_entry;
	
	index_pdpt= (gva >> 30);
	index_pdt = ((gva & (u32)0x3FFFFFFF) >> 21);
	index_pt  = ((gva & (u32)0x001FFFFF) >> 12);
	
	*pdpt_entry = *pdt_entry = *pt_entry = (u64 *)0;	//zero all
	
	g_pdpt_entry = g_pdpt[index_pdpt];
	*pdpt_entry = (u64 *)&g_pdpt[index_pdpt];
	if( !(g_pdpt_entry & _PAGE_PRESENT) )
		return;	//though we have traversed the PDPT, we dont set accessed on PDPTEs 

	g_pdt = (pdt_t)gpa_to_hpa((u32)pae_get_addr_from_pdpe(g_pdpt_entry));
	
	g_pdt_entry = g_pdt[index_pdt];
	*pdt_entry = (u64 *)&g_pdt[index_pdt];
	if (! (g_pdt_entry & _PAGE_PRESENT) )
		return;

/*
	//set ACCESSED bit on this pdt entry
	g_pdt[index_pdt] |= _PAGE_ACCESSED;
*/
		
	if(g_pdt_entry & _PAGE_PSE)
		return; //this is a 2M page directory entry, so no pt present
		
	//this is a regular page directory entry, so get the page table
	g_pt = (pt_t)gpa_to_hpa((u32)pae_get_addr_from_pde(g_pdt_entry));

/*	
	//set ACCESSED bit on this pt entry
	if(g_pt[index_pt] & _PAGE_PRESENT)
		g_pt[index_pt] |= _PAGE_ACCESSED;
*/
	
	*pt_entry = (u64 *)&g_pt[index_pt]; 
	return;
}


//allocate, zero and return the address of a page directory table
u32 shadow_alloc_pdt(u32 gva){
	u32 index_pdpt;
	
	index_pdpt= (gva >> 30);
	
	memset( (void *)((index_pdpt * PAGE_SIZE_4K) + (u32)__shadow_pd_tables), 0, PAGE_SIZE_4K);
	return ( (index_pdpt * PAGE_SIZE_4K) + (u32)__shadow_pd_tables );
}

//allocate, zero and return the address of a page table
u32 shadow_alloc_pt(u32 gva){
	u32 index_pdpt, index_pdt;
	
	index_pdpt= (gva >> 30);
	index_pdt = ((gva & (u32)0x3FFFFFFF) >> 21);
	
	//((((index_pdpt * PAE_PTRS_PER_PDT) + index_pdt) * PAGE_SIZE_4K) + (u32)__shadow_p_tables);
	
	memset( (void *)((((index_pdpt * PAE_PTRS_PER_PDT) + index_pdt) * PAGE_SIZE_4K) + (u32)__shadow_p_tables), 0, PAGE_SIZE_4K);
	return ( ((((index_pdpt * PAE_PTRS_PER_PDT) + index_pdt) * PAGE_SIZE_4K) + (u32)__shadow_p_tables) );
}


//returns 1 if the page is present in guest, else 0
u32 is_present_guest(u64 *gPDPTE, u64 *gPDE, u64 *gPTE){
	ASSERT ( gPDPTE != (u64 *)0 );
	
	if( !(*gPDPTE & _PAGE_PRESENT) )
		return 0;
		
	ASSERT ( gPDE != (u64 *)0 );
	
	if( !(*gPDE & _PAGE_PRESENT) )
		return 0;
	
	if( *gPDE & _PAGE_PSE )
		return 1;
	
	ASSERT ( gPTE != (u64 *)0 );
	
	if( !(*gPTE & _PAGE_PRESENT) )
		return 0;
	else
		return 1;
}


void set_guestentry_accessed(u64 *gPDPTE, u64 *gPDE, u64 *gPTE){
	u64 *guest_entry;
	
	//determine which GUEST entry we will use (PDE or PTE)
	ASSERT( gPDPTE != (u64 *)0 );
	ASSERT( *gPDPTE & _PAGE_PRESENT );
	ASSERT( gPDE != (u64 *)0 );
	ASSERT( *gPDE & _PAGE_PRESENT );
	
	if(*gPDE & _PAGE_PSE){	//2M page
		guest_entry = gPDE;
	}else{
		ASSERT( gPTE != (u64 *)0 );
		ASSERT( *gPTE & _PAGE_PRESENT );
		guest_entry = gPTE;
	}

	//set ACCESSED bit
	*guest_entry |= _PAGE_ACCESSED;

}


//never called for a non-present guest page
void shadow_updateshadowentries(u32 gva, u64 **sPDPTE, u64 **sPDE, u64 **sPTE,
	u64 **gPDPTE, u64 **gPDE, u64 **gPTE){
	
	u32 index_pdpt, index_pdt, index_pt; 
	u64 flags;
	u32 paddr;
	ASSERT( (*gPDPTE != (u64 *)0 && *sPDPTE != (u64 *)0) );
	ASSERT( **gPDPTE & _PAGE_PRESENT); //gPDPTE MUST be present
	
	index_pdpt= (gva >> 30);
	index_pdt = ((gva & (u32)0x3FFFFFFF) >> 21);
	index_pt  = ((gva & (u32)0x001FFFFF) >> 12);
	
	printf("\n	index_pdpt=%u, index_pdt=%u, index_pt=%u", index_pdpt, index_pdt, index_pt);
	
		flags=pae_get_flags_from_pdpe(**gPDPTE);
		paddr=pae_get_addr_from_pdpe(**sPDPTE);
		//propagate guest PDPTE flags to shadow PDPTE
		**sPDPTE = pae_make_pdpe(paddr, flags);

		ASSERT( *gPDE != (u64 *)0 ); //gPDE MUST be valid, either a 2M page or point to a PT
		ASSERT( **gPDE & _PAGE_PRESENT );

		//check if we have a valid shadow PD
		if(*sPDE == (u64 *)0){	//no shadow PD, so assign one
			ASSERT(paddr == 0);
			paddr = shadow_alloc_pdt(gva);
			**sPDPTE = pae_make_pdpe(paddr, flags);
			*sPDE = (u64 *)(paddr + (index_pdt * sizeof(u64))); 			
		}

			
		if( **gPDE & _PAGE_PSE){	//2M page
			//copy the entire entry into shadow
			**sPDE = **gPDE;			
		}else{	//4K page table
			flags=pae_get_flags_from_pde(**gPDE);
			paddr=pae_get_addr_from_pde(**sPDE);
			//propagate guest PDE flags to shadow PDE
			**sPDE = pae_make_pde(paddr, flags);
			
			ASSERT( *gPTE != (u64 *)0 ); //gPTE MUST be valid and present
			ASSERT( **gPTE & _PAGE_PRESENT );

			//check if we have a valid shadow PT
			if(*sPTE == (u64 *)0){	//no shadow PT, so assign one
				ASSERT(paddr == 0);
				paddr = shadow_alloc_pt(gva);
				**sPDE = pae_make_pde(paddr, flags);
				*sPTE = (u64 *)(paddr + (index_pt * sizeof(u64))); 			
			}	
			
				
			//copy the entire entry into shadow	
			**sPTE = **gPTE;	
		}

}


//[DEBUG]: dump the page table entries for both shadow and guest
void sdbg_dumpentries(u64 *gPDPTE, u64 *gPDE, u64 *gPTE,
		u64 *sPDPTE, u64 *sPDE, u64 *sPTE){
	ASSERT( (gPDPTE != (u64 *)0 && sPDPTE != (u64 *)0) );
	printf("\n	__s_pdp=0x%08x, __s_pd=0x%08x, __s_pt=0x%08x", 
		(u32)__shadow_pdp_table, (u32)__shadow_pd_tables, (u32)__shadow_p_tables);
	printf("\n	PDPTEs: g=0x%016llx, s=0x%016llx", *gPDPTE, *sPDPTE);
	
	printf("\n	PDEs	: ");
	if(gPDE)
		printf("g=0x%016llx, ", *gPDE);
	else
		printf("g=<     NP         >, ");

	if(sPDE)
		printf("s=0x%016llx", *sPDE);
	else
		printf("s=<     NP         >");
	
	printf("\n	PTEs	: ");
	if(gPTE)
		printf("g=0x%016llx, ", *gPTE);
	else
		printf("g=<     NP         >, ");

	if(sPTE)
		printf("s=0x%016llx", *sPTE);
	else
		printf("s=<     NP         >");
	
	return;		
}

//[DEBUG]: dumps PF details
void sdbg_dumppfdetails(u32 cr2, u32 error_code){
	u32 index_pdpt, index_pdt, index_pt;
	
	index_pdpt= (cr2 >> 30);
	index_pdt = ((cr2 & (u32)0x3FFFFFFF) >> 21);
	index_pt  = ((cr2 & (u32)0x001FFFFF) >> 12);

	printf("\n0x%04x:0x%08x: #PF (cr2=0x%08x, error_code=0x%08x), triad=%u,%u,%u -> ", 
		(unsigned short)guest_CS_selector, (unsigned int)guest_RIP, 
		(unsigned int)cr2, (unsigned int)error_code, index_pdpt, index_pdt, index_pt);

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
void clear_shadowentry_dirtywaiting(u64 *sPDPTE, u64 *sPDE, u64 *sPTE){
	u32 original_rw_bit;
	u64 *shadow_entry;
	
	//grab original RW bit value 
	//and also determine which shadow entry we will use (PDE or PTE)
	ASSERT( sPDPTE != (u64 *)0 );
	ASSERT( *sPDPTE & _PAGE_PRESENT );
	ASSERT( sPDE != (u64 *)0 );
	ASSERT( *sPDE & _PAGE_PRESENT );
	
	if(*sPDE & _PAGE_PSE){	//2M page
		original_rw_bit = (*sPDE & _PAGE_SHADOW_ORIGINALRWBIT);
		shadow_entry = sPDE;
	}else{
		ASSERT( sPTE != (u64 *)0 );
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
u32 is_shadowentry_writable(u64 *sPDPTE, u64 *sPDE, u64 *sPTE){
	u32 original_rw_bit;
	u64 *shadow_entry;
	
	//grab original RW bit value 
	//and also determine which shadow entry we will use (PDE or PTE)
	ASSERT( sPDPTE != (u64 *)0 );
	ASSERT( *sPDPTE & _PAGE_PRESENT );
	ASSERT( sPDE != (u64 *)0 );
	ASSERT( *sPDE & _PAGE_PRESENT );
	
	if(*sPDE & _PAGE_PSE){	//2M page
		shadow_entry = sPDE;
	}else{
		ASSERT( sPTE != (u64 *)0 );
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
void set_shadowentry_dirtywaiting(u64 *sPDPTE, u64 *sPDE, u64 *sPTE,
			u64 *gPDPTE, u64 *gPDE, u64 *gPTE){
	u32 original_rw_bit;
	u64 *shadow_entry;
	
	//grab original RW bit value from guest paging structures
	//and also determine which shadow entry we will use (PDE or PTE)
	ASSERT( gPDPTE != (u64 *)0 );
	ASSERT( *gPDPTE & _PAGE_PRESENT );
	ASSERT( gPDE != (u64 *)0 );
	ASSERT( *gPDE & _PAGE_PRESENT );
	
	if(*gPDE & _PAGE_PSE){	//2M page
		original_rw_bit = (*gPDE & _PAGE_RW);
		shadow_entry = sPDE;
	}else{
		ASSERT( gPTE != (u64 *)0 );
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
u32 is_shadowentry_dirtywaiting(u64 *sPDPTE, u64 *sPDE, u64 *sPTE){
	u64 *shadow_entry;
	
	//determine which shadow entry we will use (PDE or PTE)
	ASSERT( sPDPTE != (u64 *)0 );
	ASSERT( *sPDPTE & _PAGE_PRESENT );
	ASSERT( sPDE != (u64 *)0 );
	ASSERT( *sPDE & _PAGE_PRESENT );
	
	if(*sPDE & _PAGE_PSE){	//2M page
		shadow_entry = sPDE;
	}else{
		ASSERT( sPTE != (u64 *)0 );
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
void set_guestentry_dirty(u64 *gPDPTE, u64 *gPDE, u64 *gPTE){
	u64 *guest_entry;
	
	//determine which GUEST entry we will use (PDE or PTE)
	ASSERT( gPDPTE != (u64 *)0 );
	ASSERT( *gPDPTE & _PAGE_PRESENT );
	ASSERT( gPDE != (u64 *)0 );
	ASSERT( *gPDE & _PAGE_PRESENT );
	
	if(*gPDE & _PAGE_PSE){	//2M page
		guest_entry = gPDE;
	}else{
		ASSERT( gPTE != (u64 *)0 );
		ASSERT( *gPTE & _PAGE_PRESENT );
		guest_entry = gPTE;
	}

	//check for dirty-waiting
	*guest_entry |= _PAGE_DIRTY;
}



//------------------------------------------------------------------------------
// #PF handling
//should return VMX_EVENT_INJECT if the page-fault has to be
//injected into the guest, else VMX_EVENT_CANCEL
u32 shadow_page_fault(u32 cr2, u32 error_code){
#if 1
	u64 *gPDPTE, *gPDE, *gPTE;
	u64 *sPDPTE, *sPDE, *sPTE;
	
	//[debug]
	sdbg_dumppfdetails(cr2, error_code);
	
	//[scheck] RSVD bit set, should never happen during normal execution
	if(error_code & PFERR_RSVD_MASK){
		printf("\nRSVD bit set on page-fault, dumping shadow root structures:");
		printf("\nHalt!");
		HALT();
	}

	//[scheck] we assume CR0.WP=1 always
	ASSERT( ((guest_CR0 & CR0_WP) && (control_CR0_shadow & CR0_WP)) );

	//get SHADOW and GUEST paging entries for the fault-address (CR2)
	shadow_get_guestentry(cr2, shadow_guest_CR3, &gPDPTE, &gPDE, &gPTE);
	shadow_get_shadowentry(cr2, &sPDPTE, &sPDE, &sPTE);

	//sdbg_dumpentries(gPDPTE, gPDE, gPTE, sPDPTE, sPDE, sPTE);

	//if(!shadow_checkcontext( (u32)pae_get_addr_from_32bit_cr3((u32)shadow_guest_CR3) ) ){
	//		printf("\nPF: Halting, reserved bits set in GUEST paging structures!");
	//		HALT();
	//}	

	
	if( !(error_code & PFERR_PRESENT_MASK) ){
			if(is_present_guest(gPDPTE, gPDE, gPTE)){
				printf("\n	SHADOW-NOT-PRESENT (GUEST-PRESENT): syncing...");


				shadow_updateshadowentries(cr2, &sPDPTE, &sPDE, &sPTE,
					&gPDPTE, &gPDE, &gPTE);
				/*
				set_shadowentry_dirtywaiting(sPDPTE, sPDE, sPTE, gPDPTE, gPDE, gPTE);
				*/
				
				if(!shadow_checkcontext((u32)__shadow_pdp_table)){
					printf("\nPF: Halting, reserved bits set in SHADOW paging structures!");
					HALT();
				}	

				//sdbg_dumpentries(gPDPTE, gPDE, gPTE, sPDPTE, sPDE, sPTE);
				return VMX_EVENT_CANCEL;
			}else{
				printf("\n	SHADOW-NOT-PRESENT (GUEST-NOT-PRESENT): injecting #PF into guest (NP fault).");
				return VMX_EVENT_INJECT;
			}
/*	}else if (error_code & PFERR_WR_MASK){
			if(is_shadowentry_dirtywaiting(sPDPTE, sPDE, sPTE)){
				printf("\n	SHADOW-PRESENT (GUEST-PRESENT): processing dirty-waiting...");
				clear_shadowentry_dirtywaiting(sPDPTE, sPDE, sPTE);
				if(is_shadowentry_writable(sPDPTE, sPDE, sPTE))
					set_guestentry_dirty(gPDPTE, gPDE, gPTE);			
				return VMX_EVENT_CANCEL;
			}else{
				printf("\n	SHADOW-PRESENT (GUEST-PRESENT): injecting #PF into guest (R/W fault).");
				return VMX_EVENT_INJECT;
			}
	}else{
			printf("\n	SHADOW-PRESENT (GUEST-PRESENT): injecting #PF into guest (other fault).");
			return VMX_EVENT_INJECT;
	}*/
	}else{
			return VMX_EVENT_INJECT;
	}

#else

	if(error_code & PFERR_RSVD_MASK){
		printf("\nRSVD bit set on page-fault, hmhmhmm!!!");
		printf("\nHalt!");
		HALT();
	}

	return VMX_EVENT_INJECT;
#endif
}

//------------------------------------------------------------------------------
//invalidate a shadow paging structure
void shadow_invalidate_page(u32 address){
#if 1	
	//(void)address;
	u64 *gPDPTE, *gPDE, *gPTE;
	u64 *sPDPTE, *sPDE, *sPTE;
	
	printf("\n0x%04x:0x%08x: INVLPG (address=0x%08x)", 
		(unsigned short)guest_CS_selector, (unsigned int)guest_RIP, 
		(unsigned int)address);

	shadow_get_guestentry(address, shadow_guest_CR3, &gPDPTE, &gPDE, &gPTE);
	shadow_get_shadowentry(address, &sPDPTE, &sPDE, &sPTE);
	sdbg_dumpentries(gPDPTE, gPDE, gPTE, sPDPTE, sPDE, sPTE);

#if 1	
	if(sPTE){
		*sPTE=0;
	}else{
		ASSERT(sPDE != (u64 *)0);
		ASSERT(*sPDE & _PAGE_PSE);
		*sPDE=0;
	}
#else
	*sPDE = 0;
	sPTE=0;	
#endif	
	printf("\n	after invalidation:");
	sdbg_dumpentries(gPDPTE, gPDE, gPTE, sPDPTE, sPDE, sPTE);
	printf("\n	done.");

#else	
	u64 *gPDPTE, *gPDE, *gPTE;
	printf("\n0x%04x:0x%08x: INVLPG (address=0x%08x)", 
		(unsigned short)guest_CS_selector, (unsigned int)guest_RIP, 
		(unsigned int)address);
	shadow_get_guestentry(address, shadow_guest_CR3, &gPDPTE, &gPDE, &gPTE);
	ASSERT( gPDPTE != (u64 *)0  );
	printf("\n	PDPTE: g=0x%016llx", *gPDPTE);
	printf("\n	PDE 	: ");
	if(gPDE)
		printf("g=0x%016llx, ", *gPDE);
	else
		printf("g=<     NP         >, ");

	printf("\n	PTE	: ");
	if(gPTE)
		printf("g=0x%016llx, ", *gPTE);
	else
		printf("g=<     NP         >, ");

	return;
#endif
}



// assuming 36-bit physical addresses
//PDPTE reserved mask
//     1111 1111 1111 1111 1111 1111 1111 0000 0000 0000 0000 0000 0000 0001 1110 0110
// = 0xFFFFFFF0000001E6ULL
//PDE reserved mask
//	2M pages
//   0111 1111 1111 1111 1111  1111 1111 0000 0000 0000 0001 1111 1110 0000 0000 0000		
// = 0x7FFFFFF0001FE000ULL
//  4K page table
//   0111 1111 1111 1111 1111 1111 1111 0000 0000 0000 0000 0000 0000 0000 0000 0000
// = 0x7FFFFFF000000000ULL
//PTE reserved mask
//   0111 1111 1111 1111 1111 1111 1111 0000 0000 0000 0000 0000 0000 0000 0000 0000   
// = 0x7FFFFFF000000000ULL
//------------------------------------------------------------------------------
//dump paging structures pointed to by root
//return 1 on success, 0 on failure (as a side prints out all entries
//with RSVD bits set)
u32 shadow_checkcontext(u32 root){
	pdpt_t pdpt;
	pdt_t pdt;
	pt_t pt;
	u32 i, j, k;
	u64 flags;
	u32 paddr;
	u32 status=1;

	//index_pdpt= (gva >> 30);
	//index_pdt = ((gva & (u32)0x3FFFFFFF) >> 21);
	//index_pt  = ((gva & (u32)0x001FFFFF) >> 12);
	

	pdpt = (pdpt_t)root;
	
	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		//printf("\n	PDPTE %u: 0x%016llx (PD=0x%08x)", i, pdpt[i], (unsigned int)pdt);
		
		if(pdpt[i] & _PAGE_PRESENT){
			if( pdpt[i] & 0xFFFFFFF0000001E6ULL){
				printf("\nRSVD bit set in PDPTE %u (0x%016llx)", i, pdpt[i]);
				status=0;
			}

			pdt = (pdt_t)(u32)pae_get_addr_from_pdpe(pdpt[i]);

			for(j=0; j < PAE_PTRS_PER_PDT; j++){
						
				if(pdt[j] & _PAGE_PRESENT){
						//check RSVD bits
					if (pdt[j] & _PAGE_PSE){
						if( pdt[j] & 0x7FFFFFF0001FE000ULL){
							printf("\nRSVD bit set in PDPTE %u PDE %u (0x%016llx)", i, j, pdt[j]);
							status=0;
						}	
					}else{
						if( pdt[j] & 0x7FFFFFF000000000ULL){
							printf("\nRSVD bit set in PDPTE %u PDE %u (0x%016llx)", i, j, pdt[j]);
							status=0;
						}
					}

					if(pdt[j] & _PAGE_PSE){
						//printf("\n	PDE %u: 0x%016llx (2M)", j, pdt[j]);
					}else{
						pt = (pt_t)(u32)pae_get_addr_from_pde(pdt[j]);
						//printf("\n	PDE %u: 0x%016llx (PT=0x%08x)", j, pdt[j], (unsigned int)pt);
		
						for(k=0; k < PAE_PTRS_PER_PT; k++){
							if(pt[k] & _PAGE_PRESENT){
								if( pt[k] & 0x7FFFFFF000000000ULL){
									printf("\nRSVD bit set in PDPTE %u PDE %u PTE %u (0x%016llx)", i, j, k, pt[k]);
									status=0;
								}
							}else{	
								//printf("\n			PTE %u: 0x%016llx (NOT-PRESENT)", k, pt[k]);	
							}
						}
					}
				}else{
						//printf("\n	PDE %u: 0x%016llx (NOT-PRESENT)", j, pdt[j]);
				}
			}
		}else{
			//printf("\n	PDPTE %u: 0x%016llx (NOT-PRESENT)", i, pdpt[i]);
		}
	
	}
	
	return status;	
}




//------------------------------------------------------------------------------
//copy guest paging structures to shadow
void shadow_copy(u32 gCR3){
	pdpt_t g_pdpt, s_pdpt;
	pdt_t g_pdt, s_pdt;
	pt_t g_pt, s_pt;
	u32 i, j, k;
	u64 flags;
	u32 paddr;
	u64 *gPDPTE, *gPDE, *gPTE;
	u64 *sPDPTE, *sPDE, *sPTE;
	
	
	g_pdpt = (pdpt_t) gpa_to_hpa(pae_get_addr_from_32bit_cr3(gCR3));
	s_pdpt = (pdpt_t) (u32)__shadow_pdp_table;

	//zero out pdpt and pd tables
	memset((void *)__shadow_pdp_table, 0, PAGE_SIZE_4K);
	memset((void *)__shadow_pd_tables, 0, PAE_PTRS_PER_PDPT * PAGE_SIZE_4K);
	memset((void *)__shadow_p_tables, 0, 2048 * PAGE_SIZE_4K);
	
	
	for(i=0; i < PAE_PTRS_PER_PDPT; i++){	//i=PDPTE iterator
		
		flags = pae_get_flags_from_pdpe(g_pdpt[i]);
		
		if( (flags & _PAGE_PRESENT) && !(g_pdpt[i] & 0xFFFFFFF0000001E6ULL) ){
			paddr= (i * PAGE_SIZE_4K) + (u32) __shadow_pd_tables;
			s_pdpt[i] = pae_make_pdpe(paddr, flags);
			
			//
			gPDPTE = (u64 *)&g_pdpt[i];
			sPDPTE = (u64 *)&s_pdpt[i];
			
			g_pdt = (pdt_t)(u32)gpa_to_hpa(pae_get_addr_from_pdpe(g_pdpt[i]));
			s_pdt = (pdt_t)(u32)pae_get_addr_from_pdpe(s_pdpt[i]);
			
			for(j=0; j < PAE_PTRS_PER_PDT; j++){	//j=PDE iterator
				flags = pae_get_flags_from_pde(g_pdt[j]);
				
				if(flags & _PAGE_PRESENT){
					
					if(flags & _PAGE_PSE){	//2M page
						if(!(g_pdt[j] & 0x7FFFFFF0001FE000ULL) ){
							s_pdt[j] = g_pdt[j];
							
							//
							gPDE = (u64 *)&g_pdt[j];
							sPDE = (u64 *)&s_pdt[j];
							gPTE = (u64 *)0;
							sPTE = (u64 *)0;

							set_guestentry_accessed(gPDPTE, gPDE, gPTE);							
							set_shadowentry_dirtywaiting(sPDPTE, sPDE, sPTE,
								gPDPTE, gPDE, gPTE);
							
						}else{
							s_pdt[j] = 0;
						}
					}else{		//4K page
						if( !(g_pdt[j] & 0x7FFFFFF000000000ULL) ){
							paddr= (((i * PAE_PTRS_PER_PDT) + j) * PAGE_SIZE_4K) + (u32)__shadow_p_tables;
						
							s_pdt[j] = pae_make_pde(paddr, flags);
			
							//
							gPDE = (u64 *)&g_pdt[j];
							sPDE = (u64 *)&s_pdt[j];
							
							g_pt = (pt_t)(u32)gpa_to_hpa(pae_get_addr_from_pde(g_pdt[j]));
							s_pt = (pt_t)(u32)pae_get_addr_from_pde(s_pdt[j]);				
							ASSERT( (u32)s_pt == paddr );

							for(k=0; k < PAE_PTRS_PER_PT; k++){
								flags = pae_get_flags_from_pte(g_pt[k]);
								if( (flags & _PAGE_PRESENT) && !(g_pt[k] & 0x7FFFFFF000000000ULL) ){
									s_pt[k] = g_pt[k];
									
									//
									gPTE = (u64 *)&g_pt[k];
									sPTE = (u64 *)&s_pt[k];

									set_guestentry_accessed(gPDPTE, gPDE, gPTE);							

									set_shadowentry_dirtywaiting(sPDPTE, sPDE, sPTE,
										gPDPTE, gPDE, gPTE);
									
								}else{
									s_pt[k] = 0;
								}
							}
						}else{
							s_pdt[j] = 0;
						}
					}
				}else{
					s_pdt[j]= 0; 
				}
			}
		}else{
			s_pdpt[i]=0;			
		}
	}
	
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

#if 1

#if 1
	//copy guest CR3 structures to shadow
	if(!shadow_checkcontext( (u32)pae_get_addr_from_32bit_cr3((u32)guest_CR3) ) ){
		printf("\nHalting, reserved bits set in GUEST paging structures!");
		HALT();
	}	
	shadow_copy(guest_CR3);
	if(!shadow_checkcontext((u32)__shadow_pdp_table)){
		printf("\nHalting, reserved bits set in SHADOW paging structures!");
		HALT();
	}	
#else
	memset((void *)__shadow_pdp_table, 0, PAGE_SIZE_4K);

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
		u64 *gPDPTE, *gPDE, *gPTE;
		u64 *sPDPTE, *sPDE, *sPTE;

		printf("\n%s: pre-loading guest GDT, IDT and TR pages...");

		start_va = PAGE_ALIGN_4K (guest_GDTR_base);
		end_va = PAGE_ALIGN_4K( (guest_GDTR_base + guest_GDTR_limit) );
		printf("\n	GDT pages=0x%08x-0x%08x inclusive",	start_va, end_va); 

		for(va=start_va; va <= end_va; va+= PAGE_SIZE_4K){
			shadow_get_guestentry(va, shadow_guest_CR3, &gPDPTE, &gPDE, &gPTE);
			shadow_get_shadowentry(va, &sPDPTE, &sPDE, &sPTE);
			if(is_present_guest(gPDPTE, gPDE, gPTE)){
				printf("\n	Structures BEFORE:");
				sdbg_dumpentries(gPDPTE, gPDE, gPTE, sPDPTE, sPDE, sPTE);
				shadow_updateshadowentries(va, &sPDPTE, &sPDE, &sPTE,
						&gPDPTE, &gPDE, &gPTE);
				printf("\n	Structures AFTER:");
				sdbg_dumpentries(gPDPTE, gPDE, gPTE, sPDPTE, sPDE, sPTE);
			}else{
				printf("\n	GUEST NOT-PRESENT!");
			}
		}

		start_va = PAGE_ALIGN_4K (guest_IDTR_base);
		end_va = PAGE_ALIGN_4K( (guest_IDTR_base + guest_IDTR_limit) );
		printf("\n	IDT pages=0x%08x-0x%08x inclusive",	start_va, end_va); 

		for(va=start_va; va <= end_va; va+= PAGE_SIZE_4K){
			shadow_get_guestentry(va, shadow_guest_CR3, &gPDPTE, &gPDE, &gPTE);
			shadow_get_shadowentry(va, &sPDPTE, &sPDE, &sPTE);
			if(is_present_guest(gPDPTE, gPDE, gPTE)){
				printf("\n	Structures BEFORE:");
				sdbg_dumpentries(gPDPTE, gPDE, gPTE, sPDPTE, sPDE, sPTE);
				shadow_updateshadowentries(va, &sPDPTE, &sPDE, &sPTE,
						&gPDPTE, &gPDE, &gPTE);
				printf("\n	Structures AFTER:");
				sdbg_dumpentries(gPDPTE, gPDE, gPTE, sPDPTE, sPDE, sPTE);
			}else{
				printf("\n	GUEST NOT-PRESENT!");
			}
		}

		start_va = PAGE_ALIGN_4K(guest_TR_base);
		end_va = PAGE_ALIGN_4K( (guest_TR_base + guest_TR_limit) );
		printf("\n	TR pages=0x%08x-0x%08x inclusive",	start_va, end_va); 

		for(va=start_va; va <= end_va; va+= PAGE_SIZE_4K){
			shadow_get_guestentry(va, shadow_guest_CR3, &gPDPTE, &gPDE, &gPTE);
			shadow_get_shadowentry(va, &sPDPTE, &sPDE, &sPTE);
			if(is_present_guest(gPDPTE, gPDE, gPTE)){
				printf("\n	Structures BEFORE:");
				sdbg_dumpentries(gPDPTE, gPDE, gPTE, sPDPTE, sPDE, sPTE);
				shadow_updateshadowentries(va, &sPDPTE, &sPDE, &sPTE,
						&gPDPTE, &gPDE, &gPTE);
				printf("\n	Structures AFTER:");
				sdbg_dumpentries(gPDPTE, gPDE, gPTE, sPDPTE, sPDE, sPTE);
			}else{
				printf("\n	GUEST NOT-PRESENT!");
			}
		}
	
	}
	
	
#endif	
	//return our shadow pdp table address which will be the new CR3
	//for the guest
	return (u32)__shadow_pdp_table; 
#else

	//if(!shadow_checkcontext( (u32)pae_get_addr_from_32bit_cr3((u32)guest_CR3) ) ){
	//	printf("\nHalting, reserved bits set in GUEST paging structures!");
	//	HALT();
	//}	

	return guest_CR3;
	
#endif
}

