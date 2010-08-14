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

/* nested_pt.c routines for handling nested page tables
 * Written for TrustVisor by Arvind Seshadri and Ning Qu
 */

#include <types.h>
#include <error.h>
#include <print.h>
#include <visor.h>
#include <paging.h>
#include <heap.h>
#include <svm.h>
#include <sha1.h>
#include <prot.h>
#include <processor.h>
#include <string.h>
#include <scode.h>
#include <msr.h>
#include <io.h>
#include <pci.h>
#include <dev.h>

pdpt_t nested_pdptp; /* pointer to the pdpt of the guest npt */
extern u32 nested_pdp_table[];
extern u32 nested_pd_table[];
extern u32 nested_pt_table[];

void init_nested_paging(void) __attribute__ ((section ("_init_text")));
void activate_nested_paging(void) __attribute__ ((section ("_init_text")));

/* set up initial nested page tables. we need 4K pages only for the
 * memory regions occupied by the main kernel. all other memory can be
 * mapped as 2M pages. from AMD manual vol.2, "when an address is
 * mapped by guest and host page table entries with different page
 * sizes, the TLB entry that is created matches the size of the
 * smaller page". all address between 0 and 4GB but those between
 * visor_relocate_address and visor_relocate_address +
 * VISOR_RUNTIME_SIZE are unity mapped. the region between
 * visor_relocate_address and visor_relocate_address +
 * VISOR_RUNTIME_SIZE is marked "not present".
 */

/* FIXME: In this implementation I am only mapping guest physical
 * addresses upto 4GB. Since SimNow only has 256MB of RAM, it seems
 * unlikely that any MMIO region will get mapped above 4GB. Also,
 * most leagacy devices only have 32 address lines. To Leendert, is
 * it safe to always map only 4GB of guest physical address space?
 */

#if 0
void init_nested_paging(void)
{
	u32 pdt_array[4]; /* addresses of the 4 pdt */
	u64 flags, entry;
	u32 i, j, addr, tmp, x;
	pdt_t pdt;

	/* allocate pages for the for the user and kernel pdts */
	for(i = 0; i < PAE_PTRS_PER_PDPT; i++){
		pdt_array[i] = (u32)nested_pd_table + PAGE_SIZE_4K * i;
	}

	/* initalize the pdpt */
	nested_pdptp = (pdpt_t)nested_pdp_table;
	flags = (u64)(_PAGE_PRESENT);
	for(i = 0; i < PAE_PTRS_PER_PDPT; i++){
		x = __pa(pdt_array[i]);
		nested_pdptp[i] = pae_make_pdpe((u64)x, flags);
	}

	/* initialize the 4 pdts */
	flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER | _PAGE_ACCESSED 
			| _PAGE_DIRTY | _PAGE_PSE);
	for(i = 0, addr = 0; i < PAE_PTRS_PER_PDPT; i ++){
		pdt = (pdt_t)pdt_array[i];
		for(j = 0; j < PAE_PTRS_PER_PDT; j ++, addr += PAGE_SIZE_2M)
		{
			pdt[j] = pae_make_pde_big((u64)addr, flags);
		}
	}

	/* mark the physical pages of TrustVisor not_present. ASSUMPTION:
	 * size of TrustVisor memory region <= 1GB. Also,
	 * visor_relocate_address is located so that the addresses of
	 * TrustVisor will be covered by one page directory.
	 */
	j = (u32)pae_get_pdpt_index(visor_relocate_address);
	entry = nested_pdptp[j];
	tmp = (u32)pae_get_addr_from_pdpe(entry);
	tmp = __va(tmp);
	pdt = (pdt_t)tmp;
	j = (u32)pae_get_pdt_index(visor_relocate_address + (u32)VISOR_RUNTIME_SIZE);
	for(i = pae_get_pdt_index(visor_relocate_address); i < j; i ++){
		pdt[i] = 0;
	}
}
#else
void init_nested_paging(void)
{
	u32 pdt_array[4]; /* addresses of the 4 pdt */
	u64 flags, entry;
	u32 i, j, k, addr, tmp, x;
	pdt_t pdt;
	pt_t pt;

	/* allocate pages for the for the user and kernel pdts */
	DEBUG printf("DEBUG: nested_pd_table is %#x\n", (u32)nested_pd_table);
	for(i = 0; i < PAE_PTRS_PER_PDPT; i++){
		pdt_array[i] = (u32)nested_pd_table + PAGE_SIZE_4K * i;
	}

	/* initalize the pdpt */
	nested_pdptp = (pdpt_t)nested_pdp_table;
	flags = (u64)(_PAGE_PRESENT);
	for(i = 0; i < PAE_PTRS_PER_PDPT; i++){
		x = __pa(pdt_array[i]);
		nested_pdptp[i] = pae_make_pdpe((u64)x, flags);
	}

	/* initialize the 4 pdts */
	flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER | _PAGE_ACCESSED 
			| _PAGE_DIRTY);
	for(i = 0, addr = 0; i < PAE_PTRS_PER_PDPT; i ++){
		pdt = (pdt_t)((u32)nested_pd_table + (i << PAGE_SHIFT_4K));
		for(j = 0; j < PAE_PTRS_PER_PDT; j ++, addr += PAGE_SIZE_2M)
		{
			pt = (pt_t)((u32)nested_pt_table + ((i * PAE_PTRS_PER_PDT + j) << (PAGE_SHIFT_4K))); 

			tmp = __pa((u32)pt);
			pdt[j] = pae_make_pde((u64)tmp, flags); 

			tmp = addr;
			for (k = 0; k < PAE_PTRS_PER_PT; k ++, tmp += PAGE_SIZE_4K)
				pt[k] = pae_make_pte((u64)tmp, flags);
		}
	}

	/* mark the physical pages of TrustVisor not_present. ASSUMPTION:
	 * size of TrustVisor memory region <= 1GB. Also,
	 * visor_relocate_address is located so that the addresses of
	 * TrustVisor will be covered by one page directory.
	 */
	j = (u32)pae_get_pdpt_index(visor_relocate_address);
	entry = nested_pdptp[j];
	tmp = (u32)pae_get_addr_from_pdpe(entry);
	tmp = __va(tmp);
	pdt = (pdt_t)tmp;
	j = (u32)pae_get_pdt_index(visor_relocate_address + (u32)VISOR_RUNTIME_SIZE);
	for(i = pae_get_pdt_index(visor_relocate_address); i < j; i ++){
		pdt[i] = 0;
	}
}
#endif

/* setup kernel and user nested page table, and active kernel nested
 * page table 
 */
void activate_nested_paging(void)
{
	/* turn on nested paging */
	linux_vmcb->h_cr3 = __pa((u32)nested_pdptp);
	DEBUG printf("DEBUG: Host CR3 after NPT activation is %#llx\n", linux_vmcb->h_cr3);
	linux_vmcb->np_enable |= (1ULL << NP_ENABLE);

	linux_vmcb->guest_asid = ASID_GUEST;

	TLB_FLUSH_ALL();
}

/* function to break a big page into small pages in nested page table
*/
void nested_breakpde(u32 nvaddr)
{
	pdt_t npd;
	pt_t npt;
	u64 pd_entry;
	u32 pdp_index, pd_index, pt_index;
	u64 flags;
	u32 i, tmp;

	/* get fields from virtual addr */
	pdp_index = pae_get_pdpt_index(nvaddr);
	pd_index = pae_get_pdt_index(nvaddr);
	pt_index = pae_get_pt_index(nvaddr);

	npd = (pdt_t)((u32)nested_pd_table + (pdp_index << PAGE_SHIFT_4K));
	pd_entry = npd[pd_index]; 

	if (pd_entry & _PAGE_PSE)
	{
		npt = (pt_t)((u32)nested_pt_table + ((pdp_index * PAE_PTRS_PER_PDT + pd_index) << (PAGE_SHIFT_4K))); 
		memset(npt, 0, PAGE_SIZE_4K);

		tmp = __pa((u32)npt);
		flags = pae_get_flags_from_pde(pd_entry); 
		flags &= ~_PAGE_PSE;
		npd[pd_index] = pae_make_pde((u64)tmp, flags); 

		tmp = pae_get_addr_from_pde_big(pd_entry); 
		for (i = 0; i < PAE_PTRS_PER_PT; i ++, tmp += PAGE_SIZE_4K)
			npt[i] = pae_make_pte((u64)tmp, flags);
	}

	return;
}

void nested_set_prot(u32 pfn, int type)
{
	pdt_t npd; 
	pt_t npt; 
	u32 pdp_index, pd_index, pt_index;
	u64 pdp_entry, pd_entry, pt_entry;
	u64 tmp;
	u32 nvaddr = pfn << PAGE_SHIFT_4K;

	/* get fields from virtual addr */
	pdp_index = pae_get_pdpt_index(nvaddr);
	pd_index = pae_get_pdt_index(nvaddr);
	pt_index = pae_get_pt_index(nvaddr);

	//tmp is phy addr of page dir
	pdp_entry = nested_pdptp[pdp_index];

	DEBUG printf("DEBUG: nested_pdptp is %#x\n", (u32)nested_pdptp);

	tmp = pae_get_addr_from_pdpe(pdp_entry);
	npd = (pdt_t)(u32)(u64)__va((u32)tmp);
	pd_entry = npd[pd_index]; 

	DEBUG printf("DEBUG: npd %#x, pde old %#x, %#llx\n", (u32)npd, (u32)(npd + pd_index),  pd_entry);

	if (pd_entry & _PAGE_PSE) {
		/* break 2M large page into 4KB pages */
		DEBUG printf("DEBUG: break 2M page vaddr %#x\n", nvaddr);
		nested_breakpde(nvaddr);

		DEBUG printf("DEBUG: pde old %#llx, new %#llx\n", pd_entry, npd[pd_index]);
		/* fetch new page directory entry */
		pd_entry = npd[pd_index]; 
	}

	// now, we are dealing with 4KB page
	tmp = pae_get_addr_from_pde(pd_entry);
	npt = (pt_t)(u32)(u64)__va((u32)tmp);  
	pt_entry = npt[pt_index];

	/* ********************************************************************
	 * use NPT entry flag (unused1 bit and unused2 bit) to represent page type
	 * unused1 == 1 and unused2 == 0	registered other type of SCODE 
	 * unused1 == 1 and unused2 == 1	registered STEXT
	 * unused1 == 0 			regular code 
	 * *******************************************************************/
	pt_entry |= _PAGE_UNUSED1;
	if ( type == 2 ) {
		pt_entry |=  _PAGE_UNUSED2;
	} else {
		pt_entry &= ~_PAGE_UNUSED2;
	}

	/* use type to decide the R/W and U bit of nPTE */
	if( type != 0 ) {
		pt_entry &= ~_PAGE_RW;
	}
	if( type != 2 ) {
		pt_entry &= ~_PAGE_USER;
	} 


	DEBUG printf("DEBUG: pte old %#llx, new %#llx\n",npt[pt_index], pt_entry);
	npt[pt_index] = pt_entry;

	TLB_FLUSH_ALL();
}

void nested_clear_prot(u32 pfn)
{
	pdt_t npd; 
	pt_t npt; 
	u32 pdp_index, pd_index, pt_index;
	u64 pdp_entry, pd_entry, pt_entry;
	u64 tmp;
	u32 nvaddr = pfn << PAGE_SHIFT_4K;

	/* get fields from virtual addr */
	pdp_index = pae_get_pdpt_index(nvaddr);
	pd_index = pae_get_pdt_index(nvaddr);
	pt_index = pae_get_pt_index(nvaddr);

	// tmp is phy addr of page dir
	pdp_entry = nested_pdptp[pdp_index];

	tmp = pae_get_addr_from_pdpe(pdp_entry);
	npd = (pdt_t)(u32)(u64)__va((u32)tmp);
	pd_entry = npd[pd_index]; 

	DEBUG printf("DEBUG: pde old %#llx, new %#llx\n", pd_entry, npd[pd_index]);
	// if its 0, that means its 4 KB page
	// else, its 2MB pages 
	if ( (pd_entry & _PAGE_PSE) == 0 ) {
		/* get addr of page table from entry */
		tmp = pae_get_addr_from_pde(pd_entry);
		npt = (pt_t)(u32)(u64)__va((u32)tmp);  
		pt_entry = npt[pt_index];
		pt_entry |= _PAGE_USER;
		/* clear page flag (unused1 bit == 0) */ 
		pt_entry &= ~_PAGE_UNUSED1;
		pt_entry |= _PAGE_RW;
		DEBUG printf("DEBUG: pte old %#llx, new %#llx\n", npt[pt_index], pt_entry);
		npt[pt_index] = pt_entry;
		TLB_FLUSH_ALL();
	}
	else { /* 2MB page */
		printf("FATAL ERROR: should not clear protection on 2M large page, rip %#x, nvaddr %#x\n", 
				(u32)linux_vmcb->rip, nvaddr);
		FORCE_CRASH();
	}
}

void nested_promote(u32 pfn)
{
#if 1
	DEBUG printf("DEBUG: (Disabled) promote 2M page pfn %#x\n", pfn);
#else
	pdt_t npd; 
	pt_t npt; 
	u32 pdp_index, pd_index, pt_index;
	u64 pdp_entry, pd_entry, pt_entry;
	u64 tmp;
	u64 flags;
	u32 nvaddr = pfn << PAGE_SHIFT_4K;

	DEBUG printf("DEBUG: promote 2M page pfn %#x\n", pfn);
	/* get fields from virtual addr */
	pdp_index = pae_get_pdpt_index(nvaddr);
	pd_index = pae_get_pdt_index(nvaddr);
	pt_index = pae_get_pt_index(nvaddr);

	//tmp is phy addr of page dir
	pdp_entry = nested_pdptp[pdp_index];

	tmp = pae_get_addr_from_pdpe(pdp_entry);
	npd = (pdt_t)(u32)(u64)__va((u32)tmp);
	pd_entry = npd[pd_index]; 

	// if its 0, that means its 4 KB page
	// else, its 2MB pages 
	if ( (pd_entry & _PAGE_PSE) == 0 ) {
		/* get addr of page table from entry */
		tmp = pae_get_addr_from_pde(pd_entry);
		npt = (pt_t)(u32)(u64)__va((u32)tmp);  
		pt_entry = npt[pt_index];
		DEBUG printf("DEBUG: pte old %#x\n", (u32)pt_entry);

		/* get addr and flags of page table entry */
		flags = pae_get_flags_from_pte(pd_entry); 
		flags |= _PAGE_PSE;
		tmp = pae_get_addr_from_pte(pt_entry); 
		tmp = PAGE_ALIGN_2M(tmp);
		npd[pd_index] = pae_make_pde((u64)tmp, flags);

		DEBUG printf("DEBUG: pde old %#llx, new %#llx\n", pd_entry, npd[pd_index]);
		TLB_FLUSH_ALL();
	} else { /* 2MB page */
		printf("FATAL ERROR: should promote this range, already a 2M large page, rip %#x, nvaddr %#x\n", 
				(u32)linux_vmcb->rip, nvaddr);
		FORCE_CRASH();
	}
#endif
}

typedef struct gpaddr_struct {
	u64	     *gpaddr_list;
	u64        gpaddr_count;
} paddr_struct_t;

void nested_switch_scode(u32 pte_page, u32 size, u32 pte_page2, u32 size2)
{
	pdt_t npd; 
	pt_t npt; 
	u32 pdp_index, pd_index, pt_index;
	u64 pdp_entry, pd_entry, pt_entry;
	u64 tmp;
	u32 i, j, k;
	u32 nvaddr;
	paddr_struct_t gpaddrs[2];

	gpaddrs[0].gpaddr_list = (u64 *)pte_page;
	gpaddrs[0].gpaddr_count = size >> PAGE_SHIFT_4K;
	gpaddrs[1].gpaddr_list = (u64 *)pte_page2;
	gpaddrs[1].gpaddr_count = size2 >> PAGE_SHIFT_4K;

	DEBUG printf("DEBUG: nested_pd_table is %#x\n", (u32)nested_pd_table);
	for (i = 0; i < PAE_PTRS_PER_PDPT; i ++)
	{
		npd = (pdt_t)((u32)nested_pd_table + (i << PAGE_SHIFT_4K));
		for (j = 0; j < PAE_PTRS_PER_PDT; j ++)
		{
			pd_entry = npd[j]; 
			pd_entry &= ~_PAGE_USER; 
			npd[j] = pd_entry;
		}
	}

	DEBUG printf("DEBUG: nested_pdp is %#x\n", (u32)nested_pdptp);
	for (k = 0; k < 2; k ++)
	{
		for (i = 0; i < gpaddrs[k].gpaddr_count; i ++)
		{
			nvaddr = gpaddrs[k].gpaddr_list[i];

			/* get fields from virtual addr */
			pdp_index = pae_get_pdpt_index(nvaddr);
			pd_index = pae_get_pdt_index(nvaddr);
			pt_index = pae_get_pt_index(nvaddr);

			// tmp is phy addr of page dir
			pdp_entry = nested_pdptp[pdp_index];

			tmp = pae_get_addr_from_pdpe(pdp_entry);
			npd = (pdt_t)(u32)(u64)__va((u32)tmp);
			pd_entry = npd[pd_index]; 

			// now, we are dealing with 4KB page
			tmp = pae_get_addr_from_pde(pd_entry);
			npt = (pt_t)(u32)(u64)__va((u32)tmp);  

			if (!(pd_entry & _PAGE_USER)) {
				pd_entry |= _PAGE_USER;
				npd[pd_index] = pd_entry;

				for (j = 0; j < PAE_PTRS_PER_PT; j ++)
				{
					pt_entry = npt[j]; 
					pt_entry &= ~_PAGE_USER; 
					if (k > 0)
						pt_entry |= _PAGE_NX;
					npt[j] = pt_entry;
				}
			}

			pt_entry = npt[pt_index];
			pt_entry |= _PAGE_USER;
			npt[pt_index] = pt_entry;

		}
	}

	TLB_FLUSH_ALL();
}

void nested_switch_regular(u32 pte_page, u32 size, u32 pte_page2, u32 size2)
{
	pdt_t npd; 
	pt_t npt; 
	u32 pdp_index, pd_index, pt_index;
	u64 pdp_entry, pd_entry, pt_entry;
	u64 tmp;
	u32 i, j, k;
	u32 nvaddr;
	paddr_struct_t gpaddrs[2];

	gpaddrs[0].gpaddr_list = (u64 *)pte_page;
	gpaddrs[0].gpaddr_count = size >> PAGE_SHIFT_4K;
	gpaddrs[1].gpaddr_list = (u64 *)pte_page2;
	gpaddrs[1].gpaddr_count = size2 >> PAGE_SHIFT_4K;

	for (k = 0; k < 2; k ++)
	{
		for (i = 0; i < gpaddrs[k].gpaddr_count; i ++)
		{
			nvaddr = gpaddrs[k].gpaddr_list[i];

			/* get fields from virtual addr */
			pdp_index = pae_get_pdpt_index(nvaddr);
			pd_index = pae_get_pdt_index(nvaddr);
			pt_index = pae_get_pt_index(nvaddr);

			//tmp is phy addr of page dir
			pdp_entry = nested_pdptp[pdp_index];

			tmp = pae_get_addr_from_pdpe(pdp_entry);
			npd = (pdt_t)(u32)(u64)__va((u32)tmp);
			pd_entry = npd[pd_index]; 

			// now, we are dealing with 4KB page
			tmp = pae_get_addr_from_pde(pd_entry);
			npt = (pt_t)(u32)(u64)__va((u32)tmp);  

			if (pd_entry & _PAGE_USER) {
				pd_entry &= ~_PAGE_USER;
				npd[pd_index] = pd_entry;

				for (j = 0; j < PAE_PTRS_PER_PT; j ++){
					pt_entry = npt[j]; 
					/* Do not set the USER bit for SENTRY pages 
					 * that have been registered by other scode */
					if(!(pt_entry & _PAGE_UNUSED1))  {
						pt_entry |= _PAGE_USER; 
					}

					if( (pt_entry & _PAGE_UNUSED1) && ((pt_entry & _PAGE_UNUSED2)))  {
						pt_entry |= _PAGE_USER; 
					}

					if (k > 0)
						pt_entry &= ~_PAGE_NX;
					npt[j] = pt_entry;
				}
			}

			if( k == 0 )  {
				pt_entry = npt[pt_index];
				if(!(pt_entry & _PAGE_UNUSED2))  {
					pt_entry &= ~_PAGE_USER; 
				}
				npt[pt_index] = pt_entry;
			}
		}
	}

	for (i = 0; i < PAE_PTRS_PER_PDPT; i ++)
	{
		npd = (pdt_t)((u32)nested_pd_table + (i << PAGE_SHIFT_4K));
		for (j = 0; j < PAE_PTRS_PER_PDT; j ++)
		{
			pd_entry = npd[j]; 
			pd_entry |= _PAGE_USER; 
			npd[j] = pd_entry;
		}
	}

	TLB_FLUSH_ALL();
}

/* The following functions deal with guest space access. It doesn't need 
 * any specific nested paging support, just putting in this file for convenience
 */

/* guest page table walker. 
 * argument: vaddr - virtual address that needs to be translated
 * returns - paddr of the vaddr. note the paddr should not be bigger than 32 bits in current 
 */

u32 guest_pt_walker_internal(u64 gcr3, u32 vaddr, u64 *pdp, u64 *pd, u64 *pt) 
{
	u32 pd_index, pt_index, offset;
	u64 paddr;

	/* initial value 0 is incorrect !!!  --ZONGWEI JAN 13 2010 */
	//if (pdp)	*pdp = 0;
	//if (pd)	*pd = 0;
	//if (pt)	*pt = 0;

	if (pdp)	*pdp = 0xFFFFFFFF;
	if (pd)	*pd = 0xFFFFFFFF;
	if (pt)	*pt = 0xFFFFFFFF;
	/* we need to know whether the Linux kernel enable PAE or not, 
	 * because there are different page table processing for PAE 
	 * mode or non-PAE mode 
	 */
	if (linux_vmcb->cr4 & CR4_PAE)
	{ 
		pdpt_t gpdp; /* kernel page directory */
		pdt_t gpd; 
		pt_t gpt; 
		u32 pdp_index;
		u64 pdp_entry, pd_entry, pt_entry;
		u64 tmp;

		/* get fields from virtual addr */
		pdp_index = pae_get_pdpt_index(vaddr);
		pd_index = pae_get_pdt_index(vaddr);
		pt_index = pae_get_pt_index(vaddr);
		offset = pae_get_offset_4K_page(vaddr);  

		//tmp is phy addr of page dir
		tmp = pae_get_addr_from_32bit_cr3(gcr3);
		if (pdp) *pdp = tmp;
		gpdp = (pdpt_t)__gpa2hva((u32)tmp); 
		pdp_entry = gpdp[pdp_index];

		tmp = pae_get_addr_from_pdpe(pdp_entry);
		if (pd) *pd = tmp;
		gpd = (pdt_t)__gpa2hva((u32)tmp);
		pd_entry = gpd[pd_index]; 

		// if its 0, that means its 4 KB page
		// else, its 2MB pages 
		if ( (pd_entry & _PAGE_PSE) == 0 ) {
			/* get addr of page table from entry */
			tmp = pae_get_addr_from_pde(pd_entry);
			if (pt) *pt = tmp;
			gpt = (pt_t)__gpa2hva((u32)tmp);  
			pt_entry  = gpt[pt_index];
			/* find physical page base addr from page table entry */
			paddr = (u64)pae_get_addr_from_pte(pt_entry) + offset;
		}
		else { /* 2MB page */
			offset = pae_get_offset_big(vaddr);
			paddr = pae_get_addr_from_pde_big(pd_entry);
			paddr += (u64)offset;
		}
	}else
	{
		npdt_t gpd; /* kernel page directory */
		npt_t gpt; 
		u32 pd_entry, pt_entry;
		u32 tmp;

		/* get fields from virtual addr */
		pd_index = npae_get_pdt_index(vaddr);
		pt_index = npae_get_pt_index(vaddr);
		offset = npae_get_offset_4K_page(vaddr);  

		// tmp is phy addr of page dir
		tmp = npae_get_addr_from_32bit_cr3(gcr3);
		/* to be compitable with the code for PAE mode */
		if (pdp) *pdp = tmp;
		gpd = (npdt_t)__gpa2hva((u32)tmp); 

		/* find entry from kernel page dir */
		pd_entry = gpd[pd_index];

		// if its 0, that means its 4 KB page
		// else, its 4MB pages 
		if ( (pd_entry & _PAGE_PSE) == 0 ) {
			/* get addr of page table from entry */
			tmp = (u32)npae_get_addr_from_pde(pd_entry);
			/* to be compitable with the code for PAE mode */
			if (pd) *pd = tmp;
			gpt = (npt_t)__gpa2hva((u32)tmp);  
			pt_entry  = gpt[pt_index];
			/* find physical page base addr from page table entry */
			paddr = (u64)npae_get_addr_from_pte(pt_entry) + offset;
		}
		else { /* 4MB page */
			offset = npae_get_offset_big(vaddr);
			paddr = (u64)npae_get_addr_from_pde_big(pd_entry);
			paddr += (u64)offset;
		}
	}
	return (u32)paddr;
}

/* function to copy the content of a range of page table entry into 
 * a buffer, which can be used by sensitive code handler
 */
int guest_pt_copy(u32 pte_page, u64 gcr3, u32 gvaddr, u32 size, int type) 
{
	if (linux_vmcb->cr4 & CR4_PAE)
	{ 
		u32 pdp_index, pd_index, pt_index;
		pdpt_t gpdp; /* guest page directory */
		pdt_t gpd; 
		pt_t gpt; 
		u64 pdp_entry, pd_entry;
		pt_t dst_page = (pt_t)pte_page;
		u32 vcurr, vend = gvaddr + size;
		u32 paddr, index = 0;
		u64 tmp, i;

		/* get fields from virtual addr */
		pdp_index = pae_get_pdpt_index(gvaddr);

		while (gvaddr < vend)
		{
			vcurr = PAGE_ALIGN_2M(gvaddr + PAGE_SIZE_2M); 
			if (vcurr > vend)
				vcurr = vend;
			else if (vcurr < vend)
			{
				printf("DEBUG: gvaddr 0x%x, vcurr 0x%x, vend 0x%x\n", gvaddr, vcurr, vend);
				printf("WARNNING: sensitive code address is not in a single 2M page\n");
			}

			pd_index = pae_get_pdt_index(gvaddr);
			pt_index = pae_get_pt_index(gvaddr);

			tmp = pae_get_addr_from_32bit_cr3(gcr3);
			gpdp = (pdpt_t)__gpa2hva((u32)tmp); 
			pdp_entry = gpdp[pdp_index];

			tmp = pae_get_addr_from_pdpe(pdp_entry);
			gpd = (pdt_t)__gpa2hva((u32)tmp);
			pd_entry = gpd[pd_index]; 

			if ( (pd_entry & _PAGE_PSE) == 0 ) {
				/* get addr of page table from entry */
				paddr = pae_get_addr_from_pde(pd_entry);
				gpt = (pt_t)__gpa2hva(paddr);  
				for (i = 0; gvaddr < vcurr; i ++, gvaddr += PAGE_SIZE_4K, index ++)
				{
					if (!(gpt[pt_index + i] & _PAGE_PRESENT))
						return -1;
					paddr = pae_get_addr_from_pte(gpt[pt_index + i]);
					/* use bit 0 of paddr to indicate the type of scode pages
					 * if bit 0 == 1, this page is SENTRY page
					 * if bit 1 == 1, this page is SDATA page
					 * if bit 2 == 1, this page is STEXT page
					 * otherwise, this page is R/W page. */
					if( type == SECTION_TYPE_SCODE )  {
						paddr+=1;
					}
					if( type == SECTION_TYPE_SDATA )  {
						paddr+=2;
					}
					if( type == SECTION_TYPE_STEXT )  {
						paddr+=4;
					}
					dst_page[index] = (u64)paddr;
					DEBUG printf("DEBUG: gvaddr 0x%x, vcurr 0x%x, vend 0x%x, index %d, paddr %#x\n", gvaddr, vcurr, vend, index, paddr);
				}
			}
			else { /* 2MB page */
				printf("FATAL ERROR: currently we don't support big page for sensitive code because of the limitation of pte_page\n");
				FORCE_CRASH();
			}
		}
	}else
	{
		u32 pd_index, pt_index;
		npdt_t gpd; 
		npt_t gpt; 
		u64 pd_entry;
		pt_t dst_page = (pt_t)pte_page;
		u32 vcurr, vend = gvaddr + size;
		u32 paddr, index = 0;
		u64 tmp, i;

		/* get fields from virtual addr */
		pd_index = npae_get_pdt_index(gvaddr);

		while (gvaddr < vend)
		{
			vcurr = PAGE_ALIGN_4M(gvaddr + PAGE_SIZE_4M); 
			if (vcurr > vend)
				vcurr = vend;
			else if (vcurr < vend)
			{
				printf("DEBUG: gvaddr 0x%x, vcurr 0x%x, vend 0x%x\n", gvaddr, vcurr, vend);
				printf("WARNNING: sensitive code address is not in a single 2M page\n");
			}

			pt_index = npae_get_pt_index(gvaddr);

			tmp = npae_get_addr_from_32bit_cr3(gcr3);
			gpd = (npdt_t)__gpa2hva((u32)tmp);
			pd_entry = gpd[pd_index]; 

			if ( (pd_entry & _PAGE_PSE) == 0 ) {
				/* get addr of page table from entry */
				paddr = npae_get_addr_from_pde(pd_entry);
				gpt = (npt_t)__gpa2hva(paddr);  
				for (i = 0; gvaddr < vcurr; i ++, gvaddr += PAGE_SIZE_4K, index ++)
				{
					if (!(gpt[pt_index + i] & _PAGE_PRESENT))
						return -1;
					paddr = npae_get_addr_from_pte(gpt[pt_index + i]);
					/* use bit 0 of paddr to indicate the type of scode pages
					 * if bit 0 == 1, this page is SENTRY page
					 * if bit 1 == 1, this page is SDATA page
					 * if bit 2 == 1, this page is STEXT page
					 * otherwise, this page is R/W page. */
					if( type == SECTION_TYPE_SCODE )  {
						paddr+=1;
					}
					if( type == SECTION_TYPE_SDATA )  {
						paddr+=2;
					}
					if( type == SECTION_TYPE_STEXT )  {
						paddr+=4;
					}
					dst_page[index] = (u64)paddr;
				}
			}
			else { /* 4MB page */
				printf("FATAL ERROR: currently we don't support big page for sensitive code because of the limitation of pte_page\n");
				FORCE_CRASH();
			}
		}
	}
	return 0;
}
