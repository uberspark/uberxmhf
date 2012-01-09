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
 *
 * Edited by Zongwei Zhou for EMHF/TrustVisor project
 *
 * EPT or NPT page table operations
 * guest page table operations
 */
#include <emhf.h> 

#include  "./include/scode.h"
#include <pages.h>

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

/* we store the permissions to use when executing the PAL in
 * unused bits of the pte's.
 */
static inline hpt_pme_t hpt_pme_setpalprot(hpt_type_t t, int lvl, hpt_pme_t pme, hpt_prot_t prot)
{
	return hpt_pme_setunused(t, lvl, pme, 2, 0, prot);
}
static inline hpt_prot_t hpt_pme_getpalprot(hpt_type_t t, int lvl, hpt_pme_t pme)
{
	return hpt_pme_getunused(t, lvl, pme, 2, 0);
}

/* ********************************* */
/* HPT related NPT operations */
/* ********************************* */

hpt_prot_t pal_prot_of_type(int type)
{
	switch(type) {
	case TV_PAL_SECTION_CODE:
		return HPT_PROTS_RX;
		break;
	case TV_PAL_SECTION_SHARED_CODE:
		return HPT_PROTS_RX;
		break;
	case TV_PAL_SECTION_DATA:
		return HPT_PROTS_RWX;
		break;
	case TV_PAL_SECTION_PARAM:
	case TV_PAL_SECTION_STACK:
		return HPT_PROTS_RW;
		break;
	case TV_PAL_SECTION_SHARED:
		return HPT_PROTS_RWX;
		break;
	case TV_PAL_SECTION_GUEST_PAGE_TABLES:
		return HPT_PROTS_RWX;
		break;
	}
	ASSERT(0); return 0; /* unreachable; appeases compiler */
}

hpt_prot_t reg_prot_of_type(int type)
{
	switch(type) {
	case TV_PAL_SECTION_CODE:
		return HPT_PROTS_NONE;
		break;
	case TV_PAL_SECTION_SHARED_CODE:
		return HPT_PROTS_RX;
		break;
	case TV_PAL_SECTION_DATA:
		return HPT_PROTS_NONE;
		break;
	case TV_PAL_SECTION_PARAM:
	case TV_PAL_SECTION_STACK:
		return HPT_PROTS_NONE;
		break;
	case TV_PAL_SECTION_SHARED:
		return HPT_PROTS_NONE;
		break;
	case TV_PAL_SECTION_GUEST_PAGE_TABLES:
		return HPT_PROTS_RWX;
		break;
	}
	ASSERT(0); return 0; /* unreachable; appeases compiler */
}

void hpt_insert_pal_pme(VCPU *vcpu, hpt_walk_ctx_t *walk_ctx, hpt_pm_t pal_pm, int top_lvl, gpa_t gpa)
{
	hpt_pme_t reg_pme, pal_pme;
	hpt_prot_t pal_prot;
	int type;
	hpt_pme_t *reg_pml1es = VCPU_get_pml1es(vcpu);
	u64 pfn = gpa >> PAGE_SHIFT_4K;

	dprintf(LOG_TRACE, "hpt_insert_pal_pme: gpa: %Lx\n", gpa);

	reg_pme = reg_pml1es[pfn];
	dprintf(LOG_TRACE, "hpt_insert_pal_pme: reg: %Lx\n", reg_pme);

	type = SCODE_PTE_TYPE_GET(gpa);
	pal_prot = pal_prot_of_type(type);
	
	pal_pme = reg_pme;
	pal_pme = hpt_pme_setprot(walk_ctx->t, 1, pal_pme, pal_prot);
	ASSERT(!(hpt_walk_insert_pme_alloc(walk_ctx,
																		 top_lvl,
																		 pal_pm,
																		 1,
																		 gpa,
																		 pal_pme)));
	dprintf(LOG_TRACE, "hpt_insert_pal_pme: pal: %Lx\n", pal_pme);
}

void hpt_insert_pal_pmes(VCPU *vcpu,
												 hpt_walk_ctx_t *walk_ctx,
												 hpt_pm_t pal_pm,
												 int pal_pm_lvl,
												 gpa_t gpas[],
												 size_t num_gpas)
{
	unsigned i;
	for(i=0; i<num_gpas; i++) {
		hpt_insert_pal_pme(vcpu, walk_ctx, pal_pm, pal_pm_lvl, gpas[i]);
	}
}

/* **************************************
 * set up scode pages permission in EPT
 *
 * on all CPUs:
 * Section type		Real Permission  PTE permission
 * SENTRY(SCODE) 	RE					unpresent
 * STEXT			RE					RE
 * SDATA 			RW					unpresent
 * SPARAM			RW					unpresent
 * SSTACK			RW					unpresent
 *
 * **************************************/
void hpt_nested_set_prot(VCPU * vcpu, gpa_t gpaddr)
{
	u64 *pt = VCPU_get_pml1es(vcpu);
	u64 pfn = gpaddr >> PAGE_SHIFT_4K;
	u64 oldentry = pt[pfn];
	hpt_prot_t pal_prot, reg_prot;
	int type;

	type = SCODE_PTE_TYPE_GET(gpaddr);

	pal_prot = pal_prot_of_type(type);
	pt[pfn] = hpt_pme_setpalprot(hpt_nested_walk_ctx.t, 1, pt[pfn], pal_prot);

	reg_prot = reg_prot_of_type(type);
	pt[pfn] = hpt_pme_setprot(hpt_nested_walk_ctx.t, 1, pt[pfn], reg_prot);

	dprintf(LOG_TRACE, "[TV]   set prot: pfn %#llx, pte old %#llx, pte new %#llx\n", pfn, oldentry, pt[pfn]);

	/* flush TLB */
	emhf_hwpgtbl_flushall(vcpu);
}

void hpt_nested_clear_prot(VCPU * vcpu, gpa_t gpaddr)
{	
	u64 *pt = VCPU_get_pml1es(vcpu);
	u64 pfn = gpaddr >> PAGE_SHIFT_4K;
	u64 oldentry = pt[pfn];
	pt[pfn] = hpt_pme_setpalprot(hpt_nested_walk_ctx.t, 1, pt[pfn], HPT_PROTS_NONE);
	pt[pfn] = hpt_pme_setprot(hpt_nested_walk_ctx.t, 1, pt[pfn], HPT_PROTS_RWX);
	dprintf(LOG_TRACE, "[TV]   clear prot: pfn %#llx, pte old %#llx, pte new %#llx\n", pfn, oldentry, pt[pfn]);

	/* flush TLB */
	emhf_hwpgtbl_flushall(vcpu);
}

/* The following functions deal with guest space access. It doesn't need 
 * any specific nested paging support, just putting in this file for convenience
 */

/* guest page table opeations (VMX and SVM) */

/* guest page table walker. 
 * argument: vaddr - virtual address that needs to be translated
 * function returns:
 * 	- paddr of the vaddr. note the paddr should not be bigger than 32 bits in current 
 * paramter returns:
* 	- could return pointers of pdp page, pd page, and pt page of vaddr
* 	- or return pointers of pdp entry, pd entry and pt entry of vaddr
* 	- or return is_pae (is PAE mode or not)
* 	- put a valid pointer as input if you want to get the above return value, or put a NULL to disable the return value
 */

u32 guest_pt_walker_internal(VCPU *vcpu, u32 vaddr, u64 *pdp, u64 *pd, u64 *pt, u64 * pdpe, u64 * pde, u64 * pte, u32 * pae) 
{
	u32 pd_index, pt_index, offset;
	u64 paddr;

	const u32 is_pae = VCPU_gcr4(vcpu) & CR4_PAE;
	const u64 gcr3 = VCPU_gcr3(vcpu);

	/* intialize PT page phys addr to -1 */
	if (pdp) *pdp = 0xFFFFFFFF;
	if (pd)	*pd = 0xFFFFFFFF;
	if (pt)	*pt = 0xFFFFFFFF;

	/* intialize PT entry phys addr to -1 */
	if (pdpe) 	*pdpe = 0xFFFFFFFF;
	if (pde)	*pde = 0xFFFFFFFF;
	if (pte)	*pte = 0xFFFFFFFF;

	/* return is_pae if needed */
	if (pae) *pae = is_pae;

	/* we need to know whether the Linux kernel enable PAE or not, 
	 * because there are different page table processing for PAE 
	 * mode or non-PAE mode 
	 */
	if (is_pae)
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
		gpdp = (pdpt_t)gpa2hva((u32)tmp); 
		pdp_entry = gpdp[pdp_index];
		if (pdpe) *pdpe = pdp_entry;

		tmp = pae_get_addr_from_pdpe(pdp_entry);
		if (pd) *pd = tmp;
		gpd = (pdt_t)gpa2hva((u32)tmp);
		pd_entry = gpd[pd_index]; 
		if (pde) *pde = pd_entry;

		// if its 0, that means its 4 KB page
		// else, its 2MB pages 
		if ( (pd_entry & _PAGE_PSE) == 0 ) {
			/* get addr of page table from entry */
			tmp = pae_get_addr_from_pde(pd_entry);
			if (pt) *pt = tmp;
			gpt = (pt_t)gpa2hva((u32)tmp);  
			pt_entry  = gpt[pt_index];
			if (pte) *pte = pt_entry;
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
		gpd = (npdt_t)gpa2hva((u32)tmp); 

		/* find entry from kernel page dir */
		pd_entry = gpd[pd_index];
		if (pde) *pde = pd_entry;

		// if its 0, that means its 4 KB page
		// else, its 4MB pages 
		if ( (pd_entry & _PAGE_PSE) == 0 ) {
			/* get addr of page table from entry */
			tmp = (u32)npae_get_addr_from_pde(pd_entry);
			/* to be compitable with the code for PAE mode */
			if (pd) *pd = tmp;
			gpt = (npt_t)gpa2hva((u32)tmp);  
			pt_entry  = gpt[pt_index];
			if (pte) *pte = pt_entry;
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
int guest_pt_copy(VCPU *vcpu, pte_t *dst_page, u32 gvaddr, u32 size, int type) 
{	
	u32 vend = gvaddr+size;
	pdte_t pde;
	pte_t pte;
	u32 i;
	u32 paddr;
	u32 is_pae;

	if (!PAGE_ALIGNED_4K(gvaddr) || !PAGE_ALIGNED_4K(size)) {
		dprintf(LOG_ERROR, "[TV] guest_pt_copy given unaligned address %x or size %x\n",
					 gvaddr, size);
		return -1;
	}

	for(i=0; gvaddr < vend; gvaddr+=PAGE_SIZE_4K, i++) {
		gpt_get_ptentries(vcpu,
											gvaddr,
											NULL, &pde, &pte, &is_pae);

		if (pde & _PAGE_PSE) {
			dprintf(LOG_ERROR, "[TV] guest_pt_copy: ERROR currently we don't support "
						 "big page for sensitive code because of the limitation "
						 "of pte_page\n");
			return -2;
		}
		if (!(pte & _PAGE_PRESENT)) {
			dprintf(LOG_ERROR, "[TV] guest_pt_copy: ERROR "
						 "Page at %x not present in guest page table\n", gvaddr);
			return -1;
		}
		paddr = (is_pae)
			? pae_get_addr_from_pte(pte)
			: npae_get_addr_from_pte(pte);

		/* store section type */
		paddr = SCODE_PTE_TYPE_SET(paddr, type);
		dst_page[i] = paddr;
		dprintf(LOG_TRACE, "[TV] copied pte: gvaddr 0x%x, vend 0x%x, index %d, paddr %#x\n",
					 gvaddr, vend, i, paddr);
	}
	return 0;
}

/* check all pages in given range can be read/written by user level privilege */
/* see Intel System Programming Guide, Volume 3, 5-42 "combined Page-Directory and Page-Table Protection"  */
u32 guest_pt_check_user_rw(VCPU * vcpu, u32 vaddr, u32 page_num)
{
	u32 i, addr;
	u64 pde, pte;
	for( i=0 ; i<page_num ; i++ )  {
		addr = vaddr+(i<<PAGE_SHIFT_4K);
		gpt_get_ptentries(vcpu,addr,NULL,&pde, &pte, NULL);
		if ((!(pde & _PAGE_USER)) || (!(pde & _PAGE_RW))) {
			return 1;
		}
		if (pte!=0xFFFFFFFF) {
			if ((!(pte & _PAGE_USER)) || (!(pte & _PAGE_RW))) {
				return 1;
			}
		}
	}
	return 0;
}

/* check all pages in given range can be accessed by user level privilege */
/* see Intel System Programming Guide, Volume 3, 5-42 "combined Page-Directory and Page-Table Protection"  */
u32 guest_pt_check_user(VCPU * vcpu, u32 vaddr, u32 page_num)
{
	u32 i, addr;
	u64 pde, pte;
	for( i=0 ; i<page_num ; i++ )  {
		addr = vaddr+(i<<PAGE_SHIFT_4K);
		gpt_get_ptentries(vcpu,addr,NULL,&pde, &pte, NULL);
		if (!(pde & _PAGE_USER)) {
			return 1;
		}
		if (pte!=0xFFFFFFFF) {
			if (!(pte & _PAGE_USER)) {
				return 1;
			}
		}
	}
	return 0;
}

/* several help functions to access guest address space */
extern u16 get_16bit_aligned_value_from_guest(const hpt_walk_ctx_t *ctx, const hpt_pmo_t *root, u32 gvaddr)
{
  u32 gpaddr;
  
  gpaddr = gpt_vaddr_to_paddr(ctx, root, gvaddr);
  return *((u16 *)gpa2hva(gpaddr));
}

extern u32 get_32bit_aligned_value_from_guest(const hpt_walk_ctx_t *ctx, const hpt_pmo_t *root, u32 gvaddr)
{
  u32 gpaddr;
  
  gpaddr = gpt_vaddr_to_paddr(ctx, root, gvaddr);
  return *((u32 *)gpa2hva(gpaddr));
}

extern void put_32bit_aligned_value_to_guest(const hpt_walk_ctx_t *ctx, const hpt_pmo_t *root, u32 gvaddr, u32 value)
{
  u32 gpaddr;
  
  gpaddr = gpt_vaddr_to_paddr(ctx, root, gvaddr);
  *((u32 *)gpa2hva(gpaddr)) = value;
}

/* several help functions to access guest address space */
extern u16 get_16bit_aligned_value_from_current_guest(VCPU *vcpu, u32 gvaddr)
{
  u32 gpaddr;
  
  gpaddr = gpt_vaddr_to_paddr_current(vcpu, gvaddr);
  return *((u16 *)gpa2hva(gpaddr));
}

extern u32 get_32bit_aligned_value_from_current_guest(VCPU *vcpu, u32 gvaddr)
{
  u32 gpaddr;
  
  gpaddr = gpt_vaddr_to_paddr_current(vcpu, gvaddr);
  return *((u32 *)gpa2hva(gpaddr));
}

extern void put_32bit_aligned_value_to_current_guest(VCPU *vcpu, u32 gvaddr, u32 value)
{
  u32 gpaddr;
  
  gpaddr = gpt_vaddr_to_paddr_current(vcpu, gvaddr);
  *((u32 *)gpa2hva(gpaddr)) = value;
}



extern void copy_from_current_guest(VCPU * vcpu, u8 *dst,u32 gvaddr, u32 len)
{
	hpt_type_t t = (VCPU_gcr4(vcpu) & CR4_PAE) ? HPT_TYPE_PAE : HPT_TYPE_NORM;
	hpt_pmo_t root = {
		.pm = VCPU_get_current_guest_root_pm(vcpu),
		.t = t,
		.lvl = hpt_root_lvl(t),
	};
	hpt_walk_ctx_t ctx = hpt_guest_walk_ctx;
	ctx.t = t;

	hpt_copy_from_guest(&ctx, &root, dst, gvaddr, len);

  /* u32 gpaddr, gvend, gvprev; */
  /* u32 tmp; */

  /* gvprev = gvaddr; */
  /* gvend = gvaddr + len; */

  /* gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr); */

  /* if (gvaddr & 0x3) */
  /* { */
  /*   tmp = (gvaddr + 0x3) & (u32)~0x3; */
  /*   for (; (gvaddr < gvend) && (gvaddr < tmp); gvaddr ++, gpaddr ++, dst ++) */
  /*   { */
  /*     if (!SAME_PAGE_NPAE(gvprev, gvaddr)) */
  /*       gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr); */

  /*     *dst = *((u8 *)gpa2hva(gpaddr)); */
  /*     gvprev = gvaddr; */
  /*   } */
  /* } */
  /* if (gvaddr < gvend) */
  /* { */
  /*   tmp = gvend & (u32)~0x3; */
  /*   for (; gvaddr < tmp; gvaddr += 4, gpaddr += 4, dst += 4) */
  /*   { */
  /*     if (!SAME_PAGE_NPAE(gvprev, gvaddr)) */
  /*       gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr); */

  /*     *(u32 *)dst = *((u32 *)gpa2hva(gpaddr)); */
  /*     gvprev = gvaddr; */
  /*   } */
  /* } */
  /* if (gvaddr < gvend) */
  /* { */
  /*   for (; gvaddr < gvend; gvaddr ++, gpaddr ++, dst ++) */
  /*   { */
  /*     if (!SAME_PAGE_NPAE(gvprev, gvaddr)) */
  /*       gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr); */

  /*     *dst = *((u8 *)gpa2hva(gpaddr)); */
  /*     gvprev = gvaddr; */
  /*   } */
  /* } */
  /* return; */
}

extern void copy_to_current_guest(VCPU * vcpu, u32 gvaddr, u8 *src, u32 len)
{
	hpt_type_t t = (VCPU_gcr4(vcpu) & CR4_PAE) ? HPT_TYPE_PAE : HPT_TYPE_NORM;
	hpt_pmo_t root = {
		.pm = VCPU_get_current_guest_root_pm(vcpu),
		.t = t,
		.lvl = hpt_root_lvl(t),
	};
	hpt_walk_ctx_t ctx = hpt_guest_walk_ctx;
	ctx.t = t;

	hpt_copy_to_guest(&ctx, &root, gvaddr, src, len);

  /* u32 gpaddr, gvend, gvprev; */
  /* u32 tmp; */

  /* gvprev = gvaddr; */
  /* gvend = gvaddr + len; */

  /* gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr); */

  /* if (gvaddr & 0x3) */
  /* { */
  /*   tmp = (gvaddr + 0x3) & (u32)~0x3; */
  /*   for (; (gvaddr < gvend) && (gvaddr < tmp); gvaddr ++, gpaddr ++, src ++) */
  /*   { */
  /*     if (!SAME_PAGE_NPAE(gvprev, gvaddr)) */
  /*       gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr); */

  /*     *((u8 *)gpa2hva(gpaddr)) = *src; */
  /*     gvprev = gvaddr; */
  /*   } */
  /* } */
  /* if (gvaddr < gvend) */
  /* { */
  /*   tmp = gvend & (u32)~0x3; */
  /*   for (; gvaddr < tmp; gvaddr += 4, gpaddr += 4, src += 4) */
  /*   { */
  /*     if (!SAME_PAGE_NPAE(gvprev, gvaddr)) */
  /*       gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr); */

  /*     *((u32 *)gpa2hva(gpaddr)) = *(u32 *)src; */
  /*     gvprev = gvaddr; */
  /*   } */
  /* } */
  /* if (gvaddr < gvend) */
  /* { */
  /*   for (; gvaddr < gvend; gvaddr ++, gpaddr ++, src ++) */
  /*   { */
  /*     if (!SAME_PAGE_NPAE(gvprev, gvaddr)) */
  /*       gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr); */

  /*     *((u8 *)gpa2hva(gpaddr)) = *src; */
  /*     gvprev = gvaddr; */
  /*   } */
  /* } */
  /* return; */
}


/* clone pal's gdt from 'reg' gdt, and add to pal's guest page tables.
	 gdt is allocted using passed-in-pl, whose pages should already be
	 accessible to pal's nested page tables. XXX SECURITY need to build
	 a trusted gdt instead. */
void scode_clone_gdt(gva_t gdtr_base, size_t gdtr_lim,
										 hpt_pmo_t* reg_gpmo_root, hpt_walk_ctx_t *reg_gpm_ctx,
										 hpt_pmo_t* pal_gpmo_root, hpt_walk_ctx_t *pal_gpm_ctx,
										 pagelist_t *pl
										 )
{
	void *gdt_pal_page;
	u64 *gdt=NULL;
	size_t gdt_size = (gdtr_lim+1)*sizeof(*gdt);
	size_t gdt_page_offset = gdtr_base & MASKRANGE64(11, 0); /* XXX */
	gva_t gdt_reg_page_gva = gdtr_base & MASKRANGE64(63, 12); /* XXX */

	dprintf(LOG_TRACE, "scode_clone_gdt base:%x size:%d:\n", gdtr_base, gdt_size);

	/* rest of fn assumes gdt is all on one page */
	ASSERT((gdt_page_offset+gdt_size) <= PAGE_SIZE_4K); 

	gdt_pal_page = pagelist_get_zeroedpage(pl);
	CHK(gdt_pal_page);
	gdt = gdt_pal_page + gdt_page_offset;

	dprintf(LOG_TRACE, "copying gdt from gva:%x to hva:%p\n", gdtr_base, gdt);
	hpt_copy_from_guest(reg_gpm_ctx, reg_gpmo_root,
											gdt, gdtr_base, gdt_size);

	/* add to guest page tables */
	{
		hpt_pmeo_t gdt_g_pmeo = { .t = pal_gpmo_root->t, .lvl = 1 };
		hpt_pa_t gdt_gpa;
		int hpt_err;

		gdt_gpa = hva2gpa(gdt);

		dprintf(LOG_TRACE, "mapping gdt into guest page tables\n");
		/* XXX SECURITY check to ensure we're not clobbering some existing
			 mapping */
    /* add access to pal guest page tables */
		hpt_pmeo_set_address(&gdt_g_pmeo, gdt_gpa);
		hpt_pmeo_setprot(&gdt_g_pmeo, HPT_PROTS_RWX);
    hpt_err = hpt_walk_insert_pmeo_alloc(pal_gpm_ctx,
                                         pal_gpmo_root,
                                         &gdt_g_pmeo,
                                         gdt_reg_page_gva);
    CHK_RV(hpt_err);
	}
}

/* lend a section of memory from a user-space process (on the
   commodity OS) to a pal */
void scode_lend_section(hpt_pmo_t* reg_npmo_root, hpt_walk_ctx_t *reg_npm_ctx,
                        hpt_pmo_t* reg_gpmo_root, hpt_walk_ctx_t *reg_gpm_ctx,
                        hpt_pmo_t* pal_npmo_root, hpt_walk_ctx_t *pal_npm_ctx,
                        hpt_pmo_t* pal_gpmo_root, hpt_walk_ctx_t *pal_gpm_ctx,
                        const tv_pal_section_int_t *section)
{
  size_t offset;
  int hpt_err;

	dprintf(LOG_TRACE,
					"entering scode_lend_section. Mapping from %016llx to %016llx, size %u, pal_prot %u\n",
					section->reg_gva, section->pal_gva, section->size, (u32)section->pal_prot);
  
  /* XXX don't hard-code page size here. */
  /* XXX fail gracefully */
  ASSERT((section->size % PAGE_SIZE_4K) == 0); 

  for (offset=0; offset < section->size; offset += PAGE_SIZE_4K) {
    hpt_va_t page_reg_gva = section->reg_gva + offset;
    hpt_va_t page_pal_gva = section->pal_gva + offset;

    /* XXX we don't use hpt_va_t or hpt_pa_t for gpa's because these
       get used as both */
    u64 page_reg_gpa, page_pal_gpa; /* guest-physical-addresses */

    hpt_pmeo_t page_reg_gpmeo; /* reg's guest page-map-entry and lvl */
    hpt_pmeo_t page_pal_gpmeo; /* pal's guest page-map-entry and lvl */

    hpt_pmeo_t page_reg_npmeo; /* reg's nested page-map-entry and lvl */
    hpt_pmeo_t page_pal_npmeo; /* pal's nested page-map-entry and lvl */

    /* lock? quiesce? */

    hpt_walk_get_pmeo(&page_reg_gpmeo,
                      reg_gpm_ctx,
                      reg_gpmo_root,
                      1,
                      page_reg_gva);
		dprintf(LOG_TRACE,
						"got pme %016llx, level %d, type %d\n",
						page_reg_gpmeo.pme, page_reg_gpmeo.lvl, page_reg_gpmeo.t);
    ASSERT(page_reg_gpmeo.lvl==1); /* we don't handle large pages */
    page_reg_gpa = hpt_pmeo_get_address(&page_reg_gpmeo);

    hpt_walk_get_pmeo(&page_reg_npmeo,
                      reg_npm_ctx,
                      reg_npmo_root,
                      1,
                      page_reg_gpa);
    ASSERT(page_reg_npmeo.lvl==1); /* we don't handle large pages */

    /* no reason to go with a different mapping */
    page_pal_gpa = page_reg_gpa;

    /* check that this VM is allowed to access this system-physical mem */
    {
      hpt_prot_t effective_prots;
      bool user_accessible=false;
      effective_prots = hpto_walk_get_effective_prots(reg_npm_ctx,
                                                      reg_npmo_root,
                                                      page_reg_gpa,
                                                      &user_accessible);
      CHK((effective_prots & section->reg_prot) == section->reg_prot);
      CHK(user_accessible);
    }

    /* check that this guest process is allowed to access this guest-physical mem */
    {
      hpt_prot_t effective_prots;
      bool user_accessible=false;
      effective_prots = hpto_walk_get_effective_prots(reg_gpm_ctx,
                                                      reg_gpmo_root,
                                                      page_reg_gva,
                                                      &user_accessible);
			dprintf(LOG_TRACE, "%s got reg gpt prots:0x%x, user:%d\n",
							__FUNCTION__, (u32)effective_prots, (int)user_accessible);
      CHK((effective_prots & section->pal_prot) == section->pal_prot);
      CHK(user_accessible);
    }

    /* check that the requested virtual address isn't already mapped
       into PAL's address space */
    {
      hpt_pmeo_t existing_pmeo;
      hpt_walk_get_pmeo(&existing_pmeo,
                        pal_gpm_ctx,
                        pal_gpmo_root,
                        1,
                        page_pal_gva);
      CHK(!hpt_pmeo_is_present(&existing_pmeo));
    }

    /* revoke access from 'reg' VM */
    hpt_pmeo_setprot(&page_reg_npmeo, section->pal_prot);
    hpt_err = hpt_walk_insert_pmeo(reg_npm_ctx,
                                   reg_npmo_root,
                                   &page_reg_npmeo,
                                   page_reg_gpa);
    CHK_RV(hpt_err);

    /* for simplicity, we don't bother removing from guest page
       tables. removing from nested page tables is sufficient */

    /* add access to pal guest page tables */
    page_pal_gpmeo = page_reg_gpmeo; /* XXX SECURITY should build from scratch */
    hpt_pmeo_set_address(&page_pal_gpmeo, page_pal_gpa);
    hpt_pmeo_setprot    (&page_pal_gpmeo, HPT_PROTS_RWX);
    hpt_err = hpt_walk_insert_pmeo_alloc(pal_gpm_ctx,
                                         pal_gpmo_root,
                                         &page_pal_gpmeo,
                                         page_pal_gva);
    CHK_RV(hpt_err);

    /* add access to pal nested page tables */
    page_pal_npmeo = page_reg_npmeo;
    hpt_pmeo_setprot(&page_pal_npmeo, section->pal_prot);
    hpt_err = hpt_walk_insert_pmeo_alloc(pal_npm_ctx,
                                         pal_npmo_root,
                                         &page_pal_npmeo,
                                         page_pal_gpa);
    CHK_RV(hpt_err);

    /* unlock? unquiesce? */
  }
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */
