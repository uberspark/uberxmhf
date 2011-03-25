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
#include <target.h>
#include  "./include/scode.h"

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

/* ********************************* */
/* VMX related NPT operations */
/* ********************************* */

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
void vmx_nested_set_prot(VCPU * vcpu, u64 gpaddr, int type)
{
	/* type is not used in vmx_nested_set_prot */

  	u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
	u64 pfn = gpaddr >> PAGE_SHIFT_4K;
	u64 oldentry = pt[pfn];

	if(gpaddr & 0x1)  {
		/* SENTRY pages */
		pt[pfn] =  (oldentry & ~(u64)0x707) | (u64)0x500; 
	} else if (gpaddr & 0x4) {
		/* STEXT pages */
		pt[pfn] =  (oldentry & ~(u64)0x707) | (u64)0x505; 
	} else {
		/* SDATA, SPARAM, SSTACK pages */
		pt[pfn] =  (oldentry & ~(u64)0x707) | (u64)0x300; 
	}
	printf("[TV]   set prot: pfn %#llx, pte old %#llx, pte new %#llx\n", pfn, oldentry, pt[pfn]);

	/* flush TLB */
	emhf_hwpgtbl_flushall(vcpu);
}

void vmx_nested_clear_prot(VCPU * vcpu, u64 gpaddr)
{	
  	u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
	u64 pfn = gpaddr >> PAGE_SHIFT_4K;
	u64 oldentry = pt[pfn];
	pt[pfn] =  (oldentry & ~(u64)0x707) | (u64)0x7; 
	printf("[TV]   clear prot: pfn %#llx, pte old %#llx, pte new %#llx\n", pfn, oldentry, pt[pfn]);

	/* flush TLB */
	emhf_hwpgtbl_flushall(vcpu);
}

void vmx_nested_make_pt_accessible(pte_t *gpaddr_list, u32 gpaddr_count, u64 * npdp, u32 is_pal)
{	
	pdt_t npd; 
	pt_t npt; 
	u32 pdp_index, pd_index, pt_index;
	u64 pdp_entry, pd_entry, pt_entry;
	u64 tmp;
	u32 nvaddr;

	u32 i, j;
	for (i = 0; i < gpaddr_count; i ++)
	{
		nvaddr = gpaddr_list[i];
		printf("[TV]   set npt prot for gpaddr %#x, ", nvaddr);

		/* get fields from virtual addr */
		pdp_index = pae_get_pdpt_index(nvaddr);
		pd_index = pae_get_pdt_index(nvaddr);
		pt_index = pae_get_pt_index(nvaddr);

		pdp_entry = npdp[pdp_index];
		tmp = pae_get_addr_from_pdpe(pdp_entry);
		npd = (pdt_t)(u32)(u64)__spa2hva__((u32)tmp);
		pd_entry = npd[pd_index]; 
//		printf("[TV]   pdp_entry %#llx, pd_entry %#llx!\n", pdp_entry, pd_entry);

		// now, we are dealing with 4KB page
		tmp = pae_get_addr_from_pde(pd_entry);
		npt = (pt_t)(u32)(u64)__spa2hva__((u32)tmp);  

		if (!(pd_entry & (u64)0x7)) {
			pd_entry |= (u64)0x7;
			npd[pd_index] = pd_entry;
			for (j = 0; j < PAE_PTRS_PER_PT; j ++)
			{
				pt_entry = npt[j]; 
				if (!(pt_entry & (u64)0x700)) {
					/* this entry hasn't been registered, set to unpresent */
					pt_entry &= ~(u64)0x7; 
					npt[j] = pt_entry;
				}
			}
		}

		pt_entry = npt[pt_index];
		if (is_pal) {
			/* scode mem region */
			pt_entry |= ((pt_entry & (u64)0x700) >> 8);
		} else {
			/* GDT, scode related PTE, r/w */
			pt_entry |= 0x3;
		}
		printf("pte old %#llx, new %#llx!\n", npt[pt_index], pt_entry);
		npt[pt_index] = pt_entry;
	}
}

void vmx_nested_switch_scode(VCPU * vcpu, pte_t* pte_pages, u32 size, u32 pte_page2, u32 size2)
{
	u64* npdp;
	u64* npd; 
	u64 pd_entry;
	u32 pd_base;
	u32 i, j;

	//printf("[TV] scode_page %#x, scode_size %#x!\n[TV] pte_page %#x, pte_size %#x!\n", pte_page, size, pte_page2, size2);

	/* get page table addresses from VCPU */
	npdp = (u64 *)(vcpu->vmx_vaddr_ept_pdp_table);
	pd_base = vcpu->vmx_vaddr_ept_pd_tables;

	//printf("[TV] pb_base is %#x!\n", (u32)pd_base);
	/* first make all pd_entry unaccessible */
	for (i = 0; i < PAE_PTRS_PER_PDPT; i ++)
	{
		npd = (u64 *)(pd_base + (i << PAGE_SHIFT_4K));
		for (j = 0; j < PAE_PTRS_PER_PDT; j ++)
		{
			pd_entry = npd[j]; 
			pd_entry &= ~(u64)0x7; 
			npd[j] = pd_entry;
		}
	}
	//printf("[TV] npdp is %#x!\n", (u32)npdp);

	/* make PAL and its related PTE pages accessbile */
	vmx_nested_make_pt_accessible(pte_pages, size >> PAGE_SHIFT_4K, npdp, 1); 
	vmx_nested_make_pt_accessible((pte_t*)pte_page2, size2 >> PAGE_SHIFT_4K, npdp, 0); 

	/* flush TLB */
	emhf_hwpgtbl_flushall(vcpu);
}

void vmx_nested_make_pt_unaccessible(pte_t *gpaddr_list, u32 gpaddr_count, pdpt_t npdp, u32 is_pal)
{	
	pdt_t npd; 
	pt_t npt; 
	u32 pdp_index, pd_index, pt_index;
	u64 pdp_entry, pd_entry, pt_entry;
	u64 tmp;
	u32 nvaddr;
	u32 i, j;

	for (i = 0; i < gpaddr_count; i ++)
	{
		nvaddr = gpaddr_list[i];
		printf("[TV]   set npt prot for gpaddr %#x, ", nvaddr);

		/* get fields from virtual addr */
		pdp_index = pae_get_pdpt_index(nvaddr);
		pd_index = pae_get_pdt_index(nvaddr);
		pt_index = pae_get_pt_index(nvaddr);

		pdp_entry = npdp[pdp_index];
		tmp = pae_get_addr_from_pdpe(pdp_entry);
		npd = (pdt_t)(u32)(u64)__spa2hva__((u32)tmp);
		pd_entry = npd[pd_index]; 

		// now, we are dealing with 4KB page
		tmp = pae_get_addr_from_pde(pd_entry);
		npt = (pt_t)(u32)(u64)__spa2hva__((u32)tmp);  

	//	printf("[TV]   pdp_entry %#llx, pd_entry %#llx!\n", pdp_entry, pd_entry);
		if (pd_entry & (u64)0x7) {
			pd_entry &= ~(u64)0x7;
			npd[pd_index] = pd_entry;

			for (j = 0; j < PAE_PTRS_PER_PT; j ++){
				pt_entry = npt[j]; 
				if (!(pt_entry & (u64)0x700)) {
					/* not registered entry, set to R/W/E */
					pt_entry |= (u64)0x7;
					npt[j] = pt_entry;
				}
			}
		}

		pt_entry = npt[pt_index];
		if( is_pal )  {
			/* scode mem region(except for STEXT sections), set to unpresent */
			if ((nvaddr & (u32)0x4) == 0)
				pt_entry &= ~(u64)0x7;
		} 
		printf("pte old %#llx, new %#llx!\n", npt[pt_index], pt_entry);
		npt[pt_index] = pt_entry;
	}
}

void vmx_nested_switch_regular(VCPU * vcpu, pte_t *pte_pages, u32 size, u32 pte_page2, u32 size2)
{
	pdpt_t npdp;
	pdt_t npd; 
	u64 pd_entry;
	u32 pd_base;
	u32 i, j;

//	printf("[TV] scode_page %#x, scode_size %#x, pte_page %#x, pte_size %#x!\n", pte_page, size, pte_page2, size2);

	/* get page table addresses from VCPU */
	npdp = (pdpt_t)(vcpu->vmx_vaddr_ept_pdp_table);
	pd_base = vcpu->vmx_vaddr_ept_pd_tables;

//	printf("[TV] npdp is %#x!\n", (u32)npdp);

	/* restore PAL protection (also don't compromise the protection of other PALs)*/
	vmx_nested_make_pt_unaccessible(pte_pages, size >> PAGE_SHIFT_4K, npdp, 1); 
	vmx_nested_make_pt_unaccessible((pte_t*)pte_page2, size2 >> PAGE_SHIFT_4K, npdp, 0); 

//	printf("[TV] pb_base is %#x!\n", (u32)pd_base);
	/* make all pd_entry accessible */
	for (i = 0; i < PAE_PTRS_PER_PDPT; i ++)
	{
		npd = (pdt_t)(pd_base + (i << PAGE_SHIFT_4K));
		for (j = 0; j < PAE_PTRS_PER_PDT; j ++)
		{
			pd_entry = npd[j]; 
			pd_entry |= 0x7; 
			npd[j] = pd_entry;
		}
	}

	/* flush TLB */
	emhf_hwpgtbl_flushall(vcpu);
}


/* ********************************* */
/* SVM related EPT operations */
/* ********************************* */

/* ************************************
 * set up scode pages permission (SVM)
 * R 	-- 	read-only
 * R/W	--	read, write
 * NU	--	guest system cannot access
 * U	--	guest system can access
 *
 * on local CPU:
 * Section type		Permission
 * SENTRY(SCODE) 	R NU
 * STEXT			R U
 * SDATA 			RW NU
 * SPARAM			RW NU
 * SSTACK			RW NU
 *
 * on other CPU:
 * all sections		unpresent
 * **************************************/

void svm_nested_set_prot(VCPU * vcpu, u64 gpaddr, int type)
{
	struct vmcb_struct * linux_vmcb;
  	u64 *pt = (u64 *)vcpu->npt_vaddr_pts;
	u64 pfn = gpaddr >> PAGE_SHIFT_4K;
	u64 oldentry = pt[pfn];

	/* ********************************************************************
	 * use NPT entry flag (unused1 bit and unused2 bit) to represent page type
	 * unused1 == 1 and unused2 == 0	registered other type of SCODE 
	 * unused1 == 1 and unused2 == 1	registered STEXT
	 * unused1 == 0 			regular code 
	 * *******************************************************************/
	if (type == 3) {
		pt[pfn] = oldentry & (~(u64)_PAGE_PRESENT);
	} else if ( type == 2 ) {
		pt[pfn] = (oldentry | (u64)_PAGE_UNUSED1 | (u64)_PAGE_UNUSED2) & (~(u64)_PAGE_RW);
	} else if (type == 1) {
		pt[pfn] = (oldentry | (u64)_PAGE_UNUSED1) & (~(u64)_PAGE_UNUSED2) & (~(u64)_PAGE_RW) & (~(u64)_PAGE_USER);
	} else if (type == 0) {
		pt[pfn] = (oldentry | (u64)_PAGE_UNUSED1) & (~(u64)_PAGE_UNUSED2) & (~(u64)_PAGE_USER);
	} else {
		printf("error in set_prot, unknown memory type!\n");
		HALT();
	}

	printf("[TV]   set prot: pfn %#llx, pte old %#llx, pte new %#llx\n",pfn, oldentry, pt[pfn]);

	/* flush TLB */
	linux_vmcb = (struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr);
	linux_vmcb->tlb_control=TLB_CONTROL_FLUSHALL;
}

void svm_nested_clear_prot(VCPU * vcpu, u64 gpaddr)
{
	struct vmcb_struct * linux_vmcb;
  	u64 *pt = (u64 *)vcpu->npt_vaddr_pts;
	u64 pfn = gpaddr >> PAGE_SHIFT_4K;
	u64 oldentry = pt[pfn];
	pt[pfn] = (oldentry | (u64)_PAGE_USER | (u64)_PAGE_RW | (u64)_PAGE_PRESENT) & (~(u64)_PAGE_UNUSED1);
	printf("[TV]   clear prot: pfn %#llx, pte old %#llx, pte new %#llx\n", pfn, oldentry, pt[pfn]);

	/* flush TLB */
	linux_vmcb = (struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr);
	linux_vmcb->tlb_control=TLB_CONTROL_FLUSHALL;
}

void svm_nested_make_pt_accessible(pte_t *gpaddr_list, u32 gpaddr_count, u64 * npdp, u32 is_nx)
{	
	pdt_t npd; 
	pt_t npt; 
	u32 pdp_index, pd_index, pt_index;
	u64 pdp_entry, pd_entry, pt_entry;
	u64 tmp;
	u32 nvaddr;

	u32 i, j;
	for (i = 0; i < gpaddr_count; i ++)
	{
		nvaddr = gpaddr_list[i];
		printf("[TV]   set npt prot for gpaddr %#x, ", nvaddr);

		/* get fields from virtual addr */
		pdp_index = pae_get_pdpt_index(nvaddr);
		pd_index = pae_get_pdt_index(nvaddr);
		pt_index = pae_get_pt_index(nvaddr);

		pdp_entry = npdp[pdp_index];
		tmp = pae_get_addr_from_pdpe(pdp_entry);
		npd = (pdt_t)(u32)(u64)__spa2hva__((u32)tmp);
		pd_entry = npd[pd_index]; 
//		printf("[TV]   pdp_entry %#llx, pd_entry %#llx!\n", pdp_entry, pd_entry);

		// now, we are dealing with 4KB page
		tmp = pae_get_addr_from_pde(pd_entry);
		npt = (pt_t)(u32)(u64)__spa2hva__((u32)tmp);  

		if (!(pd_entry & _PAGE_USER)) {
			pd_entry |= _PAGE_USER;
			npd[pd_index] = pd_entry;
			for (j = 0; j < PAE_PTRS_PER_PT; j ++)
			{
				pt_entry = npt[j]; 
				pt_entry &= ~_PAGE_USER; 
				npt[j] = pt_entry;
			}
		}

		pt_entry = npt[pt_index];
		pt_entry |= _PAGE_USER;
		if (is_nx)
			pt_entry |= _PAGE_NX;
		printf("pte old %#llx, new %#llx!\n", npt[pt_index], pt_entry);
		npt[pt_index] = pt_entry;
	}
}

void svm_nested_switch_scode(VCPU * vcpu, pte_t *pte_pages, u32 size, u32 pte_page2, u32 size2)
{
	pdpt_t npdp;
	pdt_t npd; 
	u64 pd_entry;
	u32 pd_base;
	struct vmcb_struct * linux_vmcb;
	u32 i, j;

	//printf("[TV] scode_page %#x, scode_size %#x!\n[TV] pte_page %#x, pte_size %#x!\n", pte_page, size, pte_page2, size2);

	/* get page table addresses from VCPU */
	npdp = (pdpt_t)(vcpu->npt_vaddr_ptr);
	pd_base = vcpu->npt_vaddr_pdts;

	//printf("[TV] pb_base is %#x!\n", (u32)pd_base);
	/* first make all pd_entry unaccessible */
	for (i = 0; i < PAE_PTRS_PER_PDPT; i ++)
	{
		npd = (pdt_t)(pd_base + (i << PAGE_SHIFT_4K));
		for (j = 0; j < PAE_PTRS_PER_PDT; j ++)
		{
			pd_entry = npd[j]; 
			pd_entry &= ~_PAGE_USER; 
			npd[j] = pd_entry;
		}
	}
	//printf("[TV] npdp is %#x!\n", (u32)npdp);

	/* make PAL and its related PTE pages accessbile */
	svm_nested_make_pt_accessible(pte_pages, size >> PAGE_SHIFT_4K, npdp, 0); 
	svm_nested_make_pt_accessible((pte_t*)pte_page2, size2 >> PAGE_SHIFT_4K, npdp, 1); 

	/* flush TLB */
	linux_vmcb = (struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr);
	linux_vmcb->tlb_control=TLB_CONTROL_FLUSHALL;
}

void svm_nested_make_pt_unaccessible(pte_t *gpaddr_list, u32 gpaddr_count, u64 * npdp, u32 is_nx)
{	
	pdt_t npd; 
	pt_t npt; 
	u32 pdp_index, pd_index, pt_index;
	u64 pdp_entry, pd_entry, pt_entry;
	u64 tmp;
	u32 nvaddr;
	u32 i, j;

	for (i = 0; i < gpaddr_count; i ++)
	{
		nvaddr = *(((u64 *)gpaddr_list)+i);
		printf("[TV]   set npt prot for gpaddr %#x, ", nvaddr);

		/* get fields from virtual addr */
		pdp_index = pae_get_pdpt_index(nvaddr);
		pd_index = pae_get_pdt_index(nvaddr);
		pt_index = pae_get_pt_index(nvaddr);

		pdp_entry = npdp[pdp_index];
		tmp = pae_get_addr_from_pdpe(pdp_entry);
		npd = (pdt_t)(u32)(u64)__spa2hva__((u32)tmp);
		pd_entry = npd[pd_index]; 

		// now, we are dealing with 4KB page
		tmp = pae_get_addr_from_pde(pd_entry);
		npt = (pt_t)(u32)(u64)__spa2hva__((u32)tmp);  

	//	printf("[TV]   pdp_entry %#llx, pd_entry %#llx!\n", pdp_entry, pd_entry);
		if (pd_entry & _PAGE_USER) {
			pd_entry &= ~_PAGE_USER;
			npd[pd_index] = pd_entry;

			for (j = 0; j < PAE_PTRS_PER_PT; j ++){
				pt_entry = npt[j]; 
				if(!(pt_entry & _PAGE_UNUSED1))  {
					pt_entry |= _PAGE_USER; 
				}
				if( (pt_entry & _PAGE_UNUSED1) && ((pt_entry & _PAGE_UNUSED2)))  {
					pt_entry |= _PAGE_USER; 
				}
				npt[j] = pt_entry;
			}
		}

		pt_entry = npt[pt_index];
		if( !is_nx )  {
			if((pt_entry & _PAGE_UNUSED1) && (!(pt_entry & _PAGE_UNUSED2)))  {
				pt_entry &= ~_PAGE_USER; 
			}
		} else {
			pt_entry &= ~_PAGE_NX;
		}
		printf("pte old %#llx, new %#llx!\n", npt[pt_index], pt_entry);
		npt[pt_index] = pt_entry;
	}
}

void svm_nested_switch_regular(VCPU * vcpu, pte_t* pte_pages, u32 size, u32 pte_page2, u32 size2)
{
	pdpt_t npdp;
	pdt_t npd; 
	u64 pd_entry;
	u32 pd_base;
	struct vmcb_struct * linux_vmcb;
	u32 i, j;

//	printf("[TV] scode_page %#x, scode_size %#x, pte_page %#x, pte_size %#x!\n", pte_page, size, pte_page2, size2);

	/* get page table addresses from VCPU */
	npdp = (pdpt_t)(vcpu->npt_vaddr_ptr);
	pd_base = vcpu->npt_vaddr_pdts;

//	printf("[TV] npdp is %#x!\n", (u32)npdp);

	/* restore PAL protection (also don't compromise the protection of other PALs)*/
	svm_nested_make_pt_unaccessible(pte_pages, size >> PAGE_SHIFT_4K, npdp, 0); 
	svm_nested_make_pt_unaccessible((pte_t*)pte_page2, size2 >> PAGE_SHIFT_4K, npdp, 1); 

//	printf("[TV] pb_base is %#x!\n", (u32)pd_base);
	/* make all pd_entry accessible */
	for (i = 0; i < PAE_PTRS_PER_PDPT; i ++)
	{
		npd = (pdt_t)(pd_base + (i << PAGE_SHIFT_4K));
		for (j = 0; j < PAE_PTRS_PER_PDT; j ++)
		{
			pd_entry = npd[j]; 
			pd_entry |= _PAGE_USER; 
			npd[j] = pd_entry;
		}
	}

	/* flush TLB */
	linux_vmcb = (struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr);
	linux_vmcb->tlb_control=TLB_CONTROL_FLUSHALL;
}

///* function to break a big page into small pages in nested page table
//*/
//void svm_nested_breakpde(VCPU * vcpu, u32 nvaddr)
//{
//	pdt_t npd;
//	pt_t npt;
//	u64 pd_entry;
//	u32 pdp_index, pd_index, pt_index;
//	u32 pd_base, pt_base;
//	u64 flags;
//	u32 i, tmp;
//
//	/* get fields from virtual addr */
//	pdp_index = pae_get_pdpt_index(nvaddr);
//	pd_index = pae_get_pdt_index(nvaddr);
//	pt_index = pae_get_pt_index(nvaddr);
//
//	/* get page table addresses from VCPU */
//	pd_base = vcpu->npt_vaddr_pdts;
//	pt_base = vcpu->npt_vaddr_pts;
//
//	npd = (pdt_t)(pd_base + (pdp_index << PAGE_SHIFT_4K));
//	pd_entry = npd[pd_index]; 
//
//	if (pd_entry & _PAGE_PSE)
//	{
//		npt = (pt_t)(pt_base + ((pdp_index * PAE_PTRS_PER_PDT + pd_index) << (PAGE_SHIFT_4K))); 
//		memset(npt, 0, PAGE_SIZE_4K);
//
//		tmp = __pa((u32)npt);
//		flags = pae_get_flags_from_pde(pd_entry); 
//		flags &= ~_PAGE_PSE;
//		npd[pd_index] = pae_make_pde((u64)tmp, flags); 
//
//		tmp = pae_get_addr_from_pde_big(pd_entry); 
//		for (i = 0; i < PAE_PTRS_PER_PT; i ++, tmp += PAGE_SIZE_4K)
//			npt[i] = pae_make_pte((u64)tmp, flags);
//	}
//
//	return;
//}
//void svm_nested_promote(VCPU * vcpu, u32 pfn)
//{
//	printf("[TV] (Disabled) promote 2M page pfn %#x\n", pfn);
//}
//





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

	void * linux_vmcb;
	u32 is_pae;
	u64 gcr3;

	if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
		linux_vmcb = (struct _vmx_vmcsfields *)(&(vcpu->vmcs));
		is_pae = ((struct _vmx_vmcsfields *)linux_vmcb)->guest_CR4 & CR4_PAE;
		gcr3 = ((struct _vmx_vmcsfields *)linux_vmcb)->guest_CR3;
	} else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
		linux_vmcb = (struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr);
		gcr3 = ((struct vmcb_struct *)linux_vmcb)->cr3;
		is_pae = ((struct vmcb_struct *)linux_vmcb)->cr4 & CR4_PAE;
	} else {
		printf("unknown cpu vendor!\n");
		HALT();
	}


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
		gpdp = (pdpt_t)__gpa2hva__((u32)tmp); 
		pdp_entry = gpdp[pdp_index];
		if (pdpe) *pdpe = pdp_entry;

		tmp = pae_get_addr_from_pdpe(pdp_entry);
		if (pd) *pd = tmp;
		gpd = (pdt_t)__gpa2hva__((u32)tmp);
		pd_entry = gpd[pd_index]; 
		if (pde) *pde = pd_entry;

		// if its 0, that means its 4 KB page
		// else, its 2MB pages 
		if ( (pd_entry & _PAGE_PSE) == 0 ) {
			/* get addr of page table from entry */
			tmp = pae_get_addr_from_pde(pd_entry);
			if (pt) *pt = tmp;
			gpt = (pt_t)__gpa2hva__((u32)tmp);  
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
		gpd = (npdt_t)__gpa2hva__((u32)tmp); 

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
			gpt = (npt_t)__gpa2hva__((u32)tmp);  
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
	u32 is_pae = VCPU_gcr4(vcpu) & CR4_PAE;
	u64 gcr3 = VCPU_gcr3(vcpu);

	if (is_pae)
	{ 
		u32 pdp_index, pd_index, pt_index;
		pdpt_t gpdp; /* guest page directory */
		pdt_t gpd; 
		pt_t gpt; 
		u64 pdp_entry, pd_entry;
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
				printf("[TV] gvaddr 0x%x, vcurr 0x%x, vend 0x%x\n", gvaddr, vcurr, vend);
				printf("WARNNING: sensitive code address is not in a single 2M page\n");
			}

			pd_index = pae_get_pdt_index(gvaddr);
			pt_index = pae_get_pt_index(gvaddr);

			tmp = pae_get_addr_from_32bit_cr3(gcr3);
			gpdp = (pdpt_t)__gpa2hva__((u32)tmp); 
			pdp_entry = gpdp[pdp_index];

			tmp = pae_get_addr_from_pdpe(pdp_entry);
			gpd = (pdt_t)__gpa2hva__((u32)tmp);
			pd_entry = gpd[pd_index]; 

			if ( (pd_entry & _PAGE_PSE) == 0 ) {
				/* get addr of page table from entry */
				paddr = pae_get_addr_from_pde(pd_entry);
				gpt = (pt_t)__gpa2hva__(paddr);  
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
					printf("[TV] gvaddr 0x%x, vcurr 0x%x, vend 0x%x, index %d, paddr %#x\n", gvaddr, vcurr, vend, index, paddr);
				}
			}
			else { /* 2MB page */
				printf("FATAL ERROR: currently we don't support big page for sensitive code because of the limitation of pte_page\n");
				HALT();
			}
		}
	}else
	{
		u32 pd_index, pt_index;
		npdt_t gpd; 
		npt_t gpt; 
		u64 pd_entry;
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
				printf("[TV] gvaddr 0x%x, vcurr 0x%x, vend 0x%x\n", gvaddr, vcurr, vend);
				printf("WARNNING: sensitive code address is not in a single 2M page\n");
			}

			pt_index = npae_get_pt_index(gvaddr);

			tmp = npae_get_addr_from_32bit_cr3(gcr3);
			gpd = (npdt_t)__gpa2hva__((u32)tmp);
			pd_entry = gpd[pd_index]; 

			if ( (pd_entry & _PAGE_PSE) == 0 ) {
				/* get addr of page table from entry */
				paddr = npae_get_addr_from_pde(pd_entry);
				gpt = (npt_t)__gpa2hva__(paddr);  
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
				HALT();
			}
		}
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
extern u16 get_16bit_aligned_value_from_guest(VCPU * vcpu, u32 gvaddr)
{
  u32 gpaddr;
  
  gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr);
  return *((u16 *)__gpa2hva__(gpaddr));
}

extern u32 get_32bit_aligned_value_from_guest(VCPU * vcpu, u32 gvaddr)
{
  u32 gpaddr;
  
  gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr);
  return *((u32 *)__gpa2hva__(gpaddr));
}

extern void put_32bit_aligned_value_to_guest(VCPU * vcpu, u32 gvaddr, u32 value)
{
  u32 gpaddr;
  
  gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr);
  *((u32 *)__gpa2hva__(gpaddr)) = value;
}

extern void copy_from_guest(VCPU * vcpu, u8 *dst,u32 gvaddr, u32 len)
{
  u32 gpaddr, gvend, gvprev;
  u32 tmp;

  gvprev = gvaddr;
  gvend = gvaddr + len;

  gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr);

  if (gvaddr & 0x3)
  {
    tmp = (gvaddr + 0x3) & (u32)~0x3;
    for (; (gvaddr < gvend) && (gvaddr < tmp); gvaddr ++, gpaddr ++, dst ++)
    {
      if (!SAME_PAGE_NPAE(gvprev, gvaddr))
        gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr);

      *dst = *((u8 *)__gpa2hva__(gpaddr));
      gvprev = gvaddr;
    }
  }
  if (gvaddr < gvend)
  {
    tmp = gvend & (u32)~0x3;
    for (; gvaddr < tmp; gvaddr += 4, gpaddr += 4, dst += 4)
    {
      if (!SAME_PAGE_NPAE(gvprev, gvaddr))
        gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr);

      *(u32 *)dst = *((u32 *)__gpa2hva__(gpaddr));
      gvprev = gvaddr;
    }
  }
  if (gvaddr < gvend)
  {
    for (; gvaddr < gvend; gvaddr ++, gpaddr ++, dst ++)
    {
      if (!SAME_PAGE_NPAE(gvprev, gvaddr))
        gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr);

      *dst = *((u8 *)__gpa2hva__(gpaddr));
      gvprev = gvaddr;
    }
  }
  return;
}

extern void copy_to_guest(VCPU * vcpu, u32 gvaddr, u8 *src, u32 len)
{
  u32 gpaddr, gvend, gvprev;
  u32 tmp;

  gvprev = gvaddr;
  gvend = gvaddr + len;

  gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr);

  if (gvaddr & 0x3)
  {
    tmp = (gvaddr + 0x3) & (u32)~0x3;
    for (; (gvaddr < gvend) && (gvaddr < tmp); gvaddr ++, gpaddr ++, src ++)
    {
      if (!SAME_PAGE_NPAE(gvprev, gvaddr))
        gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr);

      *((u8 *)__gpa2hva__(gpaddr)) = *src;
      gvprev = gvaddr;
    }
  }
  if (gvaddr < gvend)
  {
    tmp = gvend & (u32)~0x3;
    for (; gvaddr < tmp; gvaddr += 4, gpaddr += 4, src += 4)
    {
      if (!SAME_PAGE_NPAE(gvprev, gvaddr))
        gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr);

      *((u32 *)__gpa2hva__(gpaddr)) = *(u32 *)src;
      gvprev = gvaddr;
    }
  }
  if (gvaddr < gvend)
  {
    for (; gvaddr < gvend; gvaddr ++, gpaddr ++, src ++)
    {
      if (!SAME_PAGE_NPAE(gvprev, gvaddr))
        gpaddr = gpt_vaddr_to_paddr(vcpu, gvaddr);

      *((u8 *)__gpa2hva__(gpaddr)) = *src;
      gvprev = gvaddr;
    }
  }
  return;
}

void * __gpa2hva__(u32 gpaddr)
{
	if (gpaddr >= rpb->XtVmmRuntimePhysBase && gpaddr < rpb->XtVmmRuntimePhysBase+rpb->XtVmmRuntimeSize){
		return (void *)(rpb->XtVmmRuntimeVirtBase+(gpaddr-rpb->XtVmmRuntimePhysBase));
	} else if (gpaddr >= rpb->XtVmmRuntimeVirtBase && gpaddr < rpb->XtVmmRuntimeVirtBase+rpb->XtVmmRuntimeSize) {
		return (void *)(rpb->XtVmmRuntimePhysBase+(gpaddr-rpb->XtVmmRuntimeVirtBase));
	} else {
		return (void *)(gpaddr);
	}
}


