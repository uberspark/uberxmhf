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

/* check all pages in given range can be read/written by user level privilege */
/* see Intel System Programming Guide, Volume 3, 5-42 "combined Page-Directory and Page-Table Protection"  */
u32 guest_pt_check_user_rw(VCPU * vcpu, u32 vaddr, u32 page_num)
{
	hpt_prot_t effective_prots;
	bool user_accessible;
	hpt_type_t t = (VCPU_gcr4(vcpu) & CR4_PAE) ? HPT_TYPE_PAE : HPT_TYPE_NORM;
	hpt_pmo_t root = {
		.pm = hpt_emhf_get_current_guest_root_pm(vcpu),
		.t = t,
		.lvl = hpt_root_lvl(t),
	};
	hpt_walk_ctx_t ctx = hpt_guest_walk_ctx;
	size_t i;

	ctx.t = t;

	for(i=0; i<page_num; i++) {
		effective_prots = hpto_walk_get_effective_prots(&ctx,
																										&root,
																										vaddr+(i<<PAGE_SHIFT_4K),
																										&user_accessible);
		if (!user_accessible
				|| !((effective_prots & HPT_PROTS_RW) == HPT_PROTS_RW))
			return 1;
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
		.pm = hpt_emhf_get_current_guest_root_pm(vcpu),
		.t = t,
		.lvl = hpt_root_lvl(t),
	};
	hpt_walk_ctx_t ctx = hpt_guest_walk_ctx;
	ctx.t = t;

	hpt_copy_from_guest(&ctx, &root, dst, gvaddr, len);

}

extern void copy_to_current_guest(VCPU * vcpu, u32 gvaddr, u8 *src, u32 len)
{
	hpt_type_t t = (VCPU_gcr4(vcpu) & CR4_PAE) ? HPT_TYPE_PAE : HPT_TYPE_NORM;
	hpt_pmo_t root = {
		.pm = hpt_emhf_get_current_guest_root_pm(vcpu),
		.t = t,
		.lvl = hpt_root_lvl(t),
	};
	hpt_walk_ctx_t ctx = hpt_guest_walk_ctx;
	ctx.t = t;

	hpt_copy_to_guest(&ctx, &root, gvaddr, src, len);

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
    hpt_pmeo_setprot(&page_reg_npmeo, section->reg_prot);
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

/* lend a section of memory from a user-space process (on the
   commodity OS) to a pal.
	 PRE: assumes section was already successfully lent using scode_lend_section
	 PRE: assumes no concurrent access to page tables (e.g., quiesce other cpus)
*/
void scode_return_section(hpt_pmo_t* reg_npmo_root, hpt_walk_ctx_t *reg_npm_ctx,
													hpt_pmo_t* pal_npmo_root, hpt_walk_ctx_t *pal_npm_ctx,
													hpt_pmo_t* pal_gpmo_root, hpt_walk_ctx_t *pal_gpm_ctx,
													const tv_pal_section_int_t *section)
{
  size_t offset;

  for (offset=0; offset < section->size; offset += PAGE_SIZE_4K) {
    hpt_va_t page_pal_gva = section->pal_gva + offset;

    /* XXX we don't use hpt_va_t or hpt_pa_t for gpa's because these
       get used as both */
    u64 page_reg_gpa, page_pal_gpa; /* guest-physical-addresses */
    hpt_pmeo_t page_pal_gpmeo; /* pal's guest page-map-entry and lvl */

    hpt_walk_get_pmeo(&page_pal_gpmeo,
                      pal_gpm_ctx,
                      pal_gpmo_root,
                      1,
                      page_pal_gva);
    ASSERT(page_pal_gpmeo.lvl==1); /* we don't handle large pages */
    page_pal_gpa = hpt_pmeo_get_address(&page_pal_gpmeo);

    /* lend_section always uses the same gpas between reg and pal */
    page_reg_gpa = page_pal_gpa;

    /* check that this pal VM is allowed to access this system-physical mem.
			 we only check that it's readable; trustvisor-wide we maintain the invariant
			 that a page is readable in a PAL's npt iff it is not readable in the guest npt
			 or other PALs' npts.
		 */
    {
      hpt_prot_t effective_prots;
      bool user_accessible=false;
      effective_prots = hpto_walk_get_effective_prots(pal_npm_ctx,
                                                      pal_npmo_root,
                                                      page_pal_gpa,
                                                      &user_accessible);
			CHK(effective_prots & HPT_PROTS_R);
    }

    /* revoke access from 'pal' VM */
		hpto_walk_set_prot(pal_npm_ctx,
											 pal_npmo_root,
											 page_pal_gpa,
											 HPT_PROTS_NONE);

    /* scode_lend_section leaves reg guest page tables intact, so no
			 need to restore anything in them here. */

    /* revoke access from pal guest page tables */
		hpto_walk_set_prot(pal_gpm_ctx,
											 pal_gpmo_root,
											 page_pal_gva,
											 HPT_PROTS_NONE);

    /* add access to reg nested page tables */
		hpto_walk_set_prot(reg_npm_ctx,
											 reg_npmo_root,
											 page_reg_gpa,
											 HPT_PROTS_RWX);
  }
}



/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */
