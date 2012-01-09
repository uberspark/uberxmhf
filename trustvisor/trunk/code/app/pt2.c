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

#include <emhf.h> /* FIXME: narrow this down so this can be compiled
                     and tested independently */
#include <pt2.h>
#include <pages.h>

void hpt_walk_set_prot(hpt_walk_ctx_t *walk_ctx, hpt_pm_t pm, int pm_lvl, gpa_t gpa, hpt_prot_t prot)
{
  hpt_pme_t pme;
  int end_pm_lvl=1;

  pm = hpt_walk_get_pm(walk_ctx, pm_lvl, pm, &end_pm_lvl, gpa);
  ASSERT(pm != NULL);
  ASSERT(end_pm_lvl==1); /* FIXME we don't handle large pages */
  pme = hpt_pm_get_pme_by_va(walk_ctx->t, end_pm_lvl, pm, gpa);
  pme = hpt_pme_setprot(walk_ctx->t, end_pm_lvl, pme, prot);
  hpt_pm_set_pme_by_va(walk_ctx->t, end_pm_lvl, pm, gpa, pme);
}

void hpt_walk_set_prots(hpt_walk_ctx_t *walk_ctx,
                        hpt_pm_t pm,
                        int pm_lvl,
                        gpa_t gpas[],
                        size_t num_gpas,
                        hpt_prot_t prot)
{
  size_t i;
  for(i=0; i<num_gpas; i++) {
    hpt_walk_set_prot(walk_ctx, pm, pm_lvl, gpas[i], prot);
  }
}

/* inserts pme into the page map of level tgt_lvl containing va.
 * fails if tgt_lvl is not allocated.
 * XXX move into hpt.h once it's available again.
 */
int hpt_walk_insert_pme(const hpt_walk_ctx_t *ctx, int lvl, hpt_pm_t pm, int tgt_lvl, hpt_va_t va, hpt_pme_t pme)
{
  int end_lvl=tgt_lvl;
  dprintf(LOG_TRACE, "hpt_walk_insert_pme_alloc: lvl:%d pm:%x tgt_lvl:%d va:%Lx pme:%Lx\n",
          lvl, (u32)pm, tgt_lvl, va, pme);
  pm = hpt_walk_get_pm(ctx, lvl, pm, &end_lvl, va);

  dprintf(LOG_TRACE, "hpt_walk_insert_pme: got pm:%x end_lvl:%d\n",
          (u32)pm, end_lvl);

  if(pm == NULL || tgt_lvl != end_lvl) {
    return 1;
  }

  hpt_pm_set_pme_by_va(ctx->t, tgt_lvl, pm, va, pme);
  return 0;
}

int hpt_walk_insert_pmeo(const hpt_walk_ctx_t *ctx,
                         hpt_pmo_t *pmo,
                         const hpt_pmeo_t *pmeo,
                         hpt_va_t va)
{
  return hpt_walk_insert_pme(ctx,
                             pmo->lvl,
                             pmo->pm,
                             pmeo->lvl,
                             va,
                             pmeo->pme);
}

int hpt_walk_insert_pmeo_alloc(const hpt_walk_ctx_t *ctx,
                               hpt_pmo_t *pmo,
                               const hpt_pmeo_t *pmeo,
                               hpt_va_t va)
{
  return hpt_walk_insert_pme_alloc(ctx, pmo->lvl, pmo->pm, pmeo->lvl, va, pmeo->pme);
}

void hpt_walk_get_pmeo(hpt_pmeo_t *pmeo,
                       const hpt_walk_ctx_t *ctx,
                       const hpt_pmo_t *pmo,
                       int end_lvl,
                       hpt_va_t va)
{
	dprintf(LOG_TRACE, "Entering %s\n", __FUNCTION__);
  pmeo->pme = hpt_walk_get_pme(ctx, pmo->lvl, pmo->pm, &end_lvl, va);
  pmeo->t = pmo->t;
  pmeo->lvl = end_lvl;
}

hpt_pa_t hpt_pmeo_get_address(const hpt_pmeo_t *pmeo)
{
  return hpt_pme_get_address(pmeo->t, pmeo->lvl, pmeo->pme);
}
void hpt_pmeo_set_address(hpt_pmeo_t *pmeo, hpt_pa_t addr)
{
  pmeo->pme = hpt_pme_set_address(pmeo->t, pmeo->lvl, pmeo->pme, addr);
}

bool hpt_pmeo_is_present(const hpt_pmeo_t *pmeo)
{
  return hpt_pme_is_present(pmeo->t, pmeo->lvl, pmeo->pme);
}

void hpt_pmeo_setprot(hpt_pmeo_t *pmeo, hpt_prot_t perms)
{
  pmeo->pme = hpt_pme_setprot(pmeo->t, pmeo->lvl, pmeo->pme, perms);
}

hpt_prot_t hpt_pmeo_getprot(const hpt_pmeo_t *pmeo)
{
  return hpt_pme_getprot(pmeo->t, pmeo->lvl, pmeo->pme);
}

bool hpt_pmeo_getuser(const hpt_pmeo_t *pmeo)
{
  return hpt_pme_getuser(pmeo->t, pmeo->lvl, pmeo->pme);
}

void hpt_pm_get_pmeo_by_va(hpt_pmeo_t *pmeo, const hpt_pmo_t *pmo, hpt_va_t va)
{
  pmeo->t = pmo->t;
  pmeo->lvl = pmo->lvl;
  pmeo->pme = hpt_pm_get_pme_by_va(pmo->t, pmo->lvl, pmo->pm, va);
}

bool hpto_walk_next_lvl(const hpt_walk_ctx_t *ctx, hpt_pmo_t *pmo, hpt_va_t va)
{
  return hpt_walk_next_lvl(ctx, &pmo->lvl, &pmo->pm, va);
}

/* returns the effective protections for the given address, which is
 * the lowest permissions for the page walk. Also sets
 * *user_accessible if not NULL and if the virtual address is set
 * user-accessible.
 */
hpt_prot_t hpto_walk_get_effective_prots(const hpt_walk_ctx_t *ctx,
                                         const hpt_pmo_t *pmo_root,
                                         hpt_va_t va,
                                         bool *user_accessible)
{
  hpt_prot_t prots_rv = HPT_PROTS_RWX;
  bool user_accessible_rv = true;
  hpt_pmo_t pmo = *pmo_root;

  do {
    hpt_pmeo_t pmeo;
    hpt_pm_get_pmeo_by_va(&pmeo, &pmo, va);
    prots_rv &= hpt_pmeo_getprot(&pmeo);
    user_accessible_rv = user_accessible_rv && hpt_pmeo_getuser(&pmeo);
  } while (hpto_walk_next_lvl(ctx, &pmo, va));

  if(user_accessible != NULL) {
    *user_accessible = user_accessible_rv;
  }
  return prots_rv;
}

hpt_pa_t hpt_pmeo_va_to_pa(hpt_pmeo_t* pmeo, hpt_va_t va)
{
	hpt_pa_t base;
	hpt_pa_t offset;
	int offset_hi;

	ASSERT(hpt_pme_is_page(pmeo->t, pmeo->lvl, pmeo->pme));
	base = hpt_pmeo_get_address(pmeo);

	offset_hi = hpt_va_idx_hi[pmeo->t][pmeo->lvl-1];
	offset = va & MASKRANGE64(offset_hi, 0);
	return base + offset;
}

hpt_pa_t hpto_walk_va_to_pa(const hpt_walk_ctx_t *ctx,
														const hpt_pmo_t *pmo,
														hpt_va_t va)
{
	hpt_pmeo_t pmeo;
	hpt_walk_get_pmeo(&pmeo, ctx, pmo, 1, va);
	return hpt_pmeo_va_to_pa(&pmeo, va);
}

size_t hpt_pmeo_page_size_log_2(const hpt_pmeo_t *pmeo)
{
	int offset_hi;
	offset_hi = hpt_va_idx_hi[pmeo->t][pmeo->lvl-1];
	return offset_hi+1;
}

size_t hpt_pmeo_page_size(const hpt_pmeo_t *pmeo)
{
	return 1 << hpt_pmeo_page_size_log_2(pmeo);
}

void hpt_copy_from_guest(const hpt_walk_ctx_t *ctx,
												 const hpt_pmo_t *pmo,
												 void *dst,
												 hpt_va_t src_gva_base,
												 size_t len)
{
	size_t copied=0;

	while(copied < len) {
		hpt_va_t src_gva = src_gva_base + copied;
		hpt_pmeo_t src_pmeo;
		hpt_pa_t src_gpa;
		size_t to_copy;
		size_t page_size_log_2;
		size_t page_size;
		size_t offset_on_page;
		size_t remaining_on_page;

		hpt_walk_get_pmeo(&src_pmeo, ctx, pmo, 1, src_gva);
		src_gpa = hpt_pmeo_va_to_pa(&src_pmeo, src_gva);

		page_size_log_2 = hpt_pmeo_page_size_log_2(&src_pmeo);
		page_size = 1 << page_size_log_2;
		offset_on_page = src_gpa & MASKRANGE64(page_size_log_2-1, 0);
		remaining_on_page = page_size - offset_on_page;

		to_copy = MAX(len-copied, remaining_on_page);

		memcpy(dst+copied, gpa2hva(src_gpa), to_copy);
		copied += to_copy;
	}
}


/* XXX TEMP */
#define CHK(x) ASSERT(x)

#define CHK_RV(x) ASSERT(!(x))
#define hpt_walk_check_prot(x, y) HPT_PROTS_RWX

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

	dprintf(LOG_TRACE, "scode_clone_gdt base:%x size:%x:\n", gdtr_base, gdt_size);

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
                        const section_t *section)
{
  size_t offset;
  int hpt_err;

	dprintf(LOG_TRACE,
					"entering scode_lend_section. Mapping from %016llx to %016llx, size %u, prot %u\n",
					section->reg_gva, section->pal_gva, section->size, (u32)section->prot);
  
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
                                                      page_pal_gva,
                                                      &user_accessible);
      CHK(HPT_PROTS_RWX == effective_prots);
      CHK(user_accessible);
    }

    /* check that this guest process is allowed to access this guest-physical mem */
    {
      hpt_prot_t effective_prots;
      bool user_accessible=false;
      effective_prots = hpto_walk_get_effective_prots(reg_gpm_ctx,
                                                      reg_gpmo_root,
                                                      page_pal_gva,
                                                      &user_accessible);
			dprintf(LOG_TRACE, "%s got reg gpt prots:0x%x, user:%d\n",
							__FUNCTION__, (u32)effective_prots, (int)user_accessible);
      CHK((effective_prots & section->prot) == section->prot);
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
    /* hpt_pmeo_setprot(&page_reg_npmeo, HPT_PROTS_NONE); */
    hpt_pmeo_setprot(&page_reg_npmeo, HPT_PROTS_RWX); /* XXX FIXME TEMP for testing */
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
    hpt_pmeo_setprot(&page_pal_npmeo, section->prot);
    hpt_err = hpt_walk_insert_pmeo_alloc(pal_npm_ctx,
                                         pal_npmo_root,
                                         &page_pal_npmeo,
                                         gpa2spa(page_pal_gpa));
    CHK_RV(hpt_err);

    /* unlock? unquiesce? */
  }
  /* XXX add pal guest page tables to pal nested page tables */
}

/* for a given virtual address range, return an array of page-map-entry-objects */
/* returned size may be larger than the requested size, in which case
   the last returned pmeo contains "extra" address-range. it's up to
   the caller to splinter that last page if necessary. */
/* *pmeos_num should be set by caller to the size of pmeos. if the
   return-value is non-zero, pmeos_of_range ran out of room;
   *pmeos_num is set to the number of pmeos that would have been
   written. */
/* XXX need to think through concurrency issues. e.g., should caller
   hold a lock? */
/* int pmeos_of_range(hpt_pmeo_t pmeos[], size_t *pmeos_num, */
/*                    hpt_pmo_t* pmo_root, hpt_walk_ctx_t *walk_ctx, */
/*                    hpt_va_t base, size_t *size) */
/* { */
/*   size_t offset; */
/*   size_t pmeos_maxnum = *pmeos_num; */
  
/*   *pmeos_num = 0; */

/*   while (offset < *size) { */
/*     hpt_va_t va = base + offset; */
/*     size_t page_size; */
/*     hpt_pmeo_t pmeo; */

/*     ASSERT(*pmeos_num < pmeos_maxnum); */

/*     hpt_walk_get_pmeo(&pmeo, */
/*                       walk_ctx, */
/*                       pmo_root, */
/*                       1, */
/*                       va); */
/*     /\* XXX need to add support to hpt to get size of memory mapped by */
/*        a page *\/ */
/*     ASSERT(pmeo.lvl == 1); */
/*     page_size = PAGE_SIZE_4K; */
/*     offset += page_size; */

/*     if (*pmeos_num < pmeos_maxnum) { */
/*       pmeos[*pmeos_num] = pmeo; */
/*     } */
/*     (*pmeos_num)++; */
/*   } */

/*   *size = offset; /\* may be larger than requested *\/ */

/*   if(*pmeos_num <= pmeos_maxnum) { */
/*     return 0; */
/*   } else { */
/*     return 1; */
/*   } */
/* } */

/* /\* nested-page-map-entry-objects of guest-page-map-entry-objects *\/ */
/* void npmeos_of_gpmeos(hpt_walk_ctx_t *reg_npm_ctx, */
/*                       hpt_pmo_t* reg_npmo_root, */
/*                       hpt_pmeo_t npmeos[], size_t *npmeos_num, */
/*                       hpt_pmeo_t gpmeos[], size_t gpmeos_num) */
/* { */
/*   size_t gpmeos_i; */

/*   for(gpmeos_i=0; gpmeos_i < gpmeos_num; gpmeos_i++) { */
    
/*   } */
/* } */


/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'f */
/* tab-width:2      */
/* End:             */
