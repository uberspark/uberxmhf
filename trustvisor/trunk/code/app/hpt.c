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
static inline
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

typedef struct {
  hpt_va_t reg_gva;
  hpt_va_t pal_gva;
  size_t size;
  hpt_prot_t prot;
} section_t;

/* XXX TEMP */
#define CHK(x) ASSERT(x)
#define CHK_RV(x) ASSERT(!(x))
#define hpt_walk_check_prot(x, y) HPT_PROTS_RWX

void scode_add_section(hpt_pm_t reg_npt_root, hpt_walk_ctx_t *reg_npt_ctx,
                       hpt_pm_t reg_gpt_root, hpt_walk_ctx_t *reg_gpt_ctx,
                       hpt_pm_t pal_npt_root, hpt_walk_ctx_t *pal_npt_ctx,
                       hpt_pm_t pal_gpt_root, hpt_walk_ctx_t *pal_gpt_ctx,
                       const section_t *section)
{
  int reg_gpt_root_lvl = hpt_root_lvl(reg_gpt_ctx->t);
  int reg_npt_root_lvl = hpt_root_lvl(reg_npt_ctx->t);
  int pal_gpt_root_lvl = hpt_root_lvl(pal_gpt_ctx->t);
  int pal_npt_root_lvl = hpt_root_lvl(pal_npt_ctx->t);
  size_t offset;
  int hpt_err;
  
  /* XXX don't hard-code page size here. */
  /* XXX fail gracefully */
  ASSERT((section->size % PAGE_SIZE_4K) == 0); 

  for (offset=0; offset < section->size; offset += PAGE_SIZE_4K) {
    hpt_va_t page_reg_gva = section->reg_gva + offset;
    hpt_va_t page_pal_gva = section->pal_gva + offset;

    /* XXX we don't use hpt_va_t or hpt_pa_t for gpa's because they
       get used as both */
    u64 page_reg_gpa, page_pal_gpa; /* guest-physical-addresses */


    hpt_pme_t page_reg_gpme; int page_reg_gpme_lvl; /* reg's guest page-map-entry and lvl */
    hpt_pme_t page_pal_gpme; int page_pal_gpme_lvl; /* pal's guest page-map-entry and lvl */

    hpt_pme_t page_reg_npme; int page_reg_npme_lvl; /* reg's nested page-map-entry and lvl */
    hpt_pme_t page_pal_npme; int page_pal_npme_lvl; /* pal's nested page-map-entry and lvl */

    /* lock? quiesce? */

    page_reg_gpme_lvl=1;
    page_reg_gpme = hpt_walk_get_pme(reg_gpt_ctx, reg_gpt_root_lvl, reg_gpt_root,
                                     &page_reg_gpme_lvl,
                                     page_reg_gva);
    ASSERT(page_reg_gpme_lvl==1); /* we don't handle large pages */
    page_reg_gpa = hpt_pme_get_address(reg_gpt_ctx->t, page_reg_gpme_lvl, page_reg_gpme);

    page_reg_npme_lvl=1;
    page_reg_npme = hpt_walk_get_pme(reg_npt_ctx, reg_npt_root_lvl, reg_npt_root,
                                     &page_reg_npme_lvl,
                                     page_reg_gpa);
    ASSERT(page_reg_npme_lvl==1); /* we don't handle large pages */
    /* page_spa = hpt_pme_get_address(reg_npt_ctx->t, page_reg_npme_lvl, page_reg_npme); */

    /* probably no reason to change */
    page_pal_gpa = page_reg_gpa;

    /* check that this VM is allowed to access this system-physical mem */
    CHK(HPT_PROTS_RWX == hpt_walk_check_prot(reg_npt_root, page_reg_gpa));

    /* check that this guest process is allowed to access this guest-physical mem */
    CHK(HPT_PROTS_RWX == hpt_walk_check_prot(guest_reg_root, page_reg_gva));

    /* check that the requested virtual address isn't already mapped
       into PAL's address space */
    /*FIXME XXX*/

    /* revoke access from 'reg' VM */
    page_reg_npme = hpt_pme_setprot(reg_npt_ctx->t, page_reg_npme_lvl,
                                    page_reg_npme, HPT_PROTS_NONE);
    hpt_err = hpt_walk_insert_pme(reg_npt_ctx, reg_npt_root_lvl, reg_npt_root, 1,
                                  page_reg_gpa, page_reg_npme);
    CHK_RV(hpt_err);

    /* for simplicity, we don't bother removing from guest page
       tables. removing from nested page tables is sufficient */

    /* add access to pal guest page tables */
    page_pal_gpme = page_reg_gpme; /* XXX SECURITY should build from scratch */
    page_pal_gpme_lvl = page_reg_gpme_lvl;
    page_pal_gpme = hpt_pme_set_address(pal_gpt_ctx->t, page_pal_gpme_lvl,
                                        page_pal_gpme, page_pal_gva);
    page_pal_gpme = hpt_pme_setprot(pal_gpt_ctx->t, page_pal_gpme_lvl,
                                    page_pal_gpme, HPT_PROTS_RWX);
    hpt_walk_insert_pme_alloc(pal_gpt_ctx, pal_gpt_root_lvl, pal_gpt_root, 1,
                              page_pal_gva, page_pal_gpme);

    /* add access to pal nested page tables */
    page_pal_npme = page_reg_npme; /* XXX SECURITY should build from scratch */
    page_pal_npme_lvl = page_reg_npme_lvl;
    page_pal_npme = hpt_pme_setprot(pal_npt_ctx->t, page_pal_npme_lvl,
                                    page_pal_npme, section->prot);
    hpt_walk_insert_pme_alloc(pal_npt_ctx, pal_npt_root_lvl, pal_npt_root, 1,
                              page_pal_gpa, page_pal_npme);

    /* unlock? unquiesce? */
  }
  /* add pal guest page tables to pal nested page tables */
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'f */
/* tab-width:2      */
/* End:             */
