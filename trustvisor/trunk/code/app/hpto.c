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

#include <hpto.h>

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

void hpt_pmeo_setuser(hpt_pmeo_t *pmeo, bool user)
{
  pmeo->pme = hpt_pme_setuser(pmeo->t, pmeo->lvl, pmeo->pme, user);
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

