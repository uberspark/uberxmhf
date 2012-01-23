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
  hpt_log_trace("Entering %s\n", __FUNCTION__);
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

bool hpt_pmeo_is_page(const hpt_pmeo_t *pmeo)
{
  return hpt_pme_is_page(pmeo->t, pmeo->lvl, pmeo->pme);
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

void hpto_walk_set_prot(hpt_walk_ctx_t *walk_ctx,
                        hpt_pmo_t *pmo_root,
                        hpt_va_t va,
                        hpt_prot_t prot)
{
  hpt_walk_set_prot(walk_ctx, pmo_root->pm, pmo_root->lvl, va, prot);
}

hpt_pa_t hpt_pmeo_va_to_pa(hpt_pmeo_t* pmeo, hpt_va_t va)
{
  hpt_pa_t base;
  hpt_pa_t offset;
  int offset_hi;

  assert(hpt_pme_is_page(pmeo->t, pmeo->lvl, pmeo->pme));
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

size_t hpt_remaining_on_page(const hpt_pmeo_t *pmeo, hpt_va_t va)
{
  size_t offset_on_page;
  size_t page_size;
  size_t page_size_log_2;

  page_size_log_2 = hpt_pmeo_page_size_log_2(pmeo);
  page_size = 1 << page_size_log_2;
  offset_on_page = va & MASKRANGE64(page_size_log_2-1, 0);
  return page_size - offset_on_page;
}

void hpt_copy_from_guest(const hpt_walk_ctx_t *ctx,
                         const hpt_pmo_t *pmo,
                         void *dst,
                         hpt_va_t src_va_base,
                         size_t len)
{
  size_t copied=0;

  while(copied < len) {
    hpt_va_t src_va = src_va_base + copied;
    hpt_pmeo_t src_pmeo;
    hpt_pa_t src_pa;
    size_t to_copy;
    size_t remaining_on_page;

    hpt_walk_get_pmeo(&src_pmeo, ctx, pmo, 1, src_va);

    src_pa = hpt_pmeo_va_to_pa(&src_pmeo, src_va);
    remaining_on_page = hpt_remaining_on_page(&src_pmeo, src_pa);
    to_copy = MIN(len-copied, remaining_on_page);

    memcpy(dst+copied, ctx->pa2ptr(ctx->pa2ptr_ctx, src_pa), to_copy);
    copied += to_copy;
  }
}

void hpt_copy_to_guest(const hpt_walk_ctx_t *ctx,
                       const hpt_pmo_t *pmo,
                       hpt_va_t dst_va_base,
                       void *src,
                       size_t len)
{
  size_t copied=0;

  while(copied < len) {
    hpt_va_t dst_va = dst_va_base + copied;
    hpt_pmeo_t dst_pmeo;
    hpt_pa_t dst_pa;
    size_t to_copy;
    size_t remaining_on_page;

    hpt_walk_get_pmeo(&dst_pmeo, ctx, pmo, 1, dst_va);

    dst_pa = hpt_pmeo_va_to_pa(&dst_pmeo, dst_va);
    remaining_on_page = hpt_remaining_on_page(&dst_pmeo, dst_pa);
    to_copy = MIN(len-copied, remaining_on_page);

    memcpy(ctx->pa2ptr(ctx->pa2ptr_ctx, dst_pa), src+copied, to_copy);
    copied += to_copy;
  }
}

void hpt_copy_guest_to_guest(const hpt_walk_ctx_t *dst_ctx,
                             const hpt_pmo_t *dst_pmo,
                             hpt_va_t dst_va_base,
                             const hpt_walk_ctx_t *src_ctx,
                             const hpt_pmo_t *src_pmo,
                             hpt_va_t src_va_base,
                             size_t len)
{
  size_t copied=0;

  while(copied < len) {
    hpt_va_t dst_va = dst_va_base + copied;
    hpt_va_t src_va = src_va_base + copied;
    hpt_pmeo_t dst_pmeo;
    hpt_pmeo_t src_pmeo;
    hpt_pa_t dst_pa;
    hpt_pa_t src_pa;
    size_t to_copy;
    size_t dst_remaining_on_page;
    size_t src_remaining_on_page;

    hpt_walk_get_pmeo(&dst_pmeo, dst_ctx, dst_pmo, 1, dst_va);
    dst_pa = hpt_pmeo_va_to_pa(&dst_pmeo, dst_va);

    hpt_walk_get_pmeo(&src_pmeo, src_ctx, src_pmo, 1, src_va);
    src_pa = hpt_pmeo_va_to_pa(&src_pmeo, src_va);

    dst_remaining_on_page = hpt_remaining_on_page(&dst_pmeo, dst_pa);
    src_remaining_on_page = hpt_remaining_on_page(&src_pmeo, src_pa);

    to_copy = MIN(dst_remaining_on_page, src_remaining_on_page);
    to_copy = MIN(to_copy, len-copied);

    memcpy(dst_ctx->pa2ptr(dst_ctx->pa2ptr_ctx, dst_pa),
           src_ctx->pa2ptr(src_ctx->pa2ptr_ctx, src_pa),
           to_copy);
    copied += to_copy;
  }
}

void hpt_memset_guest(const hpt_walk_ctx_t *ctx,
                      const hpt_pmo_t *pmo,
                      hpt_va_t dst_va_base,
                      int c,
                      size_t len)
{
  size_t set=0;

  while(set < len) {
    hpt_va_t dst_va = dst_va_base + set;
    hpt_pmeo_t dst_pmeo;
    hpt_pa_t dst_pa;
    size_t to_set;
    size_t remaining_on_page;

    hpt_walk_get_pmeo(&dst_pmeo, ctx, pmo, 1, dst_va);

    dst_pa = hpt_pmeo_va_to_pa(&dst_pmeo, dst_va);
    remaining_on_page = hpt_remaining_on_page(&dst_pmeo, dst_pa);
    to_set = MIN(len-set, remaining_on_page);

    memset(ctx->pa2ptr(ctx->pa2ptr_ctx, dst_pa), c, to_set);
    set += to_set;
  }
}

