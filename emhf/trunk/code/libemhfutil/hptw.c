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

#include <hpt.h>
#include <hptw.h>
#include <string.h> /* for memset */

#include "hpt_log.h"

int hptw_insert_pmeo(const hptw_ctx_t *ctx,
                     hpt_pmo_t *pmo_root,
                     const hpt_pmeo_t *pmeo,
                     hpt_va_t va)
{
  hpt_pmo_t pmo;
  hptw_get_pmo(&pmo, ctx, pmo_root, pmeo->lvl, va);
  if (!pmo.pm || pmo.lvl != pmeo->lvl) {
    return 1;
  }
  hpt_pmo_set_pme_by_va(&pmo, pmeo, va);
  return 0;
}

int hptw_get_pmo_alloc(hpt_pmo_t *pmo,
                       const hptw_ctx_t *ctx,
                       const hpt_pmo_t *pmo_root,
                       int end_lvl,
                       hpt_va_t va)
{
  assert(pmo_root->lvl >= end_lvl);
  *pmo = *pmo_root;
  while(pmo->lvl > end_lvl) {
    hpt_pmeo_t pmeo;
    hpt_pm_get_pmeo_by_va(&pmeo, pmo, va);
    if (hpt_pmeo_is_page(&pmeo)) {
      return 2;
    }
    if (!hpt_pmeo_is_present(&pmeo)) {
      hpt_pmo_t new_pmo = {
        .pm = ctx->gzp(ctx->gzp_ctx,
                       HPT_PM_SIZE, /*FIXME*/
                       hpt_pm_size(pmo->t, pmo->lvl-1)),
        .lvl = pmo->lvl-1,
        .t = pmo->t,
      };
      if (!new_pmo.pm) {
        return 1;
      }
      hpt_pmeo_set_address(&pmeo, ctx->ptr2pa(ctx->ptr2pa_ctx, new_pmo.pm));
      hpt_pmeo_setprot(    &pmeo, HPT_PROTS_RWX);
      hpt_pmeo_setuser(    &pmeo, true);

      hpt_pmo_set_pme_by_va(pmo, &pmeo, va);
    }
    {
      bool walked_next_lvl;
      walked_next_lvl = hptw_next_lvl(ctx, pmo, va);
      assert(walked_next_lvl);
    }
  }
  return 0;
}

int hptw_insert_pmeo_alloc(const hptw_ctx_t *ctx,
                           hpt_pmo_t *pmo_root,
                           const hpt_pmeo_t *pmeo,
                           hpt_va_t va)
{
  hpt_pmo_t pmo;
  if (hptw_get_pmo_alloc(&pmo, ctx, pmo_root, pmeo->lvl, va)) {
    return 1;
  }
  if(!pmo.pm || pmo.lvl != pmeo->lvl) {
    return 2;
  }
  hpt_pmo_set_pme_by_va(&pmo, pmeo, va);
  return 0;
}

void hptw_get_pmo(hpt_pmo_t *pmo,
                  const hptw_ctx_t *ctx,
                  const hpt_pmo_t *pmo_root,
                  int end_lvl,
                  hpt_va_t va)
{
  *pmo = *pmo_root;
  while (pmo->lvl > end_lvl
         && hptw_next_lvl(ctx, pmo, va));
}

void hptw_get_pmeo(hpt_pmeo_t *pmeo,
                   const hptw_ctx_t *ctx,
                   const hpt_pmo_t *pmo,
                   int end_lvl,
                   hpt_va_t va)
{
  hpt_pmo_t end_pmo;
  hptw_get_pmo(&end_pmo, ctx, pmo, end_lvl, va);
  hpt_pm_get_pmeo_by_va(pmeo, &end_pmo, va);
}

bool hptw_next_lvl(const hptw_ctx_t *ctx, hpt_pmo_t *pmo, hpt_va_t va)
{
  hpt_pmeo_t pmeo;
  hpt_pm_get_pmeo_by_va(&pmeo, pmo, va);

  assert(pmo->pm);

  if (!hpt_pmeo_is_present(&pmeo)
      || hpt_pmeo_is_page(&pmeo)) {
    eu_trace("at leaf. is-present:%d is-page:%d",
                  hpt_pmeo_is_present(&pmeo), hpt_pmeo_is_page(&pmeo));
    return false;
  } else {
    size_t avail;
    size_t pm_sz = hpt_pm_size(pmo->t, pmo->lvl-1);
    pmo->pm = ctx->pa2ptr(ctx->pa2ptr_ctx, hpt_pmeo_get_address(&pmeo),
                          pm_sz, HPT_PROTS_R, HPTW_CPL0, &avail);
    eu_trace("next-lvl:%d pm-sz:%d pmo->pm:%p avail:%d",
                  pmo->lvl-1, pm_sz, pmo->pm, avail);
    if(!pmo->pm) {
      /* didn't descend, and this is an error. we ran into trouble
         accessing the page tables themselves, which should only
         happen if the entity that set up the page tables, whether the
         guest OS or the hypervisor, is buggy or malicious */
      pmo->t = HPT_TYPE_INVALID;
      pmo->lvl = 0;
      return false;
    }
    assert(avail == pm_sz); /* this could in principle be false if,
                               e.g., a host page table has a smaller
                               page size than the size of the given
                               page map. we don't handle this
                               case. will never happen with current
                               x86 page types */
    pmo->lvl--;
    return true;
  }
}

/* returns the effective protections for the given address, which is
 * the lowest permissions for the page walk. Also sets
 * *user_accessible if not NULL and if the virtual address is set
 * user-accessible.
 */
hpt_prot_t hptw_get_effective_prots(const hptw_ctx_t *ctx,
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
  } while (hptw_next_lvl(ctx, &pmo, va));

  /* XXX should more clearly indicate an error */
  if (pmo.t == HPT_TYPE_INVALID) {
    return HPT_PROTS_NONE;
  }

  if(user_accessible != NULL) {
    *user_accessible = user_accessible_rv;
  }
  return prots_rv;
}

void hptw_set_prot(hptw_ctx_t *ctx,
                   hpt_pmo_t *pmo_root,
                   hpt_va_t va,
                   hpt_prot_t prot)
{
  hpt_pmo_t pmo;
  hpt_pmeo_t pmeo;

  hptw_get_pmo (&pmo, ctx, pmo_root, 1, va);
  assert (pmo.pm);
  assert (pmo.lvl == 1);

  hpt_pm_get_pmeo_by_va (&pmeo, &pmo, va);
  hpt_pmeo_setprot (&pmeo, prot);
  hpt_pmo_set_pme_by_va (&pmo, &pmeo, va);
}

hpt_pa_t hptw_va_to_pa(const hptw_ctx_t *ctx,
                       const hpt_pmo_t *pmo,
                       hpt_va_t va)
{
  hpt_pmeo_t pmeo;
  hptw_get_pmeo(&pmeo, ctx, pmo, 1, va);
  return hpt_pmeo_va_to_pa(&pmeo, va);
}

void* hptw_access_va(const hptw_ctx_t *ctx,
                     const hpt_pmo_t *root,
                     hpt_va_t va,
                     size_t requested_sz,
                     size_t *avail_sz)
{
  hpt_pmeo_t pmeo;
  hpt_pa_t pa;

  hptw_get_pmeo(&pmeo, ctx, root, 1, va);

  pa = hpt_pmeo_va_to_pa(&pmeo, va);
  *avail_sz = MIN(requested_sz, hpt_remaining_on_page(&pmeo, pa));

  return ctx->pa2ptr(ctx->pa2ptr_ctx, pa,
                     *avail_sz, HPT_PROTS_R, HPTW_CPL0, avail_sz);
}

void* hptw_checked_access_va(const hptw_ctx_t *ctx,
                             const hpt_pmo_t *pmo_root,
                             hpt_prot_t access_type,
                             hptw_cpl_t cpl,
                             hpt_va_t va,
                             size_t requested_sz,
                             size_t *avail_sz)
{
  hpt_pmeo_t pmeo;
  hpt_pa_t pa;
  hpt_pmo_t pmo = *pmo_root;
  void *rv=NULL;
  *avail_sz=0;

  eu_trace("va:0x%llx access_type %lld cpl:%d",
           va, access_type, cpl);

  do {
    eu_trace("pmo t:%d pm:%p lvl:%d",
             pmo.t, pmo.pm, pmo.lvl);
    hpt_pm_get_pmeo_by_va(&pmeo, &pmo, va);
    EU_CHK(((access_type & hpt_pmeo_getprot(&pmeo)) == access_type)
           && (cpl == HPTW_CPL0 || hpt_pmeo_getuser(&pmeo)),
           eu_err_e("req-priv:%lld req-cpl:%d priv:%lld user-accessible:%d",
                    access_type, cpl, hpt_pmeo_getprot(&pmeo), hpt_pmeo_getuser(&pmeo)));
  } while (hptw_next_lvl(ctx, &pmo, va));

  EU_CHK( pmo.t != HPT_TYPE_INVALID);

  EU_CHK( hpt_pmeo_is_present(&pmeo));

  /* exiting loop means hptw_next_lvl failed, which means either the
   * current pmeo is a page, or the current pmeo is not present.
   * however, we should have already returned if not present, so pmeo
   * must be a page */
  EU_VERIFY(hpt_pmeo_is_page(&pmeo));

  pa = hpt_pmeo_va_to_pa(&pmeo, va);
  *avail_sz = MIN(requested_sz, hpt_remaining_on_page(&pmeo, pa));
  eu_trace("got pa:%llx sz:%d", pa, *avail_sz);
  rv = ctx->pa2ptr(ctx->pa2ptr_ctx, pa,
                   *avail_sz, access_type, cpl, avail_sz);

 out:
  return rv;
}

int hptw_checked_copy_from_va(const hptw_ctx_t *ctx,
                              const hpt_pmo_t *pmo,
                              hptw_cpl_t cpl,
                              void *dst,
                              hpt_va_t src_va_base,
                              size_t len)
{
  size_t copied=0;

  while(copied < len) {
    hpt_va_t src_va = src_va_base + copied;
    size_t to_copy;
    void *src;

    src = hptw_checked_access_va(ctx, pmo, HPT_PROTS_R, cpl, src_va, len-copied, &to_copy);
    if(!src) {
      return 1;
    }
    memcpy(dst+copied, src, to_copy);
    copied += to_copy;
  }
  return 0;
}

int hptw_checked_copy_to_va(const hptw_ctx_t *ctx,
                            const hpt_pmo_t *pmo,
                            hptw_cpl_t cpl,
                            hpt_va_t dst_va_base,
                            void *src,
                            size_t len)
{
  size_t copied=0;

  while(copied < len) {
    hpt_va_t dst_va = dst_va_base + copied;
    size_t to_copy;
    void *dst;

    dst = hptw_checked_access_va(ctx, pmo, HPT_PROTS_W, cpl, dst_va, len-copied, &to_copy);
    if (!dst) {
      return 1;
    }
    memcpy(dst, src+copied, to_copy);
    copied += to_copy;
  }
  return 0;
}

int hptw_checked_copy_va_to_va(const hptw_ctx_t *dst_ctx,
                               const hpt_pmo_t *dst_pmo,
                               hptw_cpl_t dst_cpl,
                               hpt_va_t dst_va_base,
                               const hptw_ctx_t *src_ctx,
                               const hpt_pmo_t *src_pmo,
                               hptw_cpl_t src_cpl,
                               hpt_va_t src_va_base,
                               size_t len)
{
  size_t copied=0;
  int rv=1;

  eu_trace("dst_pmo t:%d pm:%p lvl:%d",
           dst_pmo->t, dst_pmo->pm, dst_pmo->lvl);
  eu_trace("src_pmo t:%d pm:%p lvl:%d",
           src_pmo->t, src_pmo->pm, src_pmo->lvl);

  while(copied < len) {
    hpt_va_t dst_va = dst_va_base + copied;
    hpt_va_t src_va = src_va_base + copied;
    size_t to_copy;
    void *src, *dst;

    eu_trace("dst_va:0x%llx src_va:0x%llx", dst_va, src_va);

    EU_CHK( dst = hptw_checked_access_va(dst_ctx,
                                         dst_pmo,
                                         HPT_PROTS_W,
                                         dst_cpl,
                                         dst_va,
                                         len-copied,
                                         &to_copy));
    EU_CHK( src = hptw_checked_access_va(src_ctx,
                                         src_pmo,
                                         HPT_PROTS_R,
                                         src_cpl,
                                         src_va,
                                         to_copy,
                                         &to_copy));
    eu_trace("dst-ptr:%p src-ptr:%p to-copy:%d",
             dst, src, to_copy);

    memcpy(dst, src, to_copy);
    copied += to_copy;
  }

  eu_trace("hptw_checked_copy_va_to_va: returning");
  rv=0;
 out:
  return rv;
}

int hptw_checked_memset_va(const hptw_ctx_t *ctx,
                           const hpt_pmo_t *pmo,
                           hptw_cpl_t cpl,
                           hpt_va_t dst_va_base,
                           int c,
                           size_t len)
{
  size_t set=0;
  int rv=1;
  eu_trace("hptw_checked_memset_va entering");

  while(set < len) {
    hpt_va_t dst_va = dst_va_base + set;
    size_t to_set;
    void *dst;

    eu_trace("calling hptw_checked_access_va");
    EU_CHK(dst = hptw_checked_access_va(ctx,
                                        pmo,
                                        HPT_PROTS_W,
                                        cpl,
                                        dst_va,
                                        len-set,
                                        &to_set));
    eu_trace("got pointer %p, size %d", dst, to_set);
    memset(dst, c, to_set);
    set += to_set;
  }
  eu_trace("hptw_checked_memset_va returning");

  rv=0;
 out:
  return rv;
}

