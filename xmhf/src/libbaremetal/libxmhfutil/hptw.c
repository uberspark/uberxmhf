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
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
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

/*
 * Get the root page map object (pmo) for context (ctx)
 * For example, in 32-bit paging it gives the PDE pointed to by CR3
 */
static int hptw_get_root( hptw_ctx_t *ctx, hpt_pmo_t *pmo)
{
  int lvl = hpt_type_max_lvl[ ctx->t];
  size_t pm_sz = hpt_pm_size( ctx->t, lvl);
  size_t avail;
  hpt_pm_t pm;
  int err = 1;

  pm = ctx->pa2ptr( ctx,
                    ctx->root_pa,
                    pm_sz,
                    HPT_PROTS_RW,
                    HPTW_CPL0,
                    &avail);
  EU_CHK( pm);
  EU_CHK( avail == pm_sz);

  *pmo = (hpt_pmo_t) {
    .t = ctx->t,
    .pm = pm,
    .lvl = lvl,
  };

  err = 0;
 out:
  return err;
}

/*
 * Insert page map entry object (pmeo) to context (ctx) at virtual address (va).
 * For example, in 32-bit paging, if pmeo is a page table entry (PTE), this
 * function will walk the page directory to find the page table, then change
 * the page table entry.
 */
int hptw_insert_pmeo(hptw_ctx_t *ctx,
                     const hpt_pmeo_t *pmeo,
                     hpt_va_t va)
{
  hpt_pmo_t pmo;
  int err = 1;

  hptw_get_pmo( &pmo, ctx, pmeo->lvl, va);
  EU_CHK( pmo.pm);
  EU_CHK( pmo.lvl == pmeo->lvl);

  hpt_pmo_set_pme_by_va( &pmo, pmeo, va);

  err = 0;
 out:
  return err;
}

/*
 * Get the page map object (pmo) at level (end_lvl) to context (ctx) at virtual
 * address (va), allocate empty page tables if needed.
 */
int hptw_get_pmo_alloc(hpt_pmo_t *pmo,
                       hptw_ctx_t *ctx,
                       int end_lvl,
                       hpt_va_t va)
{
  int err = 1;

  EU_CHKN( hptw_get_root( ctx, pmo));

  while(pmo->lvl > end_lvl) {
    hpt_pmeo_t pmeo;
    hpt_pm_get_pmeo_by_va(&pmeo, pmo, va);
    EU_CHK( !hpt_pmeo_is_page(&pmeo));

    if (!hpt_pmeo_is_present(&pmeo)) {
      hpt_pm_t pm;
      hpt_pmo_t new_pmo;

      EU_CHK_W( pm = ctx->gzp(ctx,
                              HPT_PM_SIZE, /*FIXME*/
                              hpt_pm_size(pmo->t, pmo->lvl-1)));
      new_pmo = (hpt_pmo_t) {
        .pm = pm,
        .lvl = pmo->lvl-1,
        .t = pmo->t,
      };
      hpt_pmeo_set_address(&pmeo, ctx->ptr2pa(ctx, new_pmo.pm));
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

  err = 0;
 out:
  return err;
}

/*
 * Insert page map entry object (pmeo) to context (ctx) at virtual address (va),
 * allocate empty page tables if needed.
 */
int hptw_insert_pmeo_alloc(hptw_ctx_t *ctx,
                           const hpt_pmeo_t *pmeo,
                           hpt_va_t va)
{
  hpt_pmo_t pmo;
  int err=1;

  EU_CHKN_W( hptw_get_pmo_alloc( &pmo, ctx, pmeo->lvl, va));
  EU_CHK( pmo.pm);
  EU_CHK( pmo.lvl == pmeo->lvl);

  hpt_pmo_set_pme_by_va(&pmo, pmeo, va);

  err=0;
 out:
  return err;
}

/*
 * Get the page map object (pmo) at level (end_lvl) to context (ctx) at virtual
 * address (va).
 */
void hptw_get_pmo( hpt_pmo_t *pmo,
                   hptw_ctx_t *ctx,
                   int end_lvl,
                   hpt_va_t va)
{
  int err=1;
  EU_CHKN( hptw_get_root( ctx, pmo));
  while (pmo->lvl > end_lvl
         && hptw_next_lvl(ctx, pmo, va));
  err=0;
 out:
  EU_VERIFYN( err); /* XXX */
}

/*
 * Get the page map entry object (pmeo) at level (end_lvl) to context (ctx) at
 * virtual address (va).
 */
void hptw_get_pmeo(hpt_pmeo_t *pmeo,
                   hptw_ctx_t *ctx,
                   int end_lvl,
                   hpt_va_t va)
{
  hpt_pmo_t end_pmo;
  hptw_get_pmo(&end_pmo, ctx, end_lvl, va);
  hpt_pm_get_pmeo_by_va(pmeo, &end_pmo, va);
}

/*
 * In context (ctx) when walking page table for virtual address (va), descent
 * the page map object (pmo) one level down.
 * For example, in 32-bit paging, if pmo points to a page directory when
 * calling this function, it will point to a page table after calling.
 */
bool hptw_next_lvl(hptw_ctx_t *ctx, hpt_pmo_t *pmo, hpt_va_t va)
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
    pmo->pm = ctx->pa2ptr(ctx, hpt_pmeo_get_address(&pmeo),
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

/*
 * Returns the effective protections for the given address, which is
 * the lowest permissions for the page walk. Also sets
 * *user_accessible if not NULL and if the virtual address is set
 * user-accessible.
 * According to hardware, this is usually the logical AND for the permission
 * bits in all levels of page map entries during the page table walk.
 */
hpt_prot_t hptw_get_effective_prots(hptw_ctx_t *ctx,
                                    hpt_va_t va,
                                    bool *user_accessible)
{
  hpt_prot_t prots_rv = HPT_PROTS_RWX;
  bool user_accessible_rv = true;
  hpt_pmo_t pmo;
  int err = 1;

  EU_CHKN( hptw_get_root( ctx, &pmo));

  do {
    hpt_pmeo_t pmeo;
    hpt_pm_get_pmeo_by_va(&pmeo, &pmo, va);
    prots_rv &= hpt_pmeo_getprot(&pmeo);
    user_accessible_rv = user_accessible_rv && hpt_pmeo_getuser(&pmeo);
  } while (hptw_next_lvl(ctx, &pmo, va));

  /* XXX should more clearly indicate an error */
  EU_CHK( pmo.t != HPT_TYPE_INVALID);

  if(user_accessible != NULL) {
    *user_accessible = user_accessible_rv;
  }

  err=0;
 out:
  if (err) {
    prots_rv = HPT_PROTS_NONE;
  }
  return prots_rv;
}

/* Set protection bits (prot) for a virtual address (va) in context (ctx) */
void hptw_set_prot(hptw_ctx_t *ctx,
                   hpt_va_t va,
                   hpt_prot_t prot)
{
  hpt_pmo_t pmo;
  hpt_pmeo_t pmeo;

  hptw_get_pmo (&pmo, ctx, 1, va);
  assert (pmo.pm);
  assert (pmo.lvl == 1);

  hpt_pm_get_pmeo_by_va (&pmeo, &pmo, va);
  hpt_pmeo_setprot (&pmeo, prot);
  hpt_pmo_set_pme_by_va (&pmo, &pmeo, va);
}

/*
 * Translate virtual address (va) in context (ctx) to physical address
 * (i.e. walk the page table in software).
 */
hpt_pa_t hptw_va_to_pa(hptw_ctx_t *ctx,
                       hpt_va_t va)
{
  hpt_pmeo_t pmeo;
  hptw_get_pmeo(&pmeo, ctx, 1, va);
  return hpt_pmeo_va_to_pa(&pmeo, va);
}

// translate guest paddr to system paddr (spa)
uintptr_t hptw_gpa_to_spa(hptw_ctx_t *ctx,
                       hpt_pa_t gpa)
{
  hpt_pa_t result = 0;

  result = hptw_va_to_pa(ctx, (hpt_va_t) gpa);
  return (uintptr_t)result;
}

/*
 * Access virtual address (va) in context (ctx) in software.
 * return value is the physical address that can be accessed by the caller.
 * requested_sz is the size caller wants to access.
 * avail_sz is the size available in the same page.
 * If avail_sz < requested_sz, the caller needs to call this function again.
 */
void* hptw_access_va(hptw_ctx_t *ctx,
                     hpt_va_t va,
                     size_t requested_sz,
                     size_t *avail_sz)
{
  hpt_pmeo_t pmeo;
  hpt_pa_t pa;

  hptw_get_pmeo(&pmeo, ctx, 1, va);

  pa = hpt_pmeo_va_to_pa(&pmeo, va);
  *avail_sz = MIN(requested_sz, hpt_remaining_on_page(&pmeo, pa));

  return ctx->pa2ptr(ctx, pa,
                     *avail_sz, HPT_PROTS_R, HPTW_CPL0, avail_sz);
}

/*
 * Get the page map entry object (pmeo) to context (ctx) at virtual address
 * (va). Also perform access check using access_type and cpl.
 * Return 0 if successful, 1 if failed (e.g. invalid permission).
 * access_type and cpl are used to check permissions when accessing va.
 * pmeo is undefined when this function returns 1.
 */
int hptw_checked_get_pmeo(hpt_pmeo_t *pmeo,
                          hptw_ctx_t *ctx,
                          hpt_prot_t access_type,
                          hptw_cpl_t cpl,
                          hpt_va_t va)
{
  hpt_pmo_t pmo;

  EU_CHKN( hptw_get_root( ctx, &pmo));

  eu_trace("va:0x%llx access_type %lld cpl:%d",
           va, access_type, cpl);

  do {
    eu_trace("pmo t:%d pm:%p lvl:%d",
             pmo.t, pmo.pm, pmo.lvl);
    hpt_pm_get_pmeo_by_va( pmeo, &pmo, va);
    EU_CHK_W(((access_type & hpt_pmeo_getprot(pmeo)) == access_type)
           && (cpl == HPTW_CPL0 || hpt_pmeo_getuser(pmeo)),
           eu_warn_e("req-priv:%lld req-cpl:%d priv:%lld user-accessible:%d",
                    access_type, cpl, hpt_pmeo_getprot(pmeo), hpt_pmeo_getuser(pmeo)));
  } while (hptw_next_lvl(ctx, &pmo, va));

  EU_CHK( pmo.t != HPT_TYPE_INVALID);

  EU_CHK( hpt_pmeo_is_present(pmeo));

  /* exiting loop means hptw_next_lvl failed, which means either the
   * current pmeo is a page, or the current pmeo is not present.
   * however, we should have already returned if not present, so pmeo
   * must be a page */
  EU_VERIFY(hpt_pmeo_is_page(pmeo));

  return 0;

 out:
  return 1;
}

/*
 * Access virtual address (va) in context (ctx) in software. Return NULL when
 * error (e.g. invalid permission).
 * access_type and cpl are used to check permissions when accessing va.
 * return value is the physical address that can be accessed by the caller.
 * requested_sz is the size caller wants to access.
 * avail_sz is the size available in the same page.
 * If avail_sz < requested_sz, the caller needs to call this function again.
 */
void* hptw_checked_access_va(hptw_ctx_t *ctx,
                             hpt_prot_t access_type,
                             hptw_cpl_t cpl,
                             hpt_va_t va,
                             size_t requested_sz,
                             size_t *avail_sz)
{
  hpt_pmeo_t pmeo;
  hpt_pa_t pa;
  void *rv=NULL;
  *avail_sz=0;

  EU_CHKN_W(hptw_checked_get_pmeo(&pmeo, ctx, access_type, cpl, va));

  pa = hpt_pmeo_va_to_pa(&pmeo, va);
  *avail_sz = MIN(requested_sz, hpt_remaining_on_page(&pmeo, pa));
  eu_trace("got pa:%llx sz:%d", pa, *avail_sz);
  rv = ctx->pa2ptr(ctx, pa,
                   *avail_sz, access_type, cpl, avail_sz);

 out:
  return rv;
}

/*
 * Memory copy from virtual address (src_va_base) to physical address (dst),
 * assuming privilege level at (cpl) when reading from source.
 * Return 0 if successful, 1 if failed.
 */
int hptw_checked_copy_from_va(hptw_ctx_t *ctx,
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

    src = hptw_checked_access_va(ctx, HPT_PROTS_R, cpl, src_va, len-copied, &to_copy);
    if(!src) {
      return 1;
    }
    memcpy(dst+copied, src, to_copy);
    copied += to_copy;
  }
  return 0;
}

/*
 * Memory copy from physical address (src) to virtual address (dst_va_base),
 * assuming privilege level at (cpl) when writing to destination.
 * Return 0 if successful, 1 if failed.
 */
int hptw_checked_copy_to_va(hptw_ctx_t *ctx,
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

    dst = hptw_checked_access_va(ctx, HPT_PROTS_W, cpl, dst_va, len-copied, &to_copy);
    if (!dst) {
      return 1;
    }
    memcpy(dst, src+copied, to_copy);
    copied += to_copy;
  }
  return 0;
}

/*
 * Memory copy from virtual address (src_va_base) to virtual address
 * (dst_va_base), assuming privilege level at (cpl) when reading / writing.
 * Return 0 if successful, 1 if failed.
 */
int hptw_checked_copy_va_to_va(hptw_ctx_t *dst_ctx,
                               hptw_cpl_t dst_cpl,
                               hpt_va_t dst_va_base,
                               hptw_ctx_t *src_ctx,
                               hptw_cpl_t src_cpl,
                               hpt_va_t src_va_base,
                               size_t len)
{
  size_t copied=0;
  int rv=1;

  while(copied < len) {
    hpt_va_t dst_va = dst_va_base + copied;
    hpt_va_t src_va = src_va_base + copied;
    size_t to_copy;
    void *src, *dst;

    eu_trace("dst_va:0x%llx src_va:0x%llx", dst_va, src_va);

    EU_CHK( dst = hptw_checked_access_va(dst_ctx,
                                         HPT_PROTS_W,
                                         dst_cpl,
                                         dst_va,
                                         len-copied,
                                         &to_copy));
    EU_CHK( src = hptw_checked_access_va(src_ctx,
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

/*
 * Set memory for virtual address (dst_va_base), assuming privilege level at
 * (cpl) when reading / writing.
 * Return 0 if successful, 1 if failed.
 */
int hptw_checked_memset_va(hptw_ctx_t *ctx,
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
