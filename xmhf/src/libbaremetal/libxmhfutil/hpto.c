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
#include "hpt_internal.h"

/* Get the physical address (of page / page table) */
hpt_pa_t hpt_pmeo_get_address(const hpt_pmeo_t *pmeo)
{
  return hpt_pme_get_address(pmeo->t, pmeo->lvl, pmeo->pme);
}

/* Set the physical address (of page / page table) */
void hpt_pmeo_set_address(hpt_pmeo_t *pmeo, hpt_pa_t addr)
{
  pmeo->pme = hpt_pme_set_address(pmeo->t, pmeo->lvl, pmeo->pme, addr);
}

/* Get the present bit */
bool hpt_pmeo_is_present(const hpt_pmeo_t *pmeo)
{
  return hpt_pme_is_present(pmeo->t, pmeo->lvl, pmeo->pme);
}

/*
 * Set whether entry points to a page (otherwise, point to a page table).
 * For example, in 32-bit paging, when lvl = 2 (PDE), if is_page = true, then
 * PDE.PS is set to 1, and the entry points to a 4MB page. If is_page = false,
 * then PDE.PS is set to 0, and the entry points to a page table. When lvl = 1,
 * only is_page = true is allowed.
 */
void hpt_pmeo_set_page(hpt_pmeo_t *pmeo, bool is_page)
{
  pmeo->pme = hpt_pme_set_page(pmeo->t, pmeo->lvl, pmeo->pme, is_page);
}

/*
 * Check whether entry points to a page (otherwise, point to a page table).
 * For example, in 32-bit paging, when PDE.PS = 1, it points to a 4MB page
 * (this function returns true). When PDE.PS = 0, it points to a page table
 * (this function returns false).
 */
bool hpt_pmeo_is_page(const hpt_pmeo_t *pmeo)
{
  return hpt_pme_is_page(pmeo->t, pmeo->lvl, pmeo->pme);
}

/* Change the protection bits (R, W, X) */
void hpt_pmeo_setprot(hpt_pmeo_t *pmeo, hpt_prot_t perms)
{
  pmeo->pme = hpt_pme_setprot(pmeo->t, pmeo->lvl, pmeo->pme, perms);
}

/* Get the protection bits (R, W, X) */
hpt_prot_t hpt_pmeo_getprot(const hpt_pmeo_t *pmeo)
{
  return hpt_pme_getprot(pmeo->t, pmeo->lvl, pmeo->pme);
}

/* Set the memory type (e.g. uncached, write back) */
void hpt_pmeo_setcache(hpt_pmeo_t *pmeo, hpt_pmt_t pmt)
{
  pmeo->pme = hpt_pme_set_pmt(pmeo->t, pmeo->lvl, pmeo->pme, pmt);
}

/* Get the user / supervisor bit (U/S) */
bool hpt_pmeo_getuser(const hpt_pmeo_t *pmeo)
{
  return hpt_pme_getuser(pmeo->t, pmeo->lvl, pmeo->pme);
}

/* Change the user / supervisor bit (U/S) */
void hpt_pmeo_setuser(hpt_pmeo_t *pmeo, bool user)
{
  pmeo->pme = hpt_pme_setuser(pmeo->t, pmeo->lvl, pmeo->pme, user);
}

/* Get page table entry in page table (pm) using virtual address (va) */
void hpt_pm_get_pmeo_by_va(hpt_pmeo_t *pmeo, const hpt_pmo_t *pmo, hpt_va_t va)
{
  pmeo->t = pmo->t;
  pmeo->lvl = pmo->lvl;
  pmeo->pme = hpt_pm_get_pme_by_va(pmo->t, pmo->lvl, pmo->pm, va);
}

/* Set page table entry (pme) in page table (pm) using virtual address (va) */
void hpt_pmo_set_pme_by_va(hpt_pmo_t *pmo, const hpt_pmeo_t *pmeo, hpt_va_t va)
{
  hpt_pm_set_pme_by_va(pmo->t, pmo->lvl, pmo->pm, va, pmeo->pme);
}

/*
 * Get the physical address of virtual address (va), pmeo is the last level of
 * page table entry.
 * For example, in 32-bit paging with 4K pages, pmeo is the page table entry,
 * va=0x12345678, then pa=0xabcde678.
 */
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

/*
 * Get the log2 of size region controlled by the page map entry.
 * For example, in 32-bit paging, PDE's size is log(4M) = 22, PTE's size is
 * log(4K) = 12.
 */
size_t hpt_pmeo_page_size_log_2(const hpt_pmeo_t *pmeo)
{
  int offset_hi;
  offset_hi = hpt_va_idx_hi[pmeo->t][pmeo->lvl-1];
  return offset_hi+1;
}

/*
 * Get the size region controlled by the page map entry.
 * For example, in 32-bit paging, PDE's size 4M, PTE's size is 4K.
 */
size_t hpt_pmeo_page_size(const hpt_pmeo_t *pmeo)
{
  return 1 << hpt_pmeo_page_size_log_2(pmeo);
}

/*
 * Get the number of bytes from va to page boundary.
 * For example, in 32-bit paging with 4K pages, when va=0x12345678, this
 * function returns 0x1000 - 0x678 = 0x988.
 */
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
