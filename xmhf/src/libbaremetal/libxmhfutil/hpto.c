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

void hpt_pmo_set_pme_by_va(hpt_pmo_t *pmo, const hpt_pmeo_t *pmeo, hpt_va_t va)
{
  hpt_pm_set_pme_by_va(pmo->t, pmo->lvl, pmo->pm, va, pmeo->pme);
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
