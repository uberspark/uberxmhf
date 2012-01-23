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

/* inserts pme into the page map of level tgt_lvl containing va, allocating
 * maps if necessary. returns 0 on success, other on failure.
 * Will fail if one of the intermediate entries is a large page
 */
int hpt_walk_insert_pme_alloc(const hpt_walk_ctx_t *ctx, int lvl, hpt_pm_t pm, int tgt_lvl, hpt_va_t va, hpt_pme_t pme)
{
  int end_lvl=tgt_lvl;
  hpt_log_trace("hpt_walk_insert_pme_alloc: lvl:%d pm:%p tgt_lvl:%d va:%Lx pme:%Lx\n",
          lvl, pm, tgt_lvl, va, pme);
  {
    hpt_pmo_t pmo;
    hpt_pmo_t pmo_root = {
      .pm = pm,
      .lvl = lvl,
      .t = ctx->t,
    };
    if (hpt_walk_get_pmo_alloc(&pmo, ctx, &pmo_root, end_lvl, va)) {
      return 1;
    }
    pm = pmo.pm;
    end_lvl = pmo.lvl;
  }
  hpt_log_trace("hpt_walk_insert_pme_alloc: got pm:%x end_lvl:%d\n",
          (u32)pm, end_lvl);

  if(pm == NULL || tgt_lvl != end_lvl) {
    return 1;
  }
  hpt_pm_set_pme_by_va(ctx->t, tgt_lvl, pm, va, pme);
  return 0;
}

void hpt_walk_set_prot(hpt_walk_ctx_t *walk_ctx, hpt_pm_t pm, int pm_lvl, hpt_va_t va, hpt_prot_t prot)
{
  hpt_pmo_t pmo_start = {
    .pm = pm,
    .lvl = pm_lvl,
    .t = walk_ctx->t,
  };
  hpt_pmo_t pmo;
  hpt_pmeo_t pmeo;
  hpt_pme_t pme;
  int end_pm_lvl=1;

  hpt_walk_get_pmo(&pmo, walk_ctx, &pmo_start, end_pm_lvl, va);
  end_pm_lvl = pmo.lvl;
  pm = pmo.pm;

  assert(pm != NULL);
  assert(end_pm_lvl==1); /* FIXME we don't handle large pages */

  pme = hpt_pm_get_pme_by_va(walk_ctx->t, end_pm_lvl, pm, va);
  pme = hpt_pme_setprot(walk_ctx->t, end_pm_lvl, pme, prot);
  hpt_pm_set_pme_by_va(walk_ctx->t, end_pm_lvl, pm, va, pme);
}

void hpt_walk_set_prots(hpt_walk_ctx_t *walk_ctx,
                        hpt_pm_t pm,
                        int pm_lvl,
                        hpt_va_t vas[],
                        size_t num_vas,
                        hpt_prot_t prot)
{
  size_t i;
  for(i=0; i<num_vas; i++) {
    hpt_walk_set_prot(walk_ctx, pm, pm_lvl, vas[i], prot);
  }
}

/* inserts pme into the page map of level tgt_lvl containing va.
 * fails if tgt_lvl is not allocated.
 */
int hpt_walk_insert_pme(const hpt_walk_ctx_t *ctx, int lvl, hpt_pm_t pm, int tgt_lvl, hpt_va_t va, hpt_pme_t pme)
{
  int end_lvl=tgt_lvl;
  hpt_log_trace("hpt_walk_insert_pme_alloc: lvl:%d pm:%x tgt_lvl:%d va:%Lx pme:%Lx\n",
                lvl, (u32)pm, tgt_lvl, va, pme);

  {
    hpt_pmo_t pmo;
    hpt_pmo_t start_pmo = {
      .pm = pm,
      .lvl = lvl,
      .t = ctx->t,
    };
    hpt_walk_get_pmo(&pmo, ctx, &start_pmo, end_lvl, va);
    pm = pmo.pm;
    end_lvl = pmo.lvl;
  }

  hpt_log_trace("hpt_walk_insert_pme: got pm:%x end_lvl:%d\n",
                (u32)pm, end_lvl);

  if(pm == NULL || tgt_lvl != end_lvl) {
    return 1;
  }

  hpt_pm_set_pme_by_va(ctx->t, tgt_lvl, pm, va, pme);
  return 0;
}
