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

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'f */
/* tab-width:2      */
/* End:             */
