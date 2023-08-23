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

#include <hptw_emhf.h>
#include <hpt_emhf.h>
#include <tv_log.h>

static hpt_pa_t hptw_emhf_host_ctx_ptr2pa(void *vctx, void *ptr)
{
  (void)vctx;
  return hva2spa(ptr);
}

static void* hptw_emhf_host_ctx_pa2ptr(void *vctx, hpt_pa_t spa, size_t sz, hpt_prot_t access_type, hptw_cpl_t cpl, size_t *avail_sz)
{
  (void)vctx;
  (void)access_type;
  (void)cpl;
  *avail_sz = sz;
  return spa2hva(spa);
}

static void* hptw_emhf_host_ctx_gzp(void *vctx, size_t alignment, size_t sz)
{
  hptw_emhf_host_ctx_t *ctx = vctx;
  pagelist_t *pl = ctx->pl;
  HALT_ON_ERRORCOND(pl != NULL);
  HALT_ON_ERRORCOND(PAGE_SIZE_4K % alignment == 0);
  HALT_ON_ERRORCOND(sz <= PAGE_SIZE_4K);
  return pagelist_get_zeroedpage(pl);
}

/* Context for EPT paging */
int hptw_emhf_host_ctx_init(hptw_emhf_host_ctx_t *ctx, hpt_pa_t root_pa, hpt_type_t t, pagelist_t *pl)
{
  *ctx = (hptw_emhf_host_ctx_t) {
    .super = (hptw_ctx_t) {
      .ptr2pa = hptw_emhf_host_ctx_ptr2pa,
      .pa2ptr = hptw_emhf_host_ctx_pa2ptr,
      .gzp = hptw_emhf_host_ctx_gzp,
      .root_pa = root_pa,
      .t = t,
    },
    .lower = (hptw_ctx_t) {
      .ptr2pa = NULL,
      .pa2ptr = NULL,
      .gzp = NULL,
      .root_pa = 0,
      .t = HPT_TYPE_INVALID,
    },
    .pl = pl,
  };
  return 0;
}

static hpt_pa_t hptw_emhf_host_nested01_ctx_ptr2pa(void *vctx, void *ptr)
{
  (void)vctx;
  (void)ptr;
  HALT_ON_ERRORCOND(0 && "Not supported");
  return 0;
}

static void* hptw_emhf_host_nested12_ctx_pa2ptr(void *vctx, hpt_pa_t gpa, size_t sz, hpt_prot_t access_type, hptw_cpl_t cpl, size_t *avail_sz)
{
  hptw_emhf_host_ctx_t *ctx = vctx;
  HALT_ON_ERRORCOND(ctx);

  return hptw_checked_access_va(&ctx->lower,
                                access_type,
                                cpl,
                                gpa,
                                sz,
                                avail_sz);
}

static void* hptw_emhf_host_nested01_ctx_gzp(void *vctx, size_t alignment, size_t sz)
{
  (void)vctx;
  (void)alignment;
  (void)sz;
  HALT_ON_ERRORCOND(0 && "Not supported");
  return NULL;
}

int hptw_emhf_host_nested_ctx_init(hptw_emhf_host_ctx_t *ctx, hpt_pa_t root_pa01, hpt_pa_t root_pa12, hpt_type_t t, pagelist_t *pl)
{
  *ctx = (hptw_emhf_host_ctx_t) {
    .super = (hptw_ctx_t) {
      .ptr2pa = hptw_emhf_host_ctx_ptr2pa,
      .pa2ptr = hptw_emhf_host_nested12_ctx_pa2ptr,
      .gzp = hptw_emhf_host_ctx_gzp,
      .root_pa = root_pa12,
      .t = t,
    },
    .lower = (hptw_ctx_t) {
      .ptr2pa = hptw_emhf_host_nested01_ctx_ptr2pa,
      .pa2ptr = hptw_emhf_host_ctx_pa2ptr,
      .gzp = hptw_emhf_host_nested01_ctx_gzp,
      .root_pa = root_pa01,
      .t = t,
    },
    .pl = pl,
  };
  return 0;
}

static hpt_pa_t hptw_emhf_checked_guest_ctx_ptr2pa(void __attribute__((unused)) *ctx, void *ptr)
{
  return hva2gpa(ptr);
}

static void* hptw_emhf_checked_guest_ctx_pa2ptr(void *vctx, hpt_pa_t gpa, size_t sz, hpt_prot_t access_type, hptw_cpl_t cpl, size_t *avail_sz)
{
  hptw_emhf_checked_guest_ctx_t *ctx = vctx;
  HALT_ON_ERRORCOND(ctx);

  return hptw_checked_access_va(&ctx->hptw_host_ctx.super,
                                access_type,
                                cpl,
                                gpa,
                                sz,
                                avail_sz);
}

static void* hptw_emhf_checked_guest_ctx_gzp(void *vctx, size_t alignment, size_t sz)
{
  hptw_emhf_checked_guest_ctx_t *ctx = vctx;
  pagelist_t *pl = ctx->pl;
  HALT_ON_ERRORCOND(pl != NULL);
  HALT_ON_ERRORCOND(PAGE_SIZE_4K % alignment == 0);
  HALT_ON_ERRORCOND(sz <= PAGE_SIZE_4K);
  return pagelist_get_zeroedpage(pl);
}

/* Context for guest paging (e.g. guest CR3) */
int hptw_emhf_checked_guest_ctx_init(hptw_emhf_checked_guest_ctx_t *ctx,
                                     hpt_pa_t root_pa,
                                     hpt_type_t t,
                                     hptw_cpl_t cpl,
                                     const hptw_emhf_host_ctx_t *host_ctx,
                                     pagelist_t *pl)
{
  /* FIXME: check that guest root is accessible in host pts here? */

  *ctx = (hptw_emhf_checked_guest_ctx_t) {
    .super = (hptw_ctx_t) {
      .ptr2pa = hptw_emhf_checked_guest_ctx_ptr2pa,
      .pa2ptr = hptw_emhf_checked_guest_ctx_pa2ptr,
      .gzp = hptw_emhf_checked_guest_ctx_gzp,

      .root_pa = root_pa,
      .t = t,
    },
    .cpl = cpl,
    .hptw_host_ctx = *host_ctx,
    .pl = pl,
  };

  return 0;
}

/* Always return EPT01 */
int hptw_emhf_host_l1_ctx_init_of_vcpu(hptw_emhf_host_ctx_t *rv, VCPU *vcpu)
{
  hpt_pa_t root_pa;
  hpt_type_t t;

  t = hpt_emhf_get_hpt_type( vcpu);
  root_pa = hva2spa( hpt_emhf_get_root_pm( vcpu));

  hptw_emhf_host_ctx_init( rv, root_pa, t, NULL);
  return 0;
}

/*
 * Return EPT01 when in L1, return EPT02 when in L2
 *
 * Note: for L2, the context is built using 2D page table walk: EPT12 + EPT01.
 * For function calls like hptw_va_to_pa(), hptw_get_pmeo(), and
 * hptw_checked_get_pmeo(), L1 physical address / entry is returned, not L0.
 */
int hptw_emhf_host_ctx_init_of_vcpu(hptw_emhf_host_ctx_t *rv, VCPU *vcpu)
{
  hpt_pa_t root_pa;
  hpt_type_t t;
  hpt_pa_t root_pa12;

  t = hpt_emhf_get_hpt_type( vcpu);
  root_pa = hva2spa( hpt_emhf_get_root_pm( vcpu));

  // TODO: use xmhf_nested_arch_x86vmx_access_ept02() to increase performance
  // However, this may require changing the structure of HPT library.
  root_pa12 = hpt_emhf_get_l1l2_root_pm_pa(vcpu);
  if (root_pa12 != HPTW_EMHF_EPT12_INVALID) {
    hptw_emhf_host_nested_ctx_init(rv, root_pa, root_pa12, t, NULL);
    return 0;
  }

  hptw_emhf_host_ctx_init( rv, root_pa, t, NULL);
  return 0;
}

/* static int construct_checked_walk_ctx(VCPU *vcpu, checked_guest_walk_ctx_t *rv) */
int hptw_emhf_checked_guest_ctx_init_of_vcpu(hptw_emhf_checked_guest_ctx_t *rv, VCPU *vcpu)
{
  int err=1;
  hptw_emhf_host_ctx_t host_ctx;
  hpt_pa_t root_pa;
  hpt_type_t t;

  root_pa = hpt_emhf_get_guest_root_pm_pa( vcpu);
  t = hpt_emhf_get_guest_hpt_type( vcpu);

  EU_CHKN( hptw_emhf_host_ctx_init_of_vcpu( &host_ctx, vcpu));
  EU_CHKN( hptw_emhf_checked_guest_ctx_init( rv,
                                             root_pa,
                                             t,
                                             HPTW_CPL3, /* FIXME - extract cpl from vcpu */
                                             &host_ctx,
                                             NULL));

  err = 0;
 out:
  return err;
}
