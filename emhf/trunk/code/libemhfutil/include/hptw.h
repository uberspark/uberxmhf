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

#ifndef HPTW_H
#define HPTW_H

#include <hpt.h>

typedef enum {
  HPTW_CPL0=0,
  HPTW_CPL1=1,
  HPTW_CPL2=2,
  HPTW_CPL3=3,
} hptw_cpl_t;

typedef hpt_pa_t (*hpt_ptr2pa_t)(void *ctx, void *ptr); /* translate a referencable pointer to a physical address */
typedef void* (*hpt_pa2ptr_t)(void *ctx, hpt_pa_t pa, size_t sz, hpt_prot_t access_type, hptw_cpl_t cpl, size_t *avail_sz); /* translate a physical address to a referenceable pointer */
typedef void* (*hpt_get_zeroed_page_t)(void *ctx, size_t alignment, size_t sz);

typedef struct {
  hpt_get_zeroed_page_t gzp;
  void *gzp_ctx;
  hpt_pa2ptr_t pa2ptr;
  void *pa2ptr_ctx;
  hpt_ptr2pa_t ptr2pa;
  void *ptr2pa_ctx;
} hptw_ctx_t;

int hptw_insert_pmeo(const hptw_ctx_t *ctx,
                         hpt_pmo_t *pmo,
                         const hpt_pmeo_t *pmeo,
                         hpt_va_t va);

int hptw_get_pmo_alloc(hpt_pmo_t *pmo,
                           const hptw_ctx_t *ctx,
                           const hpt_pmo_t *pmo_root,
                           int end_lvl,
                           hpt_va_t va);

int hptw_insert_pmeo_alloc(const hptw_ctx_t *ctx,
                               hpt_pmo_t *pmo,
                               const hpt_pmeo_t *pmeo,
                               hpt_va_t va);

void hptw_get_pmo(hpt_pmo_t *pmo,
                      const hptw_ctx_t *ctx,
                      const hpt_pmo_t *pmo_root,
                      int end_lvl,
                      hpt_va_t va);

void hptw_get_pmeo(hpt_pmeo_t *pmeo,
                       const hptw_ctx_t *ctx,
                       const hpt_pmo_t *pmo,
                       int end_lvl,
                       hpt_va_t va);

bool hptw_next_lvl(const hptw_ctx_t *ctx, hpt_pmo_t *pmo, hpt_va_t va);

hpt_prot_t hptw_get_effective_prots(const hptw_ctx_t *ctx,
                                         const hpt_pmo_t *pmo_root,
                                         hpt_va_t va,
                                         bool *user_accessible);

void hptw_set_prot(hptw_ctx_t *ctx,
                        hpt_pmo_t *pmo_root,
                        hpt_va_t va,
                        hpt_prot_t prot);

hpt_pa_t hptw_va_to_pa(const hptw_ctx_t *ctx,
                            const hpt_pmo_t *pmo,
                            hpt_va_t va);

void* hptw_checked_access_va(const hptw_ctx_t *ctx,
                             const hpt_pmo_t *pmo_root,
                             hpt_prot_t access_type,
                             hptw_cpl_t cpl,
                             hpt_va_t va,
                             size_t requested_sz,
                             size_t *avail_sz);

int hptw_checked_copy_from_va(const hptw_ctx_t *ctx,
                              const hpt_pmo_t *pmo,
                              hptw_cpl_t cpl,
                              void *dst,
                              hpt_va_t src_va_base,
                              size_t len);

int hptw_checked_copy_to_va(const hptw_ctx_t *ctx,
                            const hpt_pmo_t *pmo,
                            hptw_cpl_t cpl,
                            hpt_va_t dst_va_base,
                            void *src,
                            size_t len);

int hptw_checked_copy_va_to_va(const hptw_ctx_t *dst_ctx,
                               const hpt_pmo_t *dst_pmo,
                               hptw_cpl_t dst_cpl,
                               hpt_va_t dst_va_base,
                               const hptw_ctx_t *src_ctx,
                               const hpt_pmo_t *src_pmo,
                               hptw_cpl_t src_cpl,
                               hpt_va_t src_va_base,
                               size_t len);

int hptw_checked_memset_va(const hptw_ctx_t *ctx,
                           const hpt_pmo_t *pmo,
                           hptw_cpl_t cpl,
                           hpt_va_t dst_va_base,
                           int c,
                           size_t len);
#endif
