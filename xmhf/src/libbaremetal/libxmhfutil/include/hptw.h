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

#ifndef HPTW_H
#define HPTW_H

#include <hpt.h>

typedef enum {
  HPTW_CPL0=0,
  HPTW_CPL1=1,
  HPTW_CPL2=2,
  HPTW_CPL3=3,
} hptw_cpl_t;

typedef hpt_pa_t (*hpt_ptr2pa_t)(void *self, void *ptr); /* translate a referencable pointer to a physical address */
typedef void* (*hpt_pa2ptr_t)(void *self, hpt_pa_t pa, size_t sz, hpt_prot_t access_type, hptw_cpl_t cpl, size_t *avail_sz); /* translate a physical address to a referenceable pointer */
typedef void* (*hpt_get_zeroed_page_t)(void *self, size_t alignment, size_t sz);

typedef struct {
  hpt_get_zeroed_page_t gzp;
  hpt_pa2ptr_t pa2ptr;
  hpt_ptr2pa_t ptr2pa;

  hpt_pa_t root_pa;
  hpt_type_t t;
} hptw_ctx_t;

int hptw_insert_pmeo( hptw_ctx_t *ctx,
                      const hpt_pmeo_t *pmeo,
                      hpt_va_t va);

int hptw_get_pmo_alloc( hpt_pmo_t *pmo,
                        hptw_ctx_t *ctx,
                        int end_lvl,
                        hpt_va_t va);

int hptw_insert_pmeo_alloc( hptw_ctx_t *ctx,
                            const hpt_pmeo_t *pmeo,
                            hpt_va_t va);

void hptw_get_pmo( hpt_pmo_t *pmo,
                   hptw_ctx_t *ctx,
                   int end_lvl,
                   hpt_va_t va);

void hptw_get_pmeo( hpt_pmeo_t *pmeo,
                    hptw_ctx_t *ctx,
                    int end_lvl,
                    hpt_va_t va);

/* tries to descend one level in the page table tree. returns true
 * if successful. in case of an exception, such as pa2ptr callback
 * failing, pmo is set to type HPT_INVALID.
 */
bool hptw_next_lvl( hptw_ctx_t *ctx, hpt_pmo_t *pmo, hpt_va_t va);

hpt_prot_t hptw_get_effective_prots( hptw_ctx_t *ctx,
                                     hpt_va_t va,
                                     bool *user_accessible);

void hptw_set_prot( hptw_ctx_t *ctx,
                    hpt_va_t va,
                    hpt_prot_t prot);

hpt_pa_t hptw_va_to_pa( hptw_ctx_t *ctx,
                        hpt_va_t va);

void* hptw_checked_access_va( hptw_ctx_t *ctx,
                              hpt_prot_t access_type,
                              hptw_cpl_t cpl,
                              hpt_va_t va,
                              size_t requested_sz,
                              size_t *avail_sz);

int hptw_checked_copy_from_va( hptw_ctx_t *ctx,
                               hptw_cpl_t cpl,
                               void *dst,
                               hpt_va_t src_va_base,
                               size_t len);

int hptw_checked_copy_to_va( hptw_ctx_t *ctx,
                             hptw_cpl_t cpl,
                             hpt_va_t dst_va_base,
                             void *src,
                             size_t len);

int hptw_checked_copy_va_to_va( hptw_ctx_t *dst_ctx,
                                hptw_cpl_t dst_cpl,
                                hpt_va_t dst_va_base,
                                hptw_ctx_t *src_ctx,
                                hptw_cpl_t src_cpl,
                                hpt_va_t src_va_base,
                                size_t len);

int hptw_checked_memset_va( hptw_ctx_t *ctx,
                            hptw_cpl_t cpl,
                            hpt_va_t dst_va_base,
                            int c,
                            size_t len);
#endif
