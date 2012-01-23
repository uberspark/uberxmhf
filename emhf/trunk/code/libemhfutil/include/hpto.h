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

#ifndef HPTO_H
#define HPTO_H

/* experimental "object-oriented" wrappers around hpt functions. idea
   is to make code a bit less noisy by bundling page-maps and
   page-map-entries with their level and type. consider adding to
   hpt */

#include <hpt.h>

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
hpt_pa_t hpt_pmeo_get_address(const hpt_pmeo_t *pmeo);
void hpt_pmeo_set_address(hpt_pmeo_t *pmeo, hpt_pa_t addr);
bool hpt_pmeo_is_present(const hpt_pmeo_t *pmeo);
bool hpt_pmeo_is_page(const hpt_pmeo_t *pmeo);
void hpt_pmeo_setprot(hpt_pmeo_t *pmeo, hpt_prot_t perms);
hpt_prot_t hpt_pmeo_getprot(const hpt_pmeo_t *pmeo);
bool hpt_pmeo_getuser(const hpt_pmeo_t *pmeo);
void hpt_pmeo_setuser(hpt_pmeo_t *pmeo, bool user);
void hpt_pm_get_pmeo_by_va(hpt_pmeo_t *pmeo, const hpt_pmo_t *pmo, hpt_va_t va);
void hpt_pmo_set_pme_by_va(hpt_pmo_t *pmo, const hpt_pmeo_t *pmeo, hpt_va_t va);
bool hptw_next_lvl(const hptw_ctx_t *ctx, hpt_pmo_t *pmo, hpt_va_t va);
hpt_prot_t hptw_get_effective_prots(const hptw_ctx_t *ctx,
                                         const hpt_pmo_t *pmo_root,
                                         hpt_va_t va,
                                         bool *user_accessible);
void hptw_set_prot(hptw_ctx_t *ctx,
                        hpt_pmo_t *pmo_root,
                        hpt_va_t va,
                        hpt_prot_t prot);
hpt_pa_t hpt_pmeo_va_to_pa(hpt_pmeo_t* pmeo, hpt_va_t va);
hpt_pa_t hptw_va_to_pa(const hptw_ctx_t *ctx,
                            const hpt_pmo_t *pmo,
                            hpt_va_t va);
size_t hpt_pmeo_page_size_log_2(const hpt_pmeo_t *pmeo);
size_t hpt_pmeo_page_size(const hpt_pmeo_t *pmeo);

size_t hpt_remaining_on_page(const hpt_pmeo_t *pmeo, hpt_va_t va);
void hptw_copy_from_guest(const hptw_ctx_t *ctx,
                         const hpt_pmo_t *pmo,
                         void *dst,
                         hpt_va_t src_va_base,
                         size_t len);
void hptw_copy_to_guest(const hptw_ctx_t *ctx,
                       const hpt_pmo_t *pmo,
                       hpt_va_t dst_va_base,
                       void *src,
                       size_t len);
void hptw_copy_guest_to_guest(const hptw_ctx_t *dst_ctx,
                             const hpt_pmo_t *dst_pmo,
                             hpt_va_t dst_va_base,
                             const hptw_ctx_t *src_ctx,
                             const hpt_pmo_t *src_pmo,
                             hpt_va_t src_va_base,
                             size_t len);

void hptw_memset_guest(const hptw_ctx_t *ctx,
                      const hpt_pmo_t *pmo,
                      hpt_va_t dst_va_base,
                      int c,
                      size_t len);


#endif
