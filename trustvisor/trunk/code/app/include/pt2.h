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

#ifndef PT2_H
#define PT2_H

#include <hpto.h>
#include <pages.h>

typedef struct {
  hpt_va_t reg_gva;
  hpt_va_t pal_gva;
  size_t size;
  hpt_prot_t pal_prot;
  hpt_prot_t reg_prot;
} section_t;

void scode_lend_section(hpt_pmo_t* reg_npmo_root, hpt_walk_ctx_t *reg_npm_ctx,
                        hpt_pmo_t* reg_gpmo_root, hpt_walk_ctx_t *reg_gpm_ctx,
                        hpt_pmo_t* pal_npmo_root, hpt_walk_ctx_t *pal_npm_ctx,
                        hpt_pmo_t* pal_gpmo_root, hpt_walk_ctx_t *pal_gpm_ctx,
                        const section_t *section);

void scode_clone_gdt(gva_t gdtr_base, size_t gdtr_lim,
                     hpt_pmo_t* reg_gpmo_root, hpt_walk_ctx_t *reg_gpm_ctx,
                     hpt_pmo_t* pal_gpmo_root, hpt_walk_ctx_t *pal_gpm_ctx,
                     pagelist_t *pl
                     );

void hpt_copy_from_guest(const hpt_walk_ctx_t *ctx,
                         const hpt_pmo_t *pmo,
                         void *dst,
                         hpt_va_t src_gva_base,
                         size_t len);
void hpt_copy_to_guest(const hpt_walk_ctx_t *ctx,
                       const hpt_pmo_t *pmo,
                       hpt_va_t dst_gva_base,
                       void *src,
                       size_t len);
void hpt_copy_guest_to_guest(const hpt_walk_ctx_t *dst_ctx,
                             const hpt_pmo_t *dst_pmo,
                             hpt_va_t dst_gva_base,
                             const hpt_walk_ctx_t *src_ctx,
                             const hpt_pmo_t *src_pmo,
                             hpt_va_t src_gva_base,
                             size_t len);

#endif
