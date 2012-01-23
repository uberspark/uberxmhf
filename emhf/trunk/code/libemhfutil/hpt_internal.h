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

#ifndef HPT_INTERNAL_H
#define HPT_INTERNAL_H

hpt_pme_t hpt_pme_setuser(hpt_type_t t, int lvl, hpt_pme_t entry, bool user_accessible);
bool hpt_pme_getuser(hpt_type_t t, int lvl, hpt_pme_t entry);

hpt_pme_t hpt_pme_setprot(hpt_type_t t, int lvl, hpt_pme_t entry, hpt_prot_t perms);
hpt_prot_t hpt_pme_getprot(hpt_type_t t, int lvl, hpt_pme_t entry);

hpt_pme_t hpt_pme_setunused(hpt_type_t t, int lvl, hpt_pme_t entry, int hi, int lo, hpt_pme_t val);
hpt_pme_t hpt_pme_getunused(hpt_type_t t, int lvl, hpt_pme_t entry, int hi, int lo);

bool hpt_pme_is_present(hpt_type_t t, int lvl, hpt_pme_t entry);

bool hpt_pme_is_page(hpt_type_t t, int lvl, hpt_pme_t entry);

hpt_pa_t hpt_pme_get_address(hpt_type_t t, int lvl, hpt_pme_t entry);

hpt_pme_t hpt_pme_set_address(hpt_type_t t, int lvl, hpt_pme_t entry, hpt_pa_t addr);

/* Assumes PAT register has default values */
hpt_pmt_t hpt_pme_get_pmt(hpt_type_t t, int lvl, hpt_pme_t pme);

/* Always clears PAT bit when applicable. */
hpt_pmt_t hpt_pme_set_pmt(hpt_type_t t, int lvl, hpt_pme_t pme, hpt_pmt_t pmt);

unsigned int hpt_get_pm_idx(hpt_type_t t, int lvl, hpt_va_t va);

hpt_pme_t hpt_pm_get_pme_by_idx(hpt_type_t t, int lvl, hpt_pm_t pm, int idx);
void hpt_pm_set_pme_by_idx(hpt_type_t t, int lvl, hpt_pm_t pm, int idx, hpt_pme_t pme);

hpt_pme_t hpt_pm_get_pme_by_va(hpt_type_t t, int lvl, hpt_pm_t pm, hpt_va_t va);
void hpt_pm_set_pme_by_va(hpt_type_t t, int lvl, hpt_pm_t pm, hpt_va_t va, hpt_pme_t pme);

#endif
