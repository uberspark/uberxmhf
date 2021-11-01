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

/* hpt.h - hypervisor page table abstraction
 * 
 * author - Jim Newsome (jnewsome@no-fuss.com)
 *
 * note: the HPT abstraction requires certain target interfaces to
 * be defined by a "provider". EMHF specific target interface
 * definitions live in hpt_emhf.h
 */

#ifndef HPT_H
#define HPT_H

#include <bitfield.h>
#include <stddef.h>
#include <assert.h>

typedef enum {
  HPT_TYPE_NORM=0, /* x86 'normal'\legacy */
  HPT_TYPE_PAE=1, /* Physical address extension */
  HPT_TYPE_LONG=2, /* AMD Long Mode */
  HPT_TYPE_EPT=3, /* Intel Extended Page Tables */

  HPT_TYPE_INVALID=4, /* same number as below intentionally; saves memory in static arrays */
  HPT_TYPE_NUM=4 /* dummy entry. must be last */
} hpt_type_t;

#define HPT_MAX_LEVEL 4

#define HPT_LVL_PT1 1
#define HPT_LVL_PD2 2
#define HPT_LVL_PDP3 3
#define HPT_LVL_PDPT3 3
#define HPT_LVL_PML4 4

typedef u64 hpt_pme_t; /* page map entry (any level) */
typedef hpt_pme_t* hpt_pm_t; /* page map (any level) */

/* NOTE- do not dereference directly.
   Some page table types use 32-bit entries instead
   of 64-bit. */

typedef u64 hpt_prot_t; /* pme protection flags type */
typedef u64 hpt_va_t; /* virtual address type */
typedef u64 hpt_pa_t; /* physical address type */

typedef struct {
  hpt_pm_t pm;
  hpt_type_t t;
  int lvl;
} hpt_pmo_t;

typedef struct {
  hpt_pme_t pme;
  hpt_type_t t;
  int lvl;
} hpt_pmeo_t;

#define HPT_UNUSED_ARGUMENT(x) (void)x

#define HPT_PM_SIZE 4096

/* page map sizes, in bytes. note that zero index is invalid. */
extern const u16 hpt_pm_sizes[HPT_TYPE_NUM][HPT_MAX_LEVEL+1];

/* page map sizes, in bytes. note that zero index is invalid. */
extern const u16 hpt_pm_alignments[HPT_TYPE_NUM][HPT_MAX_LEVEL+1];

/* high bit of va used to index into the page map of the given level.
 * we treat level '0' specially here, so that the low bit of the index
 * can consistently be found by looking up the entry for 'level-1'.
 */
extern const u8 hpt_va_idx_hi[HPT_TYPE_NUM][HPT_MAX_LEVEL+1];

extern const u8 hpt_type_max_lvl[HPT_TYPE_NUM];

size_t hpt_pm_size(hpt_type_t t, int lvl);

#include <hpt_consts.h> /* XXX - remove this once fn bodies are moved
                           into hpt.c */

/* Abstract protection flags. */
#define HPT_PROT_READ_BIT 0
#define HPT_PROT_WRITE_BIT 1
#define HPT_PROT_EXEC_BIT 2
#define HPT_PROT_READ_MASK (1ull<<HPT_PROT_READ_BIT)
#define HPT_PROT_WRITE_MASK (1ull<<HPT_PROT_WRITE_BIT)
#define HPT_PROT_EXEC_MASK (1ull<<HPT_PROT_EXEC_BIT)

#define HPT_PROTS_RWX (HPT_PROT_READ_MASK|HPT_PROT_WRITE_MASK|HPT_PROT_EXEC_MASK)
#define HPT_PROTS_RW (HPT_PROT_READ_MASK|HPT_PROT_WRITE_MASK)
#define HPT_PROTS_RX (HPT_PROT_READ_MASK|HPT_PROT_EXEC_MASK)
#define HPT_PROTS_R (HPT_PROT_READ_MASK)
#define HPT_PROTS_WX (HPT_PROT_WRITE_MASK|HPT_PROT_EXEC_MASK) /* never valid */
#define HPT_PROTS_W (HPT_PROT_WRITE_MASK) /* never valid */
#define HPT_PROTS_X (HPT_PROT_EXEC_MASK) /* never valid */
#define HPT_PROTS_NONE (0)

u64 hpt_cr3_set_address(hpt_type_t t, u64 cr3, hpt_pa_t a);
hpt_pa_t hpt_cr3_get_address(hpt_type_t t, u64 cr3);

u64 hpt_eptp_set_address(hpt_type_t t, u64 eptp, hpt_pa_t a);
hpt_pa_t hpt_eptp_get_address(hpt_type_t t, u64 eptp);

/* XXX move into hpt.c */
#ifndef MAX
#define MAX(x, y) (((y) > (x)) ? (y) : (x))
#endif
#ifndef MIN
#define MIN(x, y) (((y) < (x)) ? (y) : (x))
#endif

typedef enum {
  HPT_PMT_UC=0, HPT_PMT_WC=1, HPT_PMT_WT=4, HPT_PMT_WP=5, HPT_PMT_WB=6
} hpt_pmt_t;

/* assumes lvl is valid for the given type */
bool hpt_prot_is_valid(hpt_type_t t, int lvl, hpt_prot_t perms);

bool hpt_lvl_is_valid(hpt_type_t t, int lvl);
bool hpt_type_is_valid(hpt_type_t t);
int hpt_root_lvl(hpt_type_t t);

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
hpt_pa_t hpt_pmeo_va_to_pa(hpt_pmeo_t* pmeo, hpt_va_t va);
size_t hpt_pmeo_page_size_log_2(const hpt_pmeo_t *pmeo);
size_t hpt_pmeo_page_size(const hpt_pmeo_t *pmeo);
size_t hpt_remaining_on_page(const hpt_pmeo_t *pmeo, hpt_va_t va);

#endif
