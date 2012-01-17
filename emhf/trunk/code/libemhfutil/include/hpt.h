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

//#include "_types.h"
#include <bitfield.h>
#include <stddef.h>
#include <assert.h>

#ifndef hpt_log_trace
# define hpt_log_trace(fmt, args...) while(0)
#endif

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

typedef hpt_pa_t (*hpt_ptr2pa_t)(void *ctx, void *ptr); /* translate a referencable pointer to a physical address */
typedef void* (*hpt_pa2ptr_t)(void *ctx, hpt_pa_t pa); /* translate a physical address to a referenceable pointer */
typedef void* (*hpt_get_zeroed_page_t)(void *ctx, size_t alignment, size_t sz);
                       
typedef struct {
  hpt_type_t t;
  hpt_get_zeroed_page_t gzp;
  void *gzp_ctx;
  hpt_pa2ptr_t pa2ptr;
  void *pa2ptr_ctx;
  hpt_ptr2pa_t ptr2pa;
  void *ptr2pa_ctx;
} hpt_walk_ctx_t;

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
#define MAX(x, y) (((y) > (x)) ? (y) : (x))
#define MIN(x, y) (((y) < (x)) ? (y) : (x))

typedef enum {
  HPT_PMT_UC=0, HPT_PMT_WC=1, HPT_PMT_WT=4, HPT_PMT_WP=5, HPT_PMT_WB=6
} hpt_pmt_t;

/* assumes lvl is valid for the given type */
bool hpt_prot_is_valid(hpt_type_t t, int lvl, hpt_prot_t perms);

bool hpt_lvl_is_valid(hpt_type_t t, int lvl);
bool hpt_type_is_valid(hpt_type_t t);
int hpt_root_lvl(hpt_type_t t);

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

/* attempt to descend one level. on success, lvl and pm are set
   accordingly, and true is returned. on failure, lvl and pm are
   untouched and false is returned. */
bool hpt_walk_next_lvl(const hpt_walk_ctx_t *ctx, int *lvl, hpt_pm_t *pm, hpt_va_t va);

/* returns the lowest-level page map containing va, down to
 * end_lvl. end_lvl is set to the level of the returned page map.
 */
hpt_pm_t hpt_walk_get_pm(const hpt_walk_ctx_t *ctx, int lvl, hpt_pm_t pm, int *end_lvl, hpt_va_t va);

/* returns the lowest-level page map _entry_ containing va, down to
 * end_lvl. end_lvl is set to the level of the returned page map
 * containing the returned entry.
 */
hpt_pme_t hpt_walk_get_pme(const hpt_walk_ctx_t *ctx, int lvl, hpt_pm_t pm, int *end_lvl, hpt_va_t va);

/* returns the page map of level end_lvl containing va, allocating
   maps if necessary. Note that the end_lvl may be a higher level than requested
   if the address is mapped via a large page.
*/
hpt_pm_t hpt_walk_get_pm_alloc(const hpt_walk_ctx_t *ctx, int lvl, hpt_pm_t pm, int *end_lvl, hpt_va_t va);

/* inserts pme into the page map of level tgt_lvl containing va, allocating
 * maps if necessary. returns 0 on success, other on failure.
 * Will fail if one of the intermediate entries is a large page
 */
int hpt_walk_insert_pme_alloc(const hpt_walk_ctx_t *ctx, int lvl, hpt_pm_t pm, int tgt_lvl, hpt_va_t va, hpt_pme_t pme);

#endif
