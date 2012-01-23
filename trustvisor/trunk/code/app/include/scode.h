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

/* scode.h - Module specific definitions
 * Written for TrustVisor by Ning Qu and Mark Luk
 * Edited by Zongwei Zhou for EMHF project
 */

#ifndef __SCODE_H_
#define __SCODE_H_

#include <emhf.h> 

#include <pages.h>

#include <trustvisor.h>
#include <crypto_init.h>
#include <tv_utpm.h> /* formerly utpm.h */

#include <hpto.h>
#include <hpt_emhf.h>	/* from libemhfutil */

/* XXX TEMP */
#define CHK(x) ASSERT(x)
#define CHK_RV(x) ASSERT(!(x))

#define MAX_REGPAGES_NUM 300

/* bits 0 to 2 of stored pte's store the section type */
#define SCODE_PTE_TYPE_MASK (0x7ull)
#define SCODE_PTE_TYPE_GET(pte)    ((pte) & SCODE_PTE_TYPE_MASK)
#define SCODE_PTE_TYPE_SET(pte, t) (((pte) & ~SCODE_PTE_TYPE_MASK) | t)

/* 
 * definition for scode whitelist 
 * */
/* max size of memory that holds scode state */
#define  WHITELIST_LIMIT 8*1024

/* in order to support 4GB memory */
#define  PFN_BITMAP_LIMIT 512*1024
#define  PFN_BITMAP_2M_LIMIT 2*1024

/* TODO: separate perf ctrs from scode.* */
extern perf_ctr_t g_tv_perf_ctrs[];
extern char *g_tv_perf_ctr_strings[];
#define TV_PERF_CTR_NPF 0
#define TV_PERF_CTR_SWITCH_SCODE 1
#define TV_PERF_CTR_SWITCH_REGULAR 2
#define TV_PERF_CTR_SAFEMALLOC 3
#define TV_PERF_CTR_MARSHALL 4
#define	TV_PERF_CTR_EXPOSE_ARCH 5
#define TV_PERF_CTR_NESTED_SWITCH_SCODE 6
/* insert new counters here, and update count below */
#define TV_PERF_CTRS_COUNT 7

typedef struct {
  hpt_va_t reg_gva;
  hpt_va_t pal_gva;
  size_t size;
  hpt_prot_t pal_prot;
  hpt_prot_t reg_prot;
  u32 section_type;
} tv_pal_section_int_t;

/* scode state struct */
typedef struct whitelist_entry{
  u64 gcr3; 
  u32 id;
  u32 grsp;		/* guest reguar stack */
  u32 gssp;		/* guest sensitive code stack */
  u32 gss_size;   /* guest sensitive code stack page number */
  u32 entry_v; /* entry point virtual address */
  u32 entry_p; /* entry point physical address */
  u32 return_v; /* return point virtual address */

  u32 gpmp;     /* guest parameter page address */
  u32 gpm_size; /* guest parameter page number */
  u32 gpm_num;  /* guest parameter number */

  tv_pal_section_int_t sections[TV_MAX_SECTIONS];
  size_t sections_num;

  struct tv_pal_sections scode_info; /* scode_info struct for registration function inpu */
  struct tv_pal_params params_info; /* param info struct */
  pte_t* scode_pages; /* registered pte's (copied from guest page tables and additional info added) */
  u32 scode_size; /* scode size */

  pte_t * pte_page;  /* holder for guest page table entry to access scode and GDT */
  u32 pte_size;	/* total size of all PTE pages */
#ifdef __MP_VERSION__
  u32 pal_running_lock; /* PAL running lock */
  u32 pal_running_vcpu_id; /* the cpu that is running this PAL */
#endif

  /* Micro-TPM related */
  utpm_master_state_t utpm;

  /* pal page tables */
  pagelist_t *gpl;
  pagelist_t *npl;
  hpt_walk_ctx_t hpt_nested_walk_ctx;
  hpt_walk_ctx_t hpt_guest_walk_ctx;
  hpt_pmo_t pal_npt_root;
  hpt_pmo_t pal_gpt_root;
  hpt_pmo_t reg_gpt_root;
  u64 pal_gcr3;
} __attribute__ ((packed)) whitelist_entry_t;


/* template page table context */
extern hpt_walk_ctx_t hpt_nested_walk_ctx;
extern hpt_walk_ctx_t hpt_guest_walk_ctx;

/* nested paging handlers (hpt) */
void hpt_insert_pal_pmes(VCPU *vcpu,
                         hpt_walk_ctx_t *walk_ctx,
                         hpt_pm_t pal_pm,
                         int pal_pm_lvl,
                         gpa_t gpas[],
                         size_t num_gpas);
void hpt_walk_set_prots(hpt_walk_ctx_t *walk_ctx,
                        hpt_pm_t pm,
                        int pm_lvl,
                        gpa_t gpas[],
                        size_t num_gpas,
                        hpt_prot_t prot);
void hpt_nested_set_prot(VCPU * vcpu, u64 gpaddr);
void hpt_nested_clear_prot(VCPU * vcpu, u64 gpaddr);
void hpt_nested_switch_scode(VCPU * vcpu, pte_t *pte_pages, u32 size, pte_t *pte_page2, u32 size2);
void hpt_nested_switch_regular(VCPU * vcpu, pte_t *pte_page, u32 size, pte_t *pte_page2, u32 size2);
void hpt_nested_make_pt_unaccessible(pte_t *gpaddr_list, u32 gpaddr_count, pdpt_t npdp, u32 is_pal);
void hpt_nested_make_pt_accessible(pte_t *gpaddr_list, u32 gpaddr_count, u64 * npdp, u32 is_pal);
hpt_prot_t pal_prot_of_type(int type);
hpt_prot_t reg_prot_of_type(int type);

/* several help functions to access guest address space */
u16 get_16bit_aligned_value_from_guest(const hpt_walk_ctx_t *ctx, const hpt_pmo_t *root, u32 gvaddr);
u32 get_32bit_aligned_value_from_guest(const hpt_walk_ctx_t *ctx, const hpt_pmo_t *root, u32 gvaddr);
void put_32bit_aligned_value_to_guest(const hpt_walk_ctx_t *ctx, const hpt_pmo_t *root, u32 gvaddr, u32 value);

u16 get_16bit_aligned_value_from_current_guest(VCPU *vcpu, u32 gvaddr);
u32 get_32bit_aligned_value_from_current_guest(VCPU *vcpu, u32 gvaddr);
void put_32bit_aligned_value_to_current_guest(VCPU *vcpu, u32 gvaddr, u32 value);

/* guest paging handlers */
int guest_pt_copy(VCPU * vcpu, pte_t *pte_page, u32 gvaddr, u32 size, int type);
static inline gpa_t gpt_vaddr_to_paddr(const hpt_walk_ctx_t *ctx, const hpt_pmo_t *gpt_root, gva_t vaddr)
{
  return hpto_walk_va_to_pa(ctx, gpt_root, vaddr);
}
static inline gpa_t gpt_vaddr_to_paddr_current(VCPU *vcpu, gva_t vaddr)
{
  hpt_type_t t = (VCPU_gcr4(vcpu) & CR4_PAE) ? HPT_TYPE_PAE : HPT_TYPE_NORM;
  hpt_pmo_t root = {
    .pm = hpt_emhf_get_guest_root_pm(vcpu),
    .t = t,
    .lvl = hpt_root_lvl(t),
  };
  hpt_walk_ctx_t ctx = hpt_guest_walk_ctx;
  gpa_t rv;
  rv = hpto_walk_va_to_pa(&ctx, &root, vaddr);

  return rv;
}

#define  gpt_get_ptpages(vcpu, vaddr, pdp, pd, pt) guest_pt_walker_internal(vcpu, vaddr, pdp, pd, pt, NULL, NULL, NULL, NULL)
#define  gpt_get_ptentries(vcpu, vaddr, pdpe, pde, pte, is_pae) guest_pt_walker_internal(vcpu, vaddr, NULL, NULL, NULL, pdpe, pde, pte, is_pae)

u32 guest_pt_walker_internal(VCPU *vcpu, u32 vaddr, u64 *pdp, u64 *pd, u64 *pt, u64 *pdpe, u64 * pde, u64 * pte, u32 * is_pae);

bool nested_pt_range_has_reqd_prots(VCPU * vcpu,
                                    hpt_prot_t reqd_prots, bool reqd_user_accessible,
                                    gva_t vaddr, size_t size_bytes);
bool guest_pt_range_is_user_rw(VCPU * vcpu, gva_t vaddr, size_t page_num);

/* operations from hypervisor to guest paging */
void * __gpa2hva__(u32 gpaddr);

void copy_from_current_guest_UNCHECKED(VCPU * vcpu, void *dst, gva_t gvaddr, u32 len);
int copy_from_current_guest(VCPU * vcpu, void *dst, gva_t gvaddr, u32 len);

void copy_to_current_guest_UNCHECKED(VCPU * vcpu, gva_t gvaddr, void *src, u32 len);
int copy_to_current_guest(VCPU * vcpu, gva_t gvaddr, void *src, u32 len);

/* PAL operations (HPT) */
u32 hpt_scode_set_prot(VCPU *vcpu, pte_t *pte_pages, u32 size);
void hpt_scode_clear_prot(VCPU * vcpu, pte_t *pte_pages, u32 size);
u32 hpt_scode_switch_scode(VCPU * vcpu);
u32 hpt_scode_switch_regular(VCPU * vcpu);
u32 hpt_scode_npf(VCPU * vcpu, u32 gpaddr, u64 errorcode);
u32 scode_share(VCPU * vcpu, u32 scode_entry, u32 addr, u32 len);
u32 scode_share_ranges(VCPU * vcpu, u32 scode_entry, u32 gva_base[], u32 gva_len[], u32 count);

u32 scode_register(VCPU * vcpu, u32 scode_info, u32 scode_pm, u32 gventry);
u32 scode_unregister(VCPU * vcpu, u32 gvaddr);
void init_scode(VCPU * vcpu);

void scode_lend_section(hpt_pmo_t* reg_npmo_root, hpt_walk_ctx_t *reg_npm_ctx,
                        hpt_pmo_t* reg_gpmo_root, hpt_walk_ctx_t *reg_gpm_ctx,
                        hpt_pmo_t* pal_npmo_root, hpt_walk_ctx_t *pal_npm_ctx,
                        hpt_pmo_t* pal_gpmo_root, hpt_walk_ctx_t *pal_gpm_ctx,
                        const tv_pal_section_int_t *section);
void scode_return_section(hpt_pmo_t* reg_npmo_root, hpt_walk_ctx_t *reg_npm_ctx,
                          hpt_pmo_t* pal_npmo_root, hpt_walk_ctx_t *pal_npm_ctx,
                          hpt_pmo_t* pal_gpmo_root, hpt_walk_ctx_t *pal_gpm_ctx,
                          const tv_pal_section_int_t *section);

void scode_clone_gdt(gva_t gdtr_base, size_t gdtr_lim,
                     hpt_pmo_t* reg_gpmo_root, hpt_walk_ctx_t *reg_gpm_ctx,
                     hpt_pmo_t* pal_gpmo_root, hpt_walk_ctx_t *pal_gpm_ctx,
                     pagelist_t *pl
                     );

#endif /* __SCODE_H_ */

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:nil */
/* c-basic-offset:2 */
/* End:             */
