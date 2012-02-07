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

/* nested_pt.c routines for handling nested page tables
 * Written for TrustVisor by Arvind Seshadri and Ning Qu
 *
 * Edited by Zongwei Zhou for EMHF/TrustVisor project
 *
 * EPT or NPT page table operations
 * guest page table operations
 */
#include <emhf.h> 
#include <malloc.h>
#include  "./include/scode.h"
#include <pages.h>

#include <tv_log.h>

/* ********************************* */
/* HPT related NPT operations */
/* ********************************* */

hpt_prot_t pal_prot_of_type(int type)
{
  switch(type) {
  case TV_PAL_SECTION_CODE:
    return HPT_PROTS_RX;
    break;
  case TV_PAL_SECTION_SHARED_CODE:
    return HPT_PROTS_RX;
    break;
  case TV_PAL_SECTION_DATA:
    return HPT_PROTS_RWX;
    break;
  case TV_PAL_SECTION_PARAM:
  case TV_PAL_SECTION_STACK:
    return HPT_PROTS_RW;
    break;
  case TV_PAL_SECTION_SHARED:
    return HPT_PROTS_RWX;
    break;
  case TV_PAL_SECTION_GUEST_PAGE_TABLES:
    return HPT_PROTS_RWX;
    break;
  }
  ASSERT(0); return 0; /* unreachable; appeases compiler */
}

hpt_prot_t reg_prot_of_type(int type)
{
  switch(type) {
  case TV_PAL_SECTION_CODE:
    return HPT_PROTS_NONE;
    break;
  case TV_PAL_SECTION_SHARED_CODE:
    return HPT_PROTS_RX;
    break;
  case TV_PAL_SECTION_DATA:
    return HPT_PROTS_NONE;
    break;
  case TV_PAL_SECTION_PARAM:
  case TV_PAL_SECTION_STACK:
    return HPT_PROTS_NONE;
    break;
  case TV_PAL_SECTION_SHARED:
    return HPT_PROTS_NONE;
    break;
  case TV_PAL_SECTION_GUEST_PAGE_TABLES:
    return HPT_PROTS_RWX;
    break;
  }
  ASSERT(0); return 0; /* unreachable; appeases compiler */
}

typedef struct {
  hpt_pmo_t guest_root;
  hptw_ctx_t guest_walk_ctx;
  hptw_cpl_t cpl;
} checked_guest_walk_ctx_t;

static int construct_checked_walk_ctx(VCPU *vcpu, checked_guest_walk_ctx_t *rv)
{
  int err=0;
  scode_guest_pa2ptr_ctx_t *guest_pa2ptr_ctx;

  memset(rv, 0, sizeof(*rv));

  EU_CHK(
         guest_pa2ptr_ctx = malloc(sizeof(*guest_pa2ptr_ctx)),
         err=1);

  hpt_emhf_get_root_pmo(vcpu, &guest_pa2ptr_ctx->host_pmo_root);
  guest_pa2ptr_ctx->host_walk_ctx = hpt_nested_walk_ctx;

  EU_CHKN(
          hpt_guest_walk_ctx_construct_vcpu(&rv->guest_walk_ctx, vcpu, NULL),
          err=2);

  hpt_emhf_get_guest_root_pmo(vcpu, &rv->guest_root);
  rv->cpl = HPTW_CPL3; /* FIXME - extract cpl from vcpu */
  
 out:
  if (err) {
    free(rv->guest_walk_ctx.pa2ptr_ctx);
  }
  return err;
}

static void destroy_checked_walk_ctx(checked_guest_walk_ctx_t *ctx)
{
  hpt_guest_walk_ctx_destroy(&ctx->guest_walk_ctx);
}

bool nested_pt_range_has_reqd_prots(VCPU * vcpu,
                                    hpt_prot_t reqd_prots, bool reqd_user_accessible,
                                    gva_t gva_base, size_t len)
{
  checked_guest_walk_ctx_t ctx;
  size_t checked=0;
  int err = 0;
  bool rv = true;

  EU_CHKN(
          construct_checked_walk_ctx(vcpu, &ctx),
          err=1);

  while(checked < len) {
    hpt_va_t gva = gva_base + checked;
    void *ptr;
    size_t size_checked;
    hptw_cpl_t cpl;

    cpl = reqd_user_accessible ? HPTW_CPL3 : HPTW_CPL0;

    EU_CHK(
           ptr = hptw_checked_access_va(&ctx.guest_walk_ctx,
                                        &ctx.guest_root,
                                        reqd_prots,
                                        cpl,
                                        gva,
                                        len-checked,
                                        &size_checked),
           rv=false);
    checked += size_checked;
  }
 out:
  assert(!err); /* FIXME */
  return rv;
}

bool guest_pt_range_is_user_rw(VCPU * vcpu, gva_t vaddr, size_t size_bytes)
{
  return nested_pt_range_has_reqd_prots(vcpu,
                                        HPT_PROTS_RW, true,
                                        vaddr, size_bytes);

}


/* several help functions to access guest address space */
u16 get_16bit_aligned_value_from_guest(const hptw_ctx_t *ctx, const hpt_pmo_t *root, u32 gvaddr)
{
  u32 gpaddr;
  ASSERT(!(gvaddr & 0x1));

  gpaddr = gpt_vaddr_to_paddr(ctx, root, gvaddr);
  return *((u16 *)gpa2hva(gpaddr));
}

u32 get_32bit_aligned_value_from_guest(const hptw_ctx_t *ctx, const hpt_pmo_t *root, u32 gvaddr)
{
  u32 gpaddr;
  ASSERT(!(gvaddr & 0x3));

  gpaddr = gpt_vaddr_to_paddr(ctx, root, gvaddr);
  return *((u32 *)gpa2hva(gpaddr));
}

void put_32bit_aligned_value_to_guest(const hptw_ctx_t *ctx, const hpt_pmo_t *root, u32 gvaddr, u32 value)
{
  u32 gpaddr;
  ASSERT(!(gvaddr & 0x3));
  
  gpaddr = gpt_vaddr_to_paddr(ctx, root, gvaddr);
  *((u32 *)gpa2hva(gpaddr)) = value;
}

/* several help functions to access guest address space */
u16 get_16bit_aligned_value_from_current_guest(VCPU *vcpu, u32 gvaddr)
{
  u32 gpaddr;
  ASSERT(!(gvaddr & 0x1));
  
  gpaddr = gpt_vaddr_to_paddr_current(vcpu, gvaddr);
  return *((u16 *)gpa2hva(gpaddr));
}

u32 get_32bit_aligned_value_from_current_guest(VCPU *vcpu, u32 gvaddr)
{
  u32 gpaddr;
  ASSERT(!(gvaddr & 0x3));
  
  gpaddr = gpt_vaddr_to_paddr_current(vcpu, gvaddr);
  return *((u32 *)gpa2hva(gpaddr));
}

void put_32bit_aligned_value_to_current_guest(VCPU *vcpu, u32 gvaddr, u32 value)
{
  u32 gpaddr;
  ASSERT(!(gvaddr & 0x3));

  gpaddr = gpt_vaddr_to_paddr_current(vcpu, gvaddr);
  *((u32 *)gpa2hva(gpaddr)) = value;
}


int copy_from_current_guest(VCPU * vcpu, void *dst, gva_t gvaddr, u32 len)
{
  checked_guest_walk_ctx_t ctx;
  int rv=0;

  EU_CHKN( construct_checked_walk_ctx(vcpu, &ctx),
           rv=1);

  EU_CHKN( hptw_checked_copy_from_va(&ctx.guest_walk_ctx, &ctx.guest_root, ctx.cpl, dst, gvaddr, len),
           rv=2);

 out:
  destroy_checked_walk_ctx(&ctx);
  return rv;
}

int copy_to_current_guest(VCPU * vcpu, gva_t gvaddr, void *src, u32 len)
{
  checked_guest_walk_ctx_t ctx;
  int rv=0;

  EU_CHKN( construct_checked_walk_ctx(vcpu, &ctx),
           rv=1);

  EU_CHKN( hptw_checked_copy_to_va(&ctx.guest_walk_ctx, &ctx.guest_root, ctx.cpl, gvaddr, src, len),
           rv = 2);

 out:
  destroy_checked_walk_ctx(&ctx);
  return rv;
}


/* clone pal's gdt from 'reg' gdt, and add to pal's guest page tables.
   gdt is allocted using passed-in-pl, whose pages should already be
   accessible to pal's nested page tables. XXX SECURITY need to build
   a trusted gdt instead. */
int scode_clone_gdt(VCPU *vcpu,
                    gva_t gdtr_base, size_t gdtr_lim,
                    hpt_pmo_t* pal_gpmo_root, hptw_ctx_t *pal_gpm_ctx,
                    pagelist_t *pl
                    )
{
  void *gdt_pal_page;
  u64 *gdt=NULL;
  size_t gdt_size = (gdtr_lim+1)*sizeof(*gdt);
  size_t gdt_page_offset = gdtr_base & MASKRANGE64(11, 0); /* XXX */
  gva_t gdt_reg_page_gva = gdtr_base & MASKRANGE64(63, 12); /* XXX */
  int err=1;

  eu_trace("scode_clone_gdt base:%x size:%d", gdtr_base, gdt_size);

  /* rest of fn assumes gdt is all on one page */
  EU_VERIFY((gdt_page_offset+gdt_size) <= PAGE_SIZE_4K); 

  EU_CHK( gdt_pal_page = pagelist_get_zeroedpage(pl));
  gdt = gdt_pal_page + gdt_page_offset;

  eu_trace("copying gdt from gva:%x to hva:%p", gdtr_base, gdt);
  EU_CHKN( copy_from_current_guest(vcpu, gdt, gdtr_base, gdt_size));

  /* add to guest page tables */
  {
    hpt_pmeo_t gdt_g_pmeo = { .t = pal_gpmo_root->t, .lvl = 1 };
    hpt_pa_t gdt_gpa;

    gdt_gpa = hva2gpa(gdt);

    eu_trace("mapping gdt into guest page tables");
    /* XXX SECURITY check to ensure we're not clobbering some existing
       mapping */
    /* add access to pal guest page tables */
    hpt_pmeo_set_address(&gdt_g_pmeo, gdt_gpa);
    hpt_pmeo_setprot(&gdt_g_pmeo, HPT_PROTS_RWX);
    EU_CHKN( hptw_insert_pmeo_alloc(pal_gpm_ctx,
                                    pal_gpmo_root,
                                    &gdt_g_pmeo,
                                    gdt_reg_page_gva));
  }

  err=0;
 out:
  return err;
}

/* lend a section of memory from a user-space process (on the
   commodity OS) to a pal */
void scode_lend_section(hpt_pmo_t* reg_npmo_root, hptw_ctx_t *reg_npm_ctx,
                        hpt_pmo_t* reg_gpmo_root, hptw_ctx_t *reg_gpm_ctx,
                        hpt_pmo_t* pal_npmo_root, hptw_ctx_t *pal_npm_ctx,
                        hpt_pmo_t* pal_gpmo_root, hptw_ctx_t *pal_gpm_ctx,
                        const tv_pal_section_int_t *section)
{
  size_t offset;
  int hpt_err;

  eu_trace("Mapping from %016llx to %016llx, size %u, pal_prot %u",
           section->reg_gva, section->pal_gva, section->size, (u32)section->pal_prot);
  
  /* XXX don't hard-code page size here. */
  /* XXX fail gracefully */
  ASSERT((section->size % PAGE_SIZE_4K) == 0); 

  for (offset=0; offset < section->size; offset += PAGE_SIZE_4K) {
    hpt_va_t page_reg_gva = section->reg_gva + offset;
    hpt_va_t page_pal_gva = section->pal_gva + offset;

    /* XXX we don't use hpt_va_t or hpt_pa_t for gpa's because these
       get used as both */
    u64 page_reg_gpa, page_pal_gpa; /* guest-physical-addresses */

    hpt_pmeo_t page_reg_gpmeo; /* reg's guest page-map-entry and lvl */
    hpt_pmeo_t page_pal_gpmeo; /* pal's guest page-map-entry and lvl */

    hpt_pmeo_t page_reg_npmeo; /* reg's nested page-map-entry and lvl */
    hpt_pmeo_t page_pal_npmeo; /* pal's nested page-map-entry and lvl */

    /* lock? quiesce? */

    hptw_get_pmeo(&page_reg_gpmeo,
                      reg_gpm_ctx,
                      reg_gpmo_root,
                      1,
                      page_reg_gva);
    eu_trace("got pme %016llx, level %d, type %d",
             page_reg_gpmeo.pme, page_reg_gpmeo.lvl, page_reg_gpmeo.t);
    ASSERT(page_reg_gpmeo.lvl==1); /* we don't handle large pages */
    page_reg_gpa = hpt_pmeo_get_address(&page_reg_gpmeo);

    hptw_get_pmeo(&page_reg_npmeo,
                      reg_npm_ctx,
                      reg_npmo_root,
                      1,
                      page_reg_gpa);
    ASSERT(page_reg_npmeo.lvl==1); /* we don't handle large pages */

    /* no reason to go with a different mapping */
    page_pal_gpa = page_reg_gpa;

    /* check that this VM is allowed to access this system-physical mem */
    {
      hpt_prot_t effective_prots;
      bool user_accessible=false;
      effective_prots = hptw_get_effective_prots(reg_npm_ctx,
                                                      reg_npmo_root,
                                                      page_reg_gpa,
                                                      &user_accessible);
      CHK((effective_prots & section->reg_prot) == section->reg_prot);
      CHK(user_accessible);
    }

    /* check that this guest process is allowed to access this guest-physical mem */
    {
      hpt_prot_t effective_prots;
      bool user_accessible=false;
      effective_prots = hptw_get_effective_prots(reg_gpm_ctx,
                                                      reg_gpmo_root,
                                                      page_reg_gva,
                                                      &user_accessible);
      eu_trace("got reg gpt prots:0x%x, user:%d",
               (u32)effective_prots, (int)user_accessible);
      CHK((effective_prots & section->pal_prot) == section->pal_prot);
      CHK(user_accessible);
    }

    /* check that the requested virtual address isn't already mapped
       into PAL's address space */
    {
      hpt_pmeo_t existing_pmeo;
      hptw_get_pmeo(&existing_pmeo,
                        pal_gpm_ctx,
                        pal_gpmo_root,
                        1,
                        page_pal_gva);
      CHK(!hpt_pmeo_is_present(&existing_pmeo));
    }

    /* revoke access from 'reg' VM */
    hpt_pmeo_setprot(&page_reg_npmeo, section->reg_prot);
    hpt_err = hptw_insert_pmeo(reg_npm_ctx,
                                   reg_npmo_root,
                                   &page_reg_npmeo,
                                   page_reg_gpa);
    CHK_RV(hpt_err);

    /* for simplicity, we don't bother removing from guest page
       tables. removing from nested page tables is sufficient */

    /* add access to pal guest page tables */
    page_pal_gpmeo = page_reg_gpmeo; /* XXX SECURITY should build from scratch */
    hpt_pmeo_set_address(&page_pal_gpmeo, page_pal_gpa);
    hpt_pmeo_setprot    (&page_pal_gpmeo, HPT_PROTS_RWX);
    hpt_err = hptw_insert_pmeo_alloc(pal_gpm_ctx,
                                         pal_gpmo_root,
                                         &page_pal_gpmeo,
                                         page_pal_gva);
    CHK_RV(hpt_err);

    /* add access to pal nested page tables */
    page_pal_npmeo = page_reg_npmeo;
    hpt_pmeo_setprot(&page_pal_npmeo, section->pal_prot);
    hpt_err = hptw_insert_pmeo_alloc(pal_npm_ctx,
                                         pal_npmo_root,
                                         &page_pal_npmeo,
                                         page_pal_gpa);
    CHK_RV(hpt_err);

    /* unlock? unquiesce? */
  }
}

/* lend a section of memory from a user-space process (on the
   commodity OS) to a pal.
   PRE: assumes section was already successfully lent using scode_lend_section
   PRE: assumes no concurrent access to page tables (e.g., quiesce other cpus)
*/
void scode_return_section(hpt_pmo_t* reg_npmo_root, hptw_ctx_t *reg_npm_ctx,
                          hpt_pmo_t* pal_npmo_root, hptw_ctx_t *pal_npm_ctx,
                          hpt_pmo_t* pal_gpmo_root, hptw_ctx_t *pal_gpm_ctx,
                          const tv_pal_section_int_t *section)
{
  size_t offset;

  for (offset=0; offset < section->size; offset += PAGE_SIZE_4K) {
    hpt_va_t page_pal_gva = section->pal_gva + offset;

    /* XXX we don't use hpt_va_t or hpt_pa_t for gpa's because these
       get used as both */
    u64 page_reg_gpa, page_pal_gpa; /* guest-physical-addresses */
    hpt_pmeo_t page_pal_gpmeo; /* pal's guest page-map-entry and lvl */

    hptw_get_pmeo(&page_pal_gpmeo,
                      pal_gpm_ctx,
                      pal_gpmo_root,
                      1,
                      page_pal_gva);
    ASSERT(page_pal_gpmeo.lvl==1); /* we don't handle large pages */
    page_pal_gpa = hpt_pmeo_get_address(&page_pal_gpmeo);

    /* lend_section always uses the same gpas between reg and pal */
    page_reg_gpa = page_pal_gpa;

    /* check that this pal VM is allowed to access this system-physical mem.
       we only check that it's readable; trustvisor-wide we maintain the invariant
       that a page is readable in a PAL's npt iff it is not readable in the guest npt
       or other PALs' npts.
    */
    {
      hpt_prot_t effective_prots;
      bool user_accessible=false;
      effective_prots = hptw_get_effective_prots(pal_npm_ctx,
                                                      pal_npmo_root,
                                                      page_pal_gpa,
                                                      &user_accessible);
      CHK(effective_prots & HPT_PROTS_R);
    }

    /* revoke access from 'pal' VM */
    hptw_set_prot(pal_npm_ctx,
                       pal_npmo_root,
                       page_pal_gpa,
                       HPT_PROTS_NONE);

    /* scode_lend_section leaves reg guest page tables intact, so no
       need to restore anything in them here. */

    /* revoke access from pal guest page tables */
    hptw_set_prot(pal_gpm_ctx,
                       pal_gpmo_root,
                       page_pal_gva,
                       HPT_PROTS_NONE);

    /* add access to reg nested page tables */
    hptw_set_prot(reg_npm_ctx,
                       reg_npmo_root,
                       page_reg_gpa,
                       HPT_PROTS_RWX);
  }
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:nil */
/* c-basic-offset:2 */
/* End:             */

