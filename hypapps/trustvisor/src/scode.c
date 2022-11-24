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

/* scode.c routines to handle all scode loading and unloading, also
 * whitelist, hash value verification for both shadow paging and nested
 * paging.
 * Written for TrustVisor by Ning Qu, Zongwei Zhou, and Yanlin Li
 * Edited for TrustVisor on EMHF by Zongwei Zhou
 */

#include <xmhf.h>

#include <scode.h>
#include <malloc.h>
#include <tv_utpm.h> /* formerly utpm.h */
#include <random.h>
#include <crypto_init.h>

#include <tv_log.h>
#include <hptw_emhf.h>

/* #define EU_DOWNCAST(vctx, t) assert(((t)vctx)->magic == t ## _MAGIC), (t)vctx */

hpt_pmo_t g_reg_npmo_root;
hptw_emhf_host_ctx_t g_hptw_reg_host_ctx;

/* this is the return address we push onto the stack when entering the
   pal. We return to the reg world on a nested page fault on
   instruction fetch of this address */
#define RETURN_FROM_PAL_ADDRESS 0x00000004

/* whitelist of all approved sensitive code regions */
/* whitelist_max and *whitelist is set up by BSP, no need to apply lock
 * whitelist_size will only be updated in scode_register() and scode_unreg(), no need to apply lock
 *
 * scode_whitelist entry is created in scode_register(), and cleaned up in scode_unregister()
 * no need to apply lock on it during those time
 *
 * scode_whitelist entry can also be edited during PAL running(during context switch),
 * However, one PAL can only be run on the CPU where the registration is done,
 * which means there is no possibility that multiple CPU will run a same PAL simultaneously,
 * thus no need to apply lock to whitelist entry.
 * */
whitelist_entry_t *whitelist=NULL;
size_t whitelist_size=0, whitelist_max=0;

perf_ctr_t g_tv_perf_ctrs[TV_PERF_CTRS_COUNT];
char *g_tv_perf_ctr_strings[] = {
  "npf", "switch_scode", "switch_regular", "safemalloc", "marshall", "expose_arch", "nested_switch_scode"
}; /* careful to keep this consistent with actual macros */

/* This two bitmaps are only updated in scode_register() and scode_unreg(), no need to apply lock */
/* bitmap of all physical page numer containing sensitive code */
u8 * scode_pfn_bitmap;
/* bitmap helps to maintain the physical pages of sensitive code
 * in one 2M physical page range
 */
u16 * scode_pfn_bitmap_2M;

/* identify which scode are running on every CPU, -1 for not running any scode */
/* each CPU has its own scode_curr value, no need to apply a lock on it */
int * scode_curr = NULL;

void scode_release_all_shared_pages(VCPU *vcpu, whitelist_entry_t* entry);

/* search scode in whitelist */
int scode_in_list(u64 gcr3, uintptr_t gvaddr, u32 g64)
{
  size_t i, j;

  for (i = 0; i < whitelist_max; i ++)
    {
      hpt_type_t t = whitelist[i].hptw_pal_checked_guest_ctx.super.t;
      if ((hpt_cr3_get_address(t, gcr3) == whitelist[i].gcr3) &&
          (g64 == whitelist[i].g64)) {
        for( j=0 ; j<(u32)(whitelist[i].scode_info.num_sections) ; j++ )  {
          if( (gvaddr >= whitelist[i].scode_info.sections[j].start_addr) &&
              (gvaddr < ((whitelist[i].scode_info.sections[j].start_addr)+((whitelist[i].scode_info.sections[j].page_num)<<PAGE_SHIFT_4K)))  )  {
            eu_trace("find gvaddr %#lx in scode %d section No.%d", gvaddr, i, j);
            return i;
          }
        }
      }
    }
#if !defined(__LDN_TV_INTEGRATION__)
  eu_trace("no matching scode found for gvaddr %#lx!", gvaddr);
#endif //__LDN_TV_INTEGRATION__
  return -1;
}

static whitelist_entry_t* find_scode_by_entry(u64 gcr3, uintptr_t gv_entry, u32 g64)
{
  size_t i;

  for (i = 0; i < whitelist_max; i ++)
    {
      /* find scode with correct cr3 and entry point */
      hpt_type_t t = whitelist[i].hptw_pal_checked_guest_ctx.super.t;
      if ((whitelist[i].gcr3 == hpt_cr3_get_address(t, gcr3)) &&
          (g64 == whitelist[i].g64) &&
          (whitelist[i].entry_v == gv_entry))
        return &whitelist[i];
    }
  return NULL;
}

int scode_measure_section(utpm_master_state_t *utpm,
                          whitelist_entry_t *wle,
                          const tv_pal_section_int_t *section)
{
  hash_state ctx;
  TPM_DIGEST sha1sum;
  int rv=1;

  EU_CHKN( sha1_init( &ctx));

  /* always measure the section type, which determines permissions and
     how the section is used. */
  EU_CHKN( sha1_process( &ctx, (const uint8_t*)&section->section_type, sizeof(section->section_type)));

  /* measure the address where the section is mapped. this prevents,
     for example, that a section is mapped with a different alignment
     to change the effective entry point, or switch some static data
     for other static data, etc. */
  /* XXX we currently don't do this for PARAM and STACK sections,
     though it wouldn't be a bad idea to do so. this will break
     existing client code, though, which dynamically allocates those
     sections and doesn't request a fixed location to map into the
     pal's virtual address space.
  */
  if (section->section_type != TV_PAL_SECTION_STACK
      && section->section_type != TV_PAL_SECTION_PARAM) {
    EU_CHKN( sha1_process( &ctx, (const uint8_t*)&section->pal_gva, sizeof(section->pal_gva)));
  }

  /* measure section size. not clear that this is strictly necessary,
     since giving a pal more memory shouldn't hurt anything, and less
     memory should result in no worse than the pal crashing, but seems
     like good hygiene. */
  EU_CHKN( sha1_process( &ctx, (const uint8_t*)&section->size, sizeof(section->size)));

  /* measure contents. we could consider making this optional for,
     e.g., PARAM and STACK sections, but seems like good hygiene to
     always do it. client ought to ensure that those sections are
     consistent (e.g., 0'd). an alternative to consider is to enforce
     that the hypervisor either measures or zeroes each section.*/
  {
    size_t measured=0;

    while(measured < section->size) {
      size_t to_measure;
      uint8_t *ptr=NULL;

      /* we just constructed these page tables, so in principle the
       * additional checks here should be unnecessary. leaving them in
       * to avoid potential future TOCTTOU vulnerabilities.
       */
      EU_VERIFY( ptr = hptw_checked_access_va( &wle->hptw_pal_checked_guest_ctx.super,
                                               HPT_PROTS_R,
                                               HPTW_CPL3,
                                               section->pal_gva + measured,
                                               section->size - measured,
                                               &to_measure));

      EU_CHKN( sha1_process( &ctx, ptr, to_measure));
      measured += to_measure;
    }
  }

  EU_CHKN( sha1_done( &ctx, sha1sum.value));

#ifdef __DRT__
  /* extend pcr 0 */
  utpm_extend(&sha1sum, utpm, 0);
#else /* !__DRT__ */
  (void) utpm;  // unused
#endif /* __DRT__ */

  rv=0;
 out:
  return rv;
}

int scode_measure_sections(utpm_master_state_t *utpm,
                           whitelist_entry_t *wle)
{
  size_t i;
  int err=0;

  for(i=0; i < wle->sections_num; i++) {
    err = scode_measure_section(utpm, wle, &wle->sections[i]);
    if (err) {
      return err;
    }
  }

  return 0;
}


/* initialize all the scode related variables and buffers */
void init_scode(VCPU * vcpu)
{
  size_t inum, max;
  (void)vcpu;

  /* initialize perf counters. this needs to happen before anythings gets profiled
   * to prevent deadlock.
   */
  {
    int j;
    for(j=0; j<TV_PERF_CTRS_COUNT; j++) {
      perf_ctr_init(&g_tv_perf_ctrs[j]);
    }
  }

  /* initialize heap memory */
  mem_init();

  whitelist = malloc(WHITELIST_LIMIT);
  eu_trace("alloc %dKB mem for scode_list at %lx!", (WHITELIST_LIMIT/1024), (unsigned long)whitelist);
  scode_pfn_bitmap = (unsigned char *)malloc(PFN_BITMAP_LIMIT);
  eu_trace("alloc %dKB mem for pfn_bitmap at %lx!", (PFN_BITMAP_LIMIT/1024), (unsigned long)scode_pfn_bitmap);
  scode_pfn_bitmap_2M = (unsigned short *)malloc(PFN_BITMAP_2M_LIMIT);
  eu_trace("alloc %dKB mem for pfn_bitmap_2M at %lx!", (PFN_BITMAP_LIMIT/1024), (unsigned long)scode_pfn_bitmap_2M);

  memset(whitelist, 0, WHITELIST_LIMIT);
  memset(scode_pfn_bitmap, 0, PFN_BITMAP_LIMIT);
  memset(scode_pfn_bitmap_2M, 0, PFN_BITMAP_2M_LIMIT);

  whitelist_size = 0;
  whitelist_max = WHITELIST_LIMIT / sizeof(whitelist_entry_t);
  eu_trace("whitelist max = %d!", whitelist_max);

  /* init scode_curr struct
   * NOTE that cpu_lapic_id could be bigger than midtable_numentries */
  max = 0;
  for( inum=0 ; inum < g_midtable_numentries ; inum++ )  {
    if ( g_midtable[inum].cpu_lapic_id > max)
      max = g_midtable[inum].cpu_lapic_id;
  }
  scode_curr = malloc((max+1) * sizeof(*scode_curr));
  memset(scode_curr, 0xFF, ((max+1) * sizeof(*scode_curr)));

#ifdef __DRT__
  /* After upgrading to tboot 1.10.5, need to call tpm_detect() */
  if (get_tpm_fp() == NULL) {
    HALT_ON_ERRORCOND(tpm_detect());
  }

  /* init PRNG and long-term crypto keys */
  EU_VERIFYN(trustvisor_master_crypto_init());
  eu_trace("trustvisor_master_crypto_init successful.");
#else /* !__DRT__ */
  eu_trace("DEVELOPMENT ONLY: skipping trustvisor_master_crypto_init().");
#endif /* __DRT__ */
}

/* parse scode paramter info ( scode registration input) */
int parse_params_info(VCPU * vcpu, struct tv_pal_params* pm_info, uintptr_t pm_addr)
{
  size_t i, num;
  uintptr_t addr;
  int rv=1;

  /* get number of parameters */
  EU_CHKN( copy_from_current_guest(vcpu,
                                   &pm_info->num_params,
                                   pm_addr,
                                   sizeof(pm_info->num_params)));
  num = pm_info->num_params;

  eu_trace("pm_info %#x, # of parameters is %d", pm_addr, num);
  EU_CHK( num <= TV_MAX_PARAMS);

  addr = pm_addr + offsetof(struct tv_pal_params, params);
  EU_CHKN( copy_from_current_guest(vcpu,
                                   &pm_info->params[0],
                                   addr,
                                   sizeof(pm_info->params[0]) * num));

  for (i = 0; i < num; i++) {
    eu_trace("parameter %d type %d size %ld", i, pm_info->params[i].type, pm_info->params[i].size);
  }

  rv=0;
out:
  return rv;
}

int memsect_info_copy_from_guest(VCPU * vcpu, struct tv_pal_sections *ps_scode_info, uintptr_t gva_scode_info)
{
  size_t gva_scode_info_offset = 0;
  int rv=1;

  /* get number of sections */
  EU_CHKN( copy_from_current_guest(vcpu,
                                   &ps_scode_info->num_sections,
                                   gva_scode_info,
                                   sizeof(ps_scode_info->num_sections)));

  gva_scode_info_offset = offsetof(struct tv_pal_sections, sections);
  eu_trace("scode_info addr %x, # of section is %d", gva_scode_info, ps_scode_info->num_sections);

  /* copy array of section descriptors */
  EU_CHK( ps_scode_info->num_sections <= TV_MAX_SECTIONS);

  EU_CHKN( copy_from_current_guest(vcpu,
                                   &(ps_scode_info->sections[0]),
                                   gva_scode_info+gva_scode_info_offset,
                                   ps_scode_info->num_sections*sizeof(ps_scode_info->sections[0])));

  rv=0;
 out:
  if(rv) {
    eu_err("failed with params: ps_scode_info:%p gva_scode_info:%#x", ps_scode_info, gva_scode_info);
  }
  return rv;
}

/* parse scode sections info (scode registration input) */
int memsect_info_register(VCPU * vcpu, struct tv_pal_sections *ps_scode_info, whitelist_entry_t * wle)
{
  size_t i;
  int is_get_param, is_get_stack;
  int type;
  uintptr_t size, start;
  int rv=1;

  (void)vcpu;

  /* parse section type, start address and size */
  is_get_param=0;
  is_get_stack=0;
  for (i = 0; i < ps_scode_info->num_sections; i++) {
    size = ps_scode_info->sections[i].page_num;
    type = ps_scode_info->sections[i].type;
    start = ps_scode_info->sections[i].start_addr;

    /* make sure the addr is 4kb page aligned */
    EU_CHK( PAGE_ALIGNED_4K(start));

    switch ( type )  {
    case TV_PAL_SECTION_PARAM :
      {
        /* set param page num and addr */
        if (!is_get_param) {
          wle->gpm_size=size;
          wle->gpmp=start+0x10;
          is_get_param=1;
        }
      }
      break;
    case TV_PAL_SECTION_STACK :
      {
        /* set stack page num and addr */
        if (!is_get_stack) {
          wle->gss_size=size;
          wle->gssp=start+(size<<PAGE_SHIFT_4K)-0x10;
          is_get_stack=1;
        }
      }
      break;
    default :
      break;
    }
    eu_trace("section %d type %d addr %#lx size %ld",i, type, start, size);
  }

  rv=0;
 out:
  return rv;
}


/* register scode in whitelist */
u64 scode_register(VCPU *vcpu, u64 scode_info, u64 scode_pm, u64 gventry)
{
  size_t i;
  whitelist_entry_t whitelist_new;
  u64 gcr3;
  hpt_pmo_t pal_npmo_root, pal_gpmo_root;
  hptw_emhf_checked_guest_ctx_t reg_guest_walk_ctx;
  u64 rv=1;

  /* set all CPUs to use the same 'reg' nested page tables,
     and set up a corresponding hpt_pmo.
  */
  /* XXX would make more sense to do this in init_scode, but there
     seems to be a race condition with all cores simultaneously trying
     to set up their EPTs and call xmhf_app_main.
  */
  {
    static bool did_change_root_mappings=false;

    if (!did_change_root_mappings) {
      hpt_emhf_get_root_pmo(vcpu, &g_reg_npmo_root);
      hptw_emhf_host_ctx_init_of_vcpu( &g_hptw_reg_host_ctx, vcpu);
#ifdef __MP_VERSION__
      {
        size_t i;
        for( i=0 ; i<g_midtable_numentries ; i++ )  {
          eu_trace("cpu %d setting root pm from %p to %p",
                  i,
                  hpt_emhf_get_root_pm((VCPU *)(g_midtable[i].vcpu_vaddr_ptr)),
                  g_reg_npmo_root.pm);
          hpt_emhf_set_root_pm((VCPU *)(g_midtable[i].vcpu_vaddr_ptr),
                               g_reg_npmo_root.pm);
        }
      }
#endif
      did_change_root_mappings = true;
    }
  }

  EU_CHKN( hptw_emhf_checked_guest_ctx_init_of_vcpu( &reg_guest_walk_ctx, vcpu));

  gcr3 = VCPU_gcr3(vcpu);

  eu_trace("*** scode register ***");

  EU_CHK( whitelist_size < whitelist_max);

  eu_trace("CPU(0x%02x): add to whitelist,  scode_info %#lx, scode_pm %#lx, gventry %#lx", vcpu->id, scode_info, scode_pm, gventry);

  /* ATTN: we should assign a ID for each registered sensitive code
   * so we know what to verify each time
   */
  whitelist_new.id = 0;
  whitelist_new.g64 = VCPU_g64(vcpu);
  whitelist_new.gcr3 = gcr3; /* Will clear lower bits for CR3 later */
  whitelist_new.grsp = (uintptr_t)-1;

  /* store scode entry point */
  whitelist_new.entry_v = gventry;
  whitelist_new.entry_p = hptw_va_to_pa( &reg_guest_walk_ctx.super, gventry);
  eu_trace("CR3 value is %#llx, entry point vaddr is %#lx, paddr is %#lx", gcr3, whitelist_new.entry_v, whitelist_new.entry_p);

  /* parse parameter structure */
  EU_CHKN( parse_params_info(vcpu, &(whitelist_new.params_info), scode_pm));

  whitelist_new.gpm_num = whitelist_new.params_info.num_params;
  /* register scode sections into whitelist entry */
  EU_CHKN( memsect_info_copy_from_guest(vcpu, &(whitelist_new.scode_info), scode_info));
  EU_CHKN( memsect_info_register(vcpu, &(whitelist_new.scode_info), &whitelist_new));

  EU_CHK( whitelist_new.npl = malloc(sizeof(pagelist_t)));
  pagelist_init(whitelist_new.npl);

  EU_CHK( whitelist_new.gpl = malloc(sizeof(pagelist_t)));
  pagelist_init(whitelist_new.gpl);

  whitelist_new.reg_gpt_root_pa = hpt_emhf_get_guest_root_pm_pa( vcpu);
  whitelist_new.reg_gpt_type = hpt_emhf_get_guest_hpt_type( vcpu);
  pal_npmo_root = (hpt_pmo_t) {
    .t = g_reg_npmo_root.t,
    .lvl = g_reg_npmo_root.lvl,
    .pm = pagelist_get_zeroedpage(whitelist_new.npl),
  };
  pal_gpmo_root = (hpt_pmo_t) {
    .t = whitelist_new.reg_gpt_type,
    .lvl = hpt_root_lvl( whitelist_new.reg_gpt_type),
    .pm = pagelist_get_zeroedpage( whitelist_new.gpl),
  };

  EU_CHKN( hptw_emhf_host_ctx_init( &whitelist_new.hptw_pal_host_ctx,
                                    hva2spa( pal_npmo_root.pm),
                                    pal_npmo_root.t,
                                    whitelist_new.npl));

  EU_CHKN( hptw_emhf_checked_guest_ctx_init( &whitelist_new.hptw_pal_checked_guest_ctx,
                                             hva2gpa( pal_gpmo_root.pm),
                                             pal_gpmo_root.t,
                                             HPTW_CPL3,
                                             &whitelist_new.hptw_pal_host_ctx,
                                             whitelist_new.gpl));

  /* add all gpl pages to pal's nested page tables, ensuring that
     the guest page tables allocated from it will be accessible to the
     pal */
  /* XXX breaks pagelist abstraction. will break if pagelist ever dynamically
     allocates more buffers. consider doing this on-demand inside pal's gzp fn instead. */
  eu_trace("adding gpl to pal's npt:");
  for (i=0; i < whitelist_new.gpl->num_allocd; i++) {
    hpt_pmeo_t pmeo = {
      .pme = 0,
      .t = pal_npmo_root.t,
      .lvl = 1,
    };
    void *page = whitelist_new.gpl->page_base + i*PAGE_SIZE_4K;
    hpt_pmeo_setprot(&pmeo, HPT_PROTS_RWX);
    hpt_pmeo_setuser(&pmeo, true);
    hpt_pmeo_set_address(&pmeo, hva2spa(page));
    EU_CHKN( hptw_insert_pmeo_alloc( &whitelist_new.hptw_pal_host_ctx.super,
                                     &pmeo,
                                     hva2gpa(page)));
  }

  eu_trace("adding sections to pal's npts and gpts:");
  /* map each requested section into the pal */
  whitelist_new.sections_num = whitelist_new.scode_info.num_sections;
  for (i=0; i<whitelist_new.scode_info.num_sections; i++) {
    whitelist_new.sections[i] = (tv_pal_section_int_t) {
      .reg_gva = whitelist_new.scode_info.sections[i].start_addr,
      .pal_gva = whitelist_new.scode_info.sections[i].start_addr,
      .size = whitelist_new.scode_info.sections[i].page_num * PAGE_SIZE_4K,
      .pal_prot = pal_prot_of_type(whitelist_new.scode_info.sections[i].type),
      .reg_prot = reg_prot_of_type(whitelist_new.scode_info.sections[i].type),
      .section_type = whitelist_new.scode_info.sections[i].type,
    };
    scode_lend_section( &g_hptw_reg_host_ctx.super,
                        &reg_guest_walk_ctx.super,
                        &whitelist_new.hptw_pal_host_ctx.super,
                        &whitelist_new.hptw_pal_checked_guest_ctx.super,
                        &whitelist_new.sections[i]);
  }

  /* clone gdt */
  /* eu_warn("skipping scode_clone_gdt"); */
  /* EU_CHKN( scode_clone_gdt(vcpu, */
  /*                          VCPU_gdtr_base(vcpu), VCPU_gdtr_limit(vcpu), */
  /*                          &pal_gpmo_root, &whitelist_new.hpt_guest_walk_ctx, */
  /*                          whitelist_new.gpl)); */

  /* we add the page containing the designated return address to the
     guest page tables, but not the nested page tables. failure to
     add to the guest page tables will cause a triple fault in the
     guest. */
  {
    hpt_pmeo_t pmeo = {
      .pme = 0,
      .t = pal_gpmo_root.t,
      .lvl = 1,
    };
    hpt_pmeo_setprot(&pmeo, HPT_PROTS_RX);
    hpt_pmeo_setuser(&pmeo, true);
    /* the gpa address here shouldn't matter, so long as it's one not
       accessible by the pal. we'll also set that to the sentinel
       return address value
    */
    hpt_pmeo_set_address(&pmeo, RETURN_FROM_PAL_ADDRESS);

    eu_trace("generated pme for return gva address %x: lvl:%d %llx",
            RETURN_FROM_PAL_ADDRESS, pmeo.lvl, pmeo.pme);
    EU_CHKN( hptw_insert_pmeo_alloc( &whitelist_new.hptw_pal_checked_guest_ctx.super,
                                     &pmeo,
                                     RETURN_FROM_PAL_ADDRESS));
  }

  /* Clear lower bits for CR3 */
  whitelist_new.gcr3 = hpt_cr3_get_address( whitelist_new.hptw_pal_checked_guest_ctx.super.t,
                                            whitelist_new.gcr3);

  whitelist_new.pal_gcr3 = hpt_cr3_set_address( whitelist_new.hptw_pal_checked_guest_ctx.super.t,
                                                VCPU_gcr3( vcpu), /* XXX should build trusted cr3 from scratch */
                                                whitelist_new.hptw_pal_checked_guest_ctx.super.root_pa);

  /*
   * flush TLB for page table modifications to take effect.
   * make sure other CPUs also flush the TLB after quiesce.
   */
  xmhf_memprot_flushmappings_alltlb(vcpu);

#ifdef __DMAP__
    /* Disable device accesses to these memory (via IOMMU) */
	xmhf_dmaprot_invalidate_cache();
#endif /* __DMAP__ */

  /* initialize Micro-TPM instance */
  utpm_init_instance(&whitelist_new.utpm);

  /* extent uTPM PCR[0] with with hash of each section metadata and contents */
  EU_CHKN( scode_measure_sections(&whitelist_new.utpm, &whitelist_new));

#ifdef __MP_VERSION__
  /* initialize PAL running lock */
  whitelist_new.pal_running_lock=1;
  whitelist_new.pal_running_vcpu_id=-1;
#endif

  /* add new entry into whitelist */
  /* CRITICAL SECTION in MP scenario: need to quiesce other CPUs or at least acquire spinlock */
  for (i = 0; whitelist[i].gcr3!=0 && i < whitelist_max; i ++);
  EU_CHK( i < whitelist_max);
  whitelist_size ++;
  memcpy(whitelist + i, &whitelist_new, sizeof(whitelist_entry_t));

  /*
   * reset performance counters
   */
  {
    int j;
    for(j=0; j<TV_PERF_CTRS_COUNT; j++) {
      perf_ctr_reset(&g_tv_perf_ctrs[j]);
    }
  }

  rv=0;
 out:
  /* FIXME clean-up in case of error */
  return rv;
}

/* unregister scode in whitelist */
u64 scode_unregister(VCPU * vcpu, u64 gvaddr)
{
  size_t i, j;
  u64 rv=1;
  u32 g64;
  u64 gcr3;

  gcr3 = VCPU_gcr3(vcpu);
  g64 = VCPU_g64(vcpu);

  eu_trace("*** scode unregister ***");

  EU_CHK( whitelist_size != 0);

  eu_trace("CPU(%02x): remove from whitelist gcr3 %#llx, gvaddr %#x", vcpu->id, gcr3, gvaddr);

  for (i = 0; i < whitelist_max; i ++) {
    /* find scode with correct cr3 and entry point */
    hpt_type_t t = whitelist[i].hptw_pal_checked_guest_ctx.super.t;
    if ((whitelist[i].gcr3 == hpt_cr3_get_address(t, gcr3)) &&
        (g64 == whitelist[i].g64) &&
        (whitelist[i].entry_v == gvaddr))
      break;
  }

  EU_CHK( i < whitelist_max);

  /* dump perf counters */
  eu_perf("performance counters:");
  for(j=0; j<TV_PERF_CTRS_COUNT; j++) {
    eu_perf("  %s total: %llu count: %llu",
            g_tv_perf_ctr_strings[j],
            perf_ctr_get_total_time(&g_tv_perf_ctrs[j]),
            perf_ctr_get_count(&g_tv_perf_ctrs[j]));
  }

  /* Disabled when we switched tlsf implementations; would now require
   * manual accounting to track accurately (i.e., account for calls to
   * free). */
  /* eu_perf("total mem mallocd: %u", heapmem_get_used_size()); */

  /* restore permissions for remapped sections */
  for(j = 0; j < whitelist[i].sections_num; j++) {
    /* zero the contents of any sections that are writable by the PAL, and not readable by the reg guest */
    if ((whitelist[i].sections[j].pal_prot & HPT_PROTS_W)
        && !(whitelist[i].sections[j].reg_prot & HPT_PROTS_R)) {
      int err;
      eu_trace("zeroing section %d", j);
      err = hptw_checked_memset_va( &whitelist[i].hptw_pal_checked_guest_ctx.super,
                                    HPTW_CPL3,
                                    whitelist[i].sections[j].pal_gva, 0, whitelist[i].sections[j].size);
      /* should only fail if insufficient permissions in the guest
         page tables, which TV constructed and the PAL should not have
         been able to modify */
      HALT_ON_ERRORCOND(!err);
    }

    scode_return_section( &g_hptw_reg_host_ctx.super,
                          &whitelist[i].hptw_pal_host_ctx.super,
                          &whitelist[i].hptw_pal_checked_guest_ctx.super,
                          &whitelist[i].sections[j]);
  }
  /*
   * flush TLB for page table modifications to take effect.
   * make sure other CPUs also flush the TLB after quiesce.
   */
  xmhf_memprot_flushmappings_alltlb(vcpu);

  /* delete entry from scode whitelist */
  /* CRITICAL SECTION in MP scenario: need to quiesce other CPUs or at least acquire spinlock */
  whitelist_size --;
  whitelist[i].gcr3 = 0;

  pagelist_free_all(whitelist[i].npl);
  free(whitelist[i].npl);

  pagelist_free_all(whitelist[i].gpl);
  free(whitelist[i].gpl);

  rv=0;
 out:
  return rv;
}

u32 scode_marshall64(VCPU * vcpu, struct regs *r)
{
#ifdef __XMHF_AMD64__
  uintptr_t pm_addr, pm_addr_base; /*parameter stack base address*/
  u64 pm_value, pm_tmp; /* For amd64 calling convention, need to be u64 */
  u64 pm_type;
  u64 pm_size, pm_size_sum; /*save pm information*/
  int pm_i;
  uintptr_t grsp;
  uintptr_t new_rsp = VCPU_grsp(vcpu);
  int curr=scode_curr[vcpu->id];
  u32 err=1;
  hptw_emhf_checked_guest_ctx_t vcpu_guest_walk_ctx;

  perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_MARSHALL], vcpu->idx);

  EU_CHKN( hptw_emhf_checked_guest_ctx_init_of_vcpu( &vcpu_guest_walk_ctx, vcpu));

  eu_trace("marshalling scode parameters!");
  EU_CHK(whitelist[curr].gpm_num != 0);

  /* memory address for input parameter in sensitive code */
  pm_addr_base = whitelist[curr].gpmp;
  eu_trace("parameter page base address is %#lx", pm_addr_base);

  /* address for parameters in guest stack */
  grsp = (uintptr_t)whitelist[curr].grsp + 8; /*the stack pointer of parameters in guest stack*/

  /* save params number */
  pm_addr = pm_addr_base;
  EU_CHKN( hptw_checked_copy_to_va( &whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                    HPTW_CPL3,
                                    pm_addr,
                                    &whitelist[curr].gpm_num,
                                    sizeof(whitelist[curr].gpm_num)));
  pm_addr += sizeof(whitelist[curr].gpm_num);
  pm_size_sum = sizeof(whitelist[curr].gpm_num); /*memory used in input pms section*/
  eu_trace("params number is %d", whitelist[curr].gpm_num);

  EU_CHK( whitelist[curr].gpm_num <= TV_MAX_PARAMS);

  /* begin to process the params*/
  for (pm_i = whitelist[curr].gpm_num-1; pm_i >= 0; pm_i--) /*the last parameter should be pushed in stack first*/
    {
      /* get param information*/
      pm_type = whitelist[curr].params_info.params[pm_i].type;
      pm_size = whitelist[curr].params_info.params[pm_i].size * 8;
      /* get param value from guest registers / stack */
      switch (pm_i) {
        case 0: pm_value = r->rdi; break;
        case 1: pm_value = r->rsi; break;
        case 2: pm_value = r->rdx; break;
        case 3: pm_value = r->rcx; break;
        case 4: pm_value = r->r8; break;
        case 5: pm_value = r->r9; break;
        default:
          eu_trace("copying param %d", pm_i);
          EU_CHKN( copy_from_current_guest(vcpu, &pm_value, grsp + (pm_i-6)*8, sizeof(pm_value)));
          break;
      }


      pm_size_sum += sizeof(pm_type)+sizeof(pm_size)+sizeof(pm_value);
      EU_CHK( pm_size_sum <= (whitelist[curr].gpm_size*PAGE_SIZE_4K));

      /* save input params in input params memory for sensitive code */
      EU_CHKN( hptw_checked_copy_to_va(&whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                       HPTW_CPL3,
                                       pm_addr,
                                       &pm_type, sizeof(pm_type)));
      pm_addr += sizeof(pm_type);
      EU_CHKN( hptw_checked_copy_to_va(&whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                       HPTW_CPL3,
                                       pm_addr,
                                       &pm_size, sizeof(pm_size)));
      pm_addr += sizeof(pm_size);
      EU_CHKN( hptw_checked_copy_to_va(&whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                       HPTW_CPL3,
                                       pm_addr,
                                       &pm_value, sizeof(pm_value)));
      pm_addr += sizeof(pm_value);
      eu_trace("scode_marshal copied metadata to params area");

      switch (pm_type)
        {
        case TV_PAL_PM_INTEGER: /* integer */
          {
            /* put the parameter value in sensitive code stack */
            pm_tmp = pm_value;
            eu_trace("PM %d is a integer (size %d, value %#lx)", pm_i, pm_size, pm_value);
            break;
          }
        case TV_PAL_PM_POINTER: /* pointer */
          {
            /*copy data from guest space to sensitive code*/
            pm_size_sum += pm_size;
            EU_CHK( pm_size_sum <= (whitelist[curr].gpm_size*PAGE_SIZE_4K));

            eu_trace("PM %d is a pointer (size %d, value %#lx)", pm_i, pm_size, pm_value);

            EU_CHKN( hptw_checked_copy_va_to_va(&whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                                HPTW_CPL3,
                                                pm_addr,
                                                &vcpu_guest_walk_ctx.super,
                                                HPTW_CPL3,
                                                pm_value,
                                                pm_size));

            /* put pointer address in sensitive code stack*/
            pm_tmp = pm_addr;
            pm_addr += pm_size;
            break;
          }
        default: /* other */
          eu_err("Fail: unknown parameter %d type %d ", pm_i, pm_type);
          err=7;
          goto out;
        }
      switch (pm_i) {
        case 0: r->rdi = pm_tmp; break;
        case 1: r->rsi = pm_tmp; break;
        case 2: r->rdx = pm_tmp; break;
        case 3: r->rcx = pm_tmp; break;
        case 4: r->r8 = pm_tmp; break;
        case 5: r->r9 = pm_tmp; break;
        default:
          new_rsp -= sizeof(pm_tmp);
          EU_CHKN( hptw_checked_copy_to_va( &whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                            HPTW_CPL3,
                                            new_rsp,
                                            &pm_tmp,
                                            sizeof(pm_tmp)));
          break;
      }
    }
    VCPU_grsp_set(vcpu, new_rsp);

  err=0;
 out:
  perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_MARSHALL], vcpu->idx);
  return err;
#else /* !__XMHF_AMD64__ */
  (void)vcpu;
  (void)r;
  /* Not supported */
  return 1;
#endif /* __XMHF_AMD64__ */
}

u32 scode_marshall32(VCPU * vcpu)
{
  uintptr_t pm_addr, pm_addr_base; /*parameter stack base address*/
  u64 pm_value;
  u32 pm_tmp; /* For x86 calling convention, need to be u32 */
  u64 pm_type;
  u64 pm_size, pm_size_sum; /*save pm information*/
  int pm_i;
  uintptr_t grsp;
  uintptr_t new_rsp = VCPU_grsp(vcpu);
  int curr=scode_curr[vcpu->id];
  u32 err=1;
  hptw_emhf_checked_guest_ctx_t vcpu_guest_walk_ctx;

  perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_MARSHALL], vcpu->idx);

  EU_CHKN( hptw_emhf_checked_guest_ctx_init_of_vcpu( &vcpu_guest_walk_ctx, vcpu));

  eu_trace("marshalling scode parameters!");
  EU_CHK(whitelist[curr].gpm_num != 0);

  /* memory address for input parameter in sensitive code */
  pm_addr_base = whitelist[curr].gpmp;
  eu_trace("parameter page base address is %#lx", pm_addr_base);

  /* address for parameters in guest stack */
  grsp = (uintptr_t)whitelist[curr].grsp + 4; /*the stack pointer of parameters in guest stack*/

  /* save params number */
  pm_addr = pm_addr_base;
  EU_CHKN( hptw_checked_copy_to_va( &whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                    HPTW_CPL3,
                                    pm_addr,
                                    &whitelist[curr].gpm_num,
                                    sizeof(whitelist[curr].gpm_num)));
  pm_addr += sizeof(whitelist[curr].gpm_num);
  pm_size_sum = sizeof(whitelist[curr].gpm_num); /*memory used in input pms section*/
  eu_trace("params number is %d", whitelist[curr].gpm_num);

  EU_CHK( whitelist[curr].gpm_num <= TV_MAX_PARAMS);

  /* begin to process the params*/
  for (pm_i = whitelist[curr].gpm_num-1; pm_i >= 0; pm_i--) /*the last parameter should be pushed in stack first*/
    {
      /* get param information*/
      pm_type = whitelist[curr].params_info.params[pm_i].type;
      pm_size = whitelist[curr].params_info.params[pm_i].size * 4;
      /* get param value from guest stack */
      eu_trace("copying param %d", pm_i);
      /* Make sure upper bits of pm_value are clear */
      pm_value = 0;
      /* Cannot use sizeof() because pm_value is u64 */
      EU_CHKN( copy_from_current_guest(vcpu, &pm_value, grsp + pm_i*4, 4));

      pm_size_sum += sizeof(pm_type)+sizeof(pm_size)+sizeof(pm_value);
      EU_CHK( pm_size_sum <= (whitelist[curr].gpm_size*PAGE_SIZE_4K));

      /* save input params in input params memory for sensitive code */
      EU_CHKN( hptw_checked_copy_to_va(&whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                       HPTW_CPL3,
                                       pm_addr,
                                       &pm_type, sizeof(pm_type)));
      pm_addr += sizeof(pm_type);
      EU_CHKN( hptw_checked_copy_to_va(&whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                       HPTW_CPL3,
                                       pm_addr,
                                       &pm_size, sizeof(pm_size)));
      pm_addr += sizeof(pm_size);
      EU_CHKN( hptw_checked_copy_to_va(&whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                       HPTW_CPL3,
                                       pm_addr,
                                       &pm_value, sizeof(pm_value)));
      pm_addr += sizeof(pm_value);
      eu_trace("scode_marshal copied metadata to params area");

      switch (pm_type)
        {
        case TV_PAL_PM_INTEGER: /* integer */
          {
            /* put the parameter value in sensitive code stack */
            pm_tmp = (u32)pm_value;
            eu_trace("PM %d is a integer (size %d, value %#lx)", pm_i, pm_size, pm_value);
            break;
          }
        case TV_PAL_PM_POINTER: /* pointer */
          {
            /*copy data from guest space to sensitive code*/
            pm_size_sum += pm_size;
            EU_CHK( pm_size_sum <= (whitelist[curr].gpm_size*PAGE_SIZE_4K));

            eu_trace("PM %d is a pointer (size %d, value %#lx)", pm_i, pm_size, pm_value);

            EU_CHKN( hptw_checked_copy_va_to_va(&whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                                HPTW_CPL3,
                                                pm_addr,
                                                &vcpu_guest_walk_ctx.super,
                                                HPTW_CPL3,
                                                pm_value,
                                                pm_size));

            /* put pointer address in sensitive code stack*/
            pm_tmp = pm_addr;
            pm_addr += pm_size;
            break;
          }
        default: /* other */
          eu_err("Fail: unknown parameter %d type %d ", pm_i, pm_type);
          err=7;
          goto out;
        }
      new_rsp -= sizeof(pm_tmp);
      EU_CHKN( hptw_checked_copy_to_va( &whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                        HPTW_CPL3,
                                        new_rsp,
                                        &pm_tmp,
                                        sizeof(pm_tmp)));
    }
    VCPU_grsp_set(vcpu, new_rsp);

  err=0;
 out:
  perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_MARSHALL], vcpu->idx);
  return err;
}



//todo: switch from regular code to sensitive code
u32 hpt_scode_switch_scode(VCPU * vcpu, struct regs *r)
{
  int curr=scode_curr[vcpu->id];
  int err=1;
  bool swapped_grsp=false;
  bool pushed_return=false;
  u64 sentinel_return; /* In x86, only use 4 bytes */
  u64 regular_return = 0; /* In x86, only use 4 bytes */
  u32 word_size = VCPU_g64(vcpu) ? 8 : 4;

  perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_SWITCH_SCODE], vcpu->idx);

  eu_trace("*** to scode ***");

  spin_lock(&(whitelist[curr].pal_running_lock));
  whitelist[curr].pal_running_vcpu_id=vcpu->id;
  eu_trace("got pal_running lock!");

  EU_CHKN( copy_from_current_guest(vcpu,
                                   &regular_return,
                                   VCPU_grsp(vcpu),
                                   word_size));
  whitelist[curr].return_v = (uintptr_t)regular_return;
  eu_trace("scode return vaddr is %#lx", whitelist[curr].return_v);

  /* save the guest stack pointer and set new stack pointer to scode stack */
  eu_trace("saved guest regular stack %#lx, switch to sensitive code stack %#lx",
           (uintptr_t)VCPU_grsp(vcpu), whitelist[curr].gssp);
  whitelist[curr].grsp = (uintptr_t)VCPU_grsp(vcpu);
  VCPU_grsp_set(vcpu, whitelist[curr].gssp);
  swapped_grsp=true;

  /* input parameter marshalling */
  if (whitelist[curr].g64) {
    EU_CHKN( scode_marshall64(vcpu, r));
  } else {
    EU_CHKN( scode_marshall32(vcpu));
  }

  /* write the sentinel return address to scode stack */
  sentinel_return = RETURN_FROM_PAL_ADDRESS;
  EU_CHKN( hptw_checked_copy_to_va( &whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                    HPTW_CPL3,
                                    VCPU_grsp(vcpu)-word_size,
                                    &sentinel_return,
                                    word_size));
  VCPU_grsp_set(vcpu, VCPU_grsp(vcpu)-word_size);
  pushed_return=true;

  eu_trace("host stack pointer before running scode is %#lx",(uintptr_t)VCPU_grsp(vcpu));

  /* nothing below here can fail. (i.e., don't have to cleanup code
     below in case of error) */

  eu_trace("change NPT permission to run PAL!");
  eu_trace("vcpu=%#x, guest_RIP=%#lx, guest_RSP=%#lx", vcpu->id,
           VCPU_grip(vcpu), VCPU_grsp(vcpu));
  hpt_emhf_set_root_pm_pa( vcpu, whitelist[curr].hptw_pal_host_ctx.super.root_pa);
  VCPU_gcr3_set(vcpu, whitelist[curr].pal_gcr3);

  /*
   * flush TLB for page table modifications to take effect.
   * make sure other CPUs also flush the TLB after quiesce.
   * TODO: this may be unnecessary. Review and see whether can remove.
   */
  xmhf_memprot_flushmappings_alltlb(vcpu);

  if (whitelist[curr].hptw_pal_checked_guest_ctx.super.t == HPT_TYPE_PAE) {
    /* For PAE paging, need to update VMCS PDPTEs manually */
    hptw_ctx_t *ctx = &whitelist[curr].hptw_pal_host_ctx.super;
    size_t avail_sz;
    u64 *pdptes = ctx->pa2ptr(ctx, VCPU_gcr3(vcpu), sizeof(u64) * 4,
                              HPT_PROTS_R, HPTW_CPL3, &avail_sz);
    EU_CHK(avail_sz == sizeof(u64) * 4);
    VCPU_gpdpte_set(vcpu, pdptes);
  }

  /* disable interrupts, assume regular code has interrupts enabled */
  {
    u64 rflags = VCPU_grflags(vcpu);
    EU_CHK((rflags & EFLAGS_IF) == EFLAGS_IF);
    VCPU_grflags_set(vcpu, rflags & ~EFLAGS_IF);
  }

  /* disable NMIs, assume regular code has NMIs enabled */
  xmhf_smpguest_nmi_block(vcpu);

  /* XXX FIXME- what's the right thing here? Keeping 'legacy' behavior
     of setting this flag for AMD only and doing nothing for INTEL for
     now */
  if(vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    /* set the sensitive code to run in ring 3 */
    ((struct _svm_vmcbfields *)(vcpu->vmcb_vaddr_ptr))->cpl = 3;
  }

  perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_SWITCH_SCODE], vcpu->idx);

  /* intercept all exceptions. (otherwise they'll result in a triple-fault,
   *   since the PAL doesn't have any exception handlers installed).
   */
  if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    whitelist[curr].saved_exception_intercepts =
      ((struct _svm_vmcbfields *)(vcpu->vmcb_vaddr_ptr))->exception_intercepts_bitmask;
    ((struct _svm_vmcbfields *)(vcpu->vmcb_vaddr_ptr))->exception_intercepts_bitmask = 0xffffffff;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    whitelist[curr].saved_exception_intercepts =  vcpu->vmcs.control_exception_bitmap;
    vcpu->vmcs.control_exception_bitmap = 0xffffffff;
  }

  err=0;
 out:
  if(err) {
    if (swapped_grsp) {
      VCPU_grsp_set(vcpu, whitelist[curr].grsp);
      whitelist[curr].grsp = (uintptr_t)-1;
    }
    if (pushed_return) {
      VCPU_grsp_set(vcpu, VCPU_grsp(vcpu)+word_size);
    }

    whitelist[curr].pal_running_vcpu_id=-1;
    spin_unlock(&(whitelist[curr].pal_running_lock));
    eu_trace("released pal_running lock!");
  }
  return err;
}

u32 scode_unmarshall(VCPU * vcpu)
{
  uintptr_t pm_addr_base, pm_addr;
  size_t i;
  u64 pm_num, pm_value; /* Need to be consistent with scode_marshall */
  u64 pm_type;
  u64 pm_size; /* Need to be consistent with scode_marshall */

  int curr=scode_curr[vcpu->id];

  hptw_emhf_checked_guest_ctx_t reg_guest_walk_ctx;
  u32 err=1;


  EU_CHKN( hptw_emhf_checked_guest_ctx_init( &reg_guest_walk_ctx,
                                             whitelist[curr].reg_gpt_root_pa,
                                             whitelist[curr].reg_gpt_type,
                                             HPTW_CPL3,
                                             &g_hptw_reg_host_ctx,
                                             NULL));

  eu_trace("unmarshalling scode parameters!");
  EU_CHK( whitelist[curr].gpm_num != 0);

  /* memory address for input parameter in sensitive code */
  pm_addr_base = whitelist[curr].gpmp;
  eu_trace("parameter page base address is %#x", pm_addr_base);

  /* get params number */
  pm_addr = pm_addr_base;
  EU_CHKN( hptw_checked_copy_from_va( &whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                      HPTW_CPL3,
                                      &pm_num,
                                      pm_addr,
                                      sizeof(pm_num)));
  pm_addr += sizeof(pm_num);
  eu_trace("params number is %d", pm_num);
  EU_CHK( pm_num <= TV_MAX_PARAMS);

  /* begin to process the params*/
  for (i = 0; i < pm_num; i++) /*the last parameter should be pushed in stack first*/
    {
      /* get param information*/
      EU_CHKN( hptw_checked_copy_from_va( &whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                          HPTW_CPL3,
                                          &pm_type,
                                          pm_addr,
                                          sizeof(pm_type)));
      pm_addr += sizeof(pm_type);

      switch (pm_type)
        {
        case TV_PAL_PM_INTEGER: /*integer*/
          {
            /* don't need to put integer back to regular code stack */
            pm_addr += sizeof(pm_size) + sizeof(pm_value);
            eu_trace("skip an integer parameter!");
            break;
          }
        case TV_PAL_PM_POINTER: /* pointer */
          {
            EU_CHKN( hptw_checked_copy_from_va( &whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                                HPTW_CPL3,
                                                &pm_size,
                                                pm_addr,
                                                sizeof(pm_size)));
            pm_addr += sizeof(pm_size);
            /* get pointer adddress in regular code */
            EU_CHKN( hptw_checked_copy_from_va( &whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                                HPTW_CPL3,
                                                &pm_value,
                                                pm_addr,
                                                sizeof(pm_value)));
            pm_addr += sizeof(pm_value);

            eu_trace("PM %d is a pointer (size %d, addr %#x)", i,  pm_size, pm_value);
            /* copy data from sensitive code (param space) to guest */
            EU_CHKN( hptw_checked_copy_va_to_va( &reg_guest_walk_ctx.super,
                                                 HPTW_CPL3,
                                                 pm_value,
                                                 &whitelist[curr].hptw_pal_checked_guest_ctx.super,
                                                 HPTW_CPL3,
                                                 pm_addr,
                                                 pm_size));
            pm_addr += pm_size;
            break;
          }

        default: /* other */
          eu_err("Fail: unknown parameter %d type %d ", i, pm_type);
          err=5;
          goto out;
        } // end switch

    } //end for loop

  err=0;
 out:
  return err;
}

//switch from sensitive code to regular code
u32 hpt_scode_switch_regular(VCPU * vcpu)
{
  int curr=scode_curr[vcpu->id];
  u32 rv=1;
  u32 word_size = VCPU_g64(vcpu) ? 8 : 4;

  perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_SWITCH_REGULAR], vcpu->idx);

  eu_trace("************************************");
  eu_trace("***** switch to regular code  ******");
  eu_trace("************************************");

  /* marshalling parameters back to regular code */
  EU_CHKN( scode_unmarshall(vcpu));

  /* whether or not marshalling succeeded, we switch back to reg world.
   * nothing below can fail.
   */
  rv=0;
 out:

  /* restore exception intercept vector */
  if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct _svm_vmcbfields *)(vcpu->vmcb_vaddr_ptr))->exception_intercepts_bitmask
      = whitelist[curr].saved_exception_intercepts;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    vcpu->vmcs.control_exception_bitmap
      = whitelist[curr].saved_exception_intercepts;
  }

  /* release shared pages */
  scode_release_all_shared_pages(vcpu, &whitelist[curr]);

  /* clear the NPT permission setting in switching into scode */
  eu_trace("change NPT permission to exit PAL!");
  hpt_emhf_set_root_pm(vcpu, g_reg_npmo_root.pm);
  VCPU_gcr3_set(vcpu, whitelist[curr].gcr3);

  /*
   * flush TLB for page table modifications to take effect.
   * make sure other CPUs also flush the TLB after quiesce.
   * TODO: this may be unnecessary. Review and see whether can remove.
   */
  xmhf_memprot_flushmappings_alltlb(vcpu);

  if (whitelist[curr].hptw_pal_checked_guest_ctx.super.t == HPT_TYPE_PAE) {
    /* For PAE paging, need to update VMCS PDPTEs manually */
    hptw_ctx_t *ctx = &g_hptw_reg_host_ctx.super;
    size_t avail_sz;
    u64 *pdptes = ctx->pa2ptr(ctx, VCPU_gcr3(vcpu), sizeof(u64) * 4,
                              HPT_PROTS_R, HPTW_CPL3, &avail_sz);
    EU_CHK(avail_sz == sizeof(u64) * 4);
    VCPU_gpdpte_set(vcpu, pdptes);
  }

  /* switch back to regular stack */
  eu_trace("switch from scode stack %#x back to regular stack %#lx", (uintptr_t)VCPU_grsp(vcpu), (uintptr_t)whitelist[curr].grsp);
  VCPU_grsp_set(vcpu, whitelist[curr].grsp + word_size);
  whitelist[curr].grsp = (uintptr_t)-1;

  /* enable interrupts, check that scode has interrupts disabled */
  {
    u64 rflags = VCPU_grflags(vcpu);
    EU_CHK((rflags & EFLAGS_IF) == 0);
    VCPU_grflags_set(vcpu, rflags | EFLAGS_IF);
  }

  /* enable NMIs, check that scode has NMIs disabled */
  xmhf_smpguest_nmi_unblock(vcpu);

  eu_trace("stack pointer before exiting scode is %#lx",(uintptr_t)VCPU_grsp(vcpu));

  /* return to actual return address */
  VCPU_grip_set(vcpu, whitelist[curr].return_v);

  whitelist[curr].pal_running_vcpu_id=-1;
  spin_unlock(&(whitelist[curr].pal_running_lock));
  eu_trace("released pal_running lock!");

  perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_SWITCH_REGULAR], vcpu->idx);

  return rv;
}

#if !defined(__LDN_TV_INTEGRATION__)
static bool hpt_error_wasInsnFetch(VCPU *vcpu, u64 errorcode)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return (errorcode & EPT_ERRORCODE_EXEC);
  } else if (vcpu->cpu_vendor != CPU_VENDOR_AMD) {
    HALT_ON_ERRORCOND(0);
  }
  return (errorcode & VMCB_NPT_ERRORCODE_ID);
}
#endif //__LDN_TV_INTEGRATION__

/*  EPT violation handler */
u32 hpt_scode_npf(VCPU * vcpu, uintptr_t gpaddr, u64 errorcode, struct regs *r)
{
  int index = -1;

  int * curr=&(scode_curr[vcpu->id]);
  u64 gcr3 = VCPU_gcr3(vcpu);
  uintptr_t rip = (uintptr_t)VCPU_grip(vcpu);
  u32 g64;
  u32 err=1;

#if defined(__LDN_TV_INTEGRATION__)
  (void)errorcode;
#endif //__LDN_TV_INTEGRATION__

  perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_NPF], vcpu->idx);

#if !defined(__LDN_TV_INTEGRATION__)
  eu_trace("CPU(%02x): nested page fault!(rip %#lx, gcr3 %#llx, gpaddr %#lx, errorcode %llx)",
          vcpu->id, rip, gcr3, gpaddr, errorcode);

  EU_CHK( hpt_error_wasInsnFetch(vcpu, errorcode));
#endif //__LDN_TV_INTEGRATION__

  g64 = VCPU_g64(vcpu);
  index = scode_in_list(gcr3, rip, g64);
  if ((*curr == -1) && (index >= 0)) {
    /* regular code to sensitive code */

    *curr = index;
    EU_CHK( ((whitelist[*curr].entry_v == rip)
             && (whitelist[*curr].entry_p == gpaddr)),
            eu_err_e("Invalid entry point"));

    /* valid entry point, switch from regular code to sensitive code */
    EU_CHKN( hpt_scode_switch_scode(vcpu, r));

  } else if ((*curr >=0) && (index < 0)) {
    /* sensitive code to regular code */

    EU_CHK( RETURN_FROM_PAL_ADDRESS == rip,
            eu_err_e("SECURITY: invalid scode return point!"));

    /* valid return point, switch from sensitive code to regular code */

    /* XXX FIXME: now return ponit is extracted from regular code stack, only support one scode function call */
    EU_CHKN( hpt_scode_switch_regular(vcpu));
    *curr = -1;
  } else if ((*curr >=0) && (index >= 0)) {
    /* sensitive code to sensitive code */
    if (*curr == index)
      eu_err("SECURITY: incorrect scode EPT configuration!");
    else
      eu_err("SECURITY: invalid access to scode mem region from other scodes!");
    goto out;
  } else {
#if !defined(__LDN_TV_INTEGRATION__)
    /* regular code to regular code */
    eu_err("incorrect regular code EPT configuration!");
#endif //__LDN_TV_INTEGRATION__
    goto out;
  }

  /* no errors, pseodu page fault canceled by nested paging */
  if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->eventinj.v = 0;
  } /* FIXME - equivalent for intel? */

  err=0;
 out:
  perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_NPF], vcpu->idx);
  if(err) {
    if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
      /* errors, inject segfault to guest */
      struct _svm_vmcbfields* vmcb = (struct _svm_vmcbfields*)(vcpu->vmcb_vaddr_ptr);
      vmcb->eventinj.vector=0xd;
      vmcb->eventinj.type=EVENTINJ_TYPE_EXCEPTION;
      vmcb->eventinj.ev=0x1;
      vmcb->eventinj.v=0x1;
      vmcb->eventinj.errorcode = 0;
    } /* FIXME - equivalent for intel? */

    *curr = -1;
  }
  return err;
}

/* caller is responsible for flushing TLB */
void scode_release_all_shared_pages(VCPU *vcpu, whitelist_entry_t* wle)
{
  int i;

  (void)vcpu;

  /* restore permissions for remapped sections */
  /* assumes that SHARED sections are contiguous and on the end of the sections array */
  for(i = wle->sections_num-1;
      i >= 0 && wle->sections[i].section_type == TV_PAL_SECTION_SHARED;
      i--) {
    eu_trace("returning shared section num %d at 0x%08llx", i, wle->sections[i].pal_gva);
    scode_return_section( &g_hptw_reg_host_ctx.super,
                          &wle->hptw_pal_host_ctx.super,
                          &wle->hptw_pal_checked_guest_ctx.super,
                          &wle->sections[i]);
    wle->sections_num--;
  }
}

/* note- caller is responsible for flushing page tables afterwards */
u32 scode_share_range(VCPU * vcpu, whitelist_entry_t *wle, u32 gva_base, u32 gva_len)
{
  u32 err=1;
  hptw_emhf_checked_guest_ctx_t vcpu_guest_walk_ctx;
  EU_CHKN( hptw_emhf_checked_guest_ctx_init_of_vcpu( &vcpu_guest_walk_ctx, vcpu));

  EU_CHK( wle->sections_num < TV_MAX_SECTIONS);

  wle->sections[wle->sections_num] = (tv_pal_section_int_t) {
    .reg_gva = gva_base,
    .pal_gva = gva_base,
    .size = gva_len,
    .pal_prot = pal_prot_of_type(TV_PAL_SECTION_SHARED),
    .reg_prot = reg_prot_of_type(TV_PAL_SECTION_SHARED),
    .section_type = TV_PAL_SECTION_SHARED,
  };

  scode_lend_section( &g_hptw_reg_host_ctx.super,
                      &vcpu_guest_walk_ctx.super,
                      &wle->hptw_pal_host_ctx.super,
                      &wle->hptw_pal_checked_guest_ctx.super,
                      &wle->sections[wle->sections_num]);

  wle->sections_num++;

  err=0;
 out:
  return err;
}

u32 scode_share_ranges(VCPU * vcpu, u32 scode_entry, u32 gva_base[], u32 gva_len[], u32 count)
{
  size_t i;
  whitelist_entry_t* entry;
  u32 g64;
  u32 err=1;

  g64 = VCPU_g64(vcpu);
  EU_CHK( entry = find_scode_by_entry(VCPU_gcr3(vcpu), scode_entry, g64));

  for(i=0; i<count; i++) {
    EU_CHKN( scode_share_range(vcpu, entry, gva_base[i], gva_len[i]));
  }

  /*
   * flush TLB for page table modifications to take effect.
   * make sure other CPUs also flush the TLB after quiesce.
   */
  xmhf_memprot_flushmappings_alltlb(vcpu);

  err=0;
out:
  if (err && entry) {
    scode_release_all_shared_pages(vcpu, entry);
  }
  return err;
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:nil */
/* c-basic-offset:2 */
/* End:             */
