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

/* scode.c routines to handle all scode loading and unloading, also 
 * whitelist, hash value verification for both shadow paging and nested 
 * paging.
 * Written for TrustVisor by Ning Qu, Zongwei Zhou, and Yanlin Li
 * Edited for TrustVisor on EMHF by Zongwei Zhou
 */

#include <emhf.h> 

#include <scode.h>
#include <malloc.h>
#include <tv_utpm.h> /* formerly utpm.h */
#include <rsa.h>
#include <random.h>
#include <crypto_init.h>
#include <sha1.h>

hpt_pa_t hpt_nested_ptr2pa(void __attribute__((unused)) *ctx, void *ptr)
{
  return hva2spa(ptr);
}
void* hpt_nested_pa2ptr(void *vctx, hpt_pa_t spa, size_t sz, hpt_prot_t access_type, hptw_cpl_t cpl, size_t *avail_sz)
{
  (void)vctx;
  (void)access_type;
  (void)cpl;
  *avail_sz = sz;
  return spa2hva(spa);
}
hpt_pa_t hpt_guest_ptr2pa(void __attribute__((unused)) *ctx, void *ptr)
{
  return hva2gpa(ptr);
}

/* void* hpt_guest_pa2ptr(void *vctx, hpt_pa_t gpa, size_t sz, hpt_prot_t access_type, hptw_cpl_t cpl, size_t *avail_sz) */
/* { */
/*   (void)vctx; */
/*   (void)access_type; */
/*   (void)cpl; */
/*   *avail_sz = sz; */
/*   return gpa2hva(gpa); */
/* } */
void* hpt_checked_guest_pa2ptr(void *vctx, hpt_pa_t gpa, size_t sz, hpt_prot_t access_type, hptw_cpl_t cpl, size_t *avail_sz)
{
  scode_guest_pa2ptr_ctx_t *ctx = vctx;

  dprintf(LOG_TRACE, "hpt_checked_guest_pa2ptr gpa:%llx, sz:%d, access_type:%lld, cpl:%d\n",
          gpa, sz, access_type, cpl);
  dprintf(LOG_TRACE, "hpt_checked_guest_pa2ptr host_pmo_root t:%d pm:%p lvl:%d\n",
          ctx->host_pmo_root.t, ctx->host_pmo_root.pm, ctx->host_pmo_root.lvl);

  ASSERT(ctx);

  return hptw_checked_access_va(&ctx->host_walk_ctx,
                                &ctx->host_pmo_root,
                                access_type,
                                cpl,
                                gpa,
                                sz,
                                avail_sz);
}

void* hpt_get_zeroed_page(void *ctx, size_t alignment, size_t sz)
{
  pagelist_t *pl = ctx;
  ASSERT(PAGE_SIZE_4K % alignment == 0);
  ASSERT(sz <= PAGE_SIZE_4K);
  return pagelist_get_zeroedpage(pl);
}
const hptw_ctx_t hpt_nested_walk_ctx = {
  .gzp = hpt_get_zeroed_page,
  .gzp_ctx = NULL, /* we'll copy this struct for
                      each pal and give each it's own allocation
                      pool */
  .pa2ptr = hpt_nested_pa2ptr,
  .ptr2pa = hpt_nested_ptr2pa,
  .ptr2pa_ctx = NULL,
};

int hpt_guest_walk_ctx_construct(hptw_ctx_t *rv, const hpt_pmo_t *host_root, const hptw_ctx_t *host_walk_ctx, pagelist_t *pl)
{
  scode_guest_pa2ptr_ctx_t *guest_pa2ptr_ctx=NULL;
  int err=0;

  guest_pa2ptr_ctx = malloc(sizeof(*guest_pa2ptr_ctx));
  if (!guest_pa2ptr_ctx) {
    err=1;
    goto out;
  }

  *guest_pa2ptr_ctx = (scode_guest_pa2ptr_ctx_t) {
    .host_pmo_root = *host_root,
    .host_walk_ctx = *host_walk_ctx,
  };

  *rv = (hptw_ctx_t) {
    .gzp = hpt_get_zeroed_page,
    .gzp_ctx = pl,
    .pa2ptr = hpt_checked_guest_pa2ptr,
    .pa2ptr_ctx = guest_pa2ptr_ctx,
    .ptr2pa = hpt_guest_ptr2pa,
    .ptr2pa_ctx = NULL,
  };

 out:
  if (err) {
    free(guest_pa2ptr_ctx);
  }
  return err;
}
int hpt_guest_walk_ctx_construct_vcpu(hptw_ctx_t *rv, VCPU *vcpu, pagelist_t *pl)
{
  hpt_pmo_t host_root;
  
  hpt_emhf_get_root_pmo(vcpu, &host_root);
  return hpt_guest_walk_ctx_construct(rv, &host_root, &hpt_nested_walk_ctx, pl);
}

void hpt_guest_walk_ctx_destroy(hptw_ctx_t *ctx)
{
  free(ctx->pa2ptr_ctx);
  ctx->pa2ptr_ctx = NULL;
}

hpt_pmo_t      g_reg_npmo_root;

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

/* helper function */
void __set_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] |= (1 << bit_offset);

  return;                        
}

void __clear_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] &= ~(1 << bit_offset);

  return;
}

u32 __test_page_prot(u32 pfn, u8 *bit_vector){
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  if (bit_vector[byte_offset] & (1 << bit_offset))
    return 1;
  else 
    return 0;
}



/* set scode remapping protection for a page, pfn is the page frame number */
#define set_page_scode_bitmap(pfn)	__set_page_prot(pfn, scode_pfn_bitmap)
/* clear scode remapping protection for a page, pfn is the page frame number */
#define clear_page_scode_bitmap(pfn)	__clear_page_prot(pfn, scode_pfn_bitmap)
/* test scode remapping protection enabled for a page, pfn is the page frame number */
#define test_page_scode_bitmap(pfn)	__test_page_prot(pfn, scode_pfn_bitmap)

static inline u32 set_page_scode_bitmap_2M(u32 pfn)
{
  u32 index;

  index = pfn >> (PAGE_SHIFT_2M - PAGE_SHIFT_4K);
  if (scode_pfn_bitmap_2M[index] < PAE_PTRS_PER_PDT)
    scode_pfn_bitmap_2M[index] ++;
  else
    {
      dprintf(LOG_ERROR, "FATAL ERROR: exceed the limitation of 2M page\n");
      HALT();
    }

  return scode_pfn_bitmap_2M[index];
}

static inline u32 clear_page_scode_bitmap_2M(u32 pfn)
{
  u32 index;

  index = pfn >> (PAGE_SHIFT_2M - PAGE_SHIFT_4K);
  if (scode_pfn_bitmap_2M[index] > 0)
    scode_pfn_bitmap_2M[index] --;
  else
    {
      dprintf(LOG_ERROR, "FATAL ERROR: exceed the limitation of 2M page\n");
      HALT();
    }

  return scode_pfn_bitmap_2M[index];
}

static inline u32 test_page_scode_bitmap_2M(u32 pfn)
{
  u32 index;

  index = pfn >> (PAGE_SHIFT_2M - PAGE_SHIFT_4K);

  return scode_pfn_bitmap_2M[index];
}

void scode_release_all_shared_pages(VCPU *vcpu, whitelist_entry_t* entry);

/* search scode in whitelist */
int scode_in_list(u64 gcr3, u32 gvaddr)
{
  size_t i, j;

  for (i = 0; i < whitelist_max; i ++)
    {
      if (gcr3 == whitelist[i].gcr3) {
        for( j=0 ; j<(u32)(whitelist[i].scode_info.num_sections) ; j++ )  {
          if( (gvaddr >= whitelist[i].scode_info.sections[j].start_addr) &&
              (gvaddr < ((whitelist[i].scode_info.sections[j].start_addr)+((whitelist[i].scode_info.sections[j].page_num)<<PAGE_SHIFT_4K)))  )  {
            dprintf(LOG_TRACE, "[TV] find gvaddr %#x in scode %d section No.%d !\n", gvaddr, i, j);
            return i;
          }
        }
      }
    }
  dprintf(LOG_TRACE, "[TV] no matching scode found for gvaddr %#x!\n", gvaddr);
  return -1;
}

static whitelist_entry_t* find_scode_by_entry(u64 gcr3, u32 gv_entry)
{
  size_t i;

  for (i = 0; i < whitelist_max; i ++)
    {
      /* find scode with correct cr3 and entry point */
      if ((whitelist[i].gcr3 == gcr3) && (whitelist[i].entry_v == gv_entry))
        return &whitelist[i];
    }
  return NULL;
}

int scode_measure_section(utpm_master_state_t *utpm,
                          whitelist_entry_t *wle,
                          const tv_pal_section_int_t *section)
{
  SHA_CTX ctx;
  TPM_DIGEST sha1sum;

  SHA1_Init(&ctx);

  /* always measure the section type, which determines permissions and
     how the section is used. */
  SHA1_Update(&ctx, (const uint8_t*)&section->section_type, sizeof(section->section_type));

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
    SHA1_Update(&ctx, (const uint8_t*)&section->pal_gva, sizeof(section->pal_gva));
  }

  /* measure section size. not clear that this is strictly necessary,
     since giving a pal more memory shouldn't hurt anything, and less
     memory should result in no worse than the pal crashing, but seems
     like good hygiene. */
  SHA1_Update(&ctx, (const uint8_t*)&section->size, sizeof(section->size));

  /* measure contents. we could consider making this optional for,
     e.g., PARAM and STACK sections, but seems like good hygiene to
     always do it. client ought to ensure that those sections are
     consistent (e.g., 0'd). an alternative to consider is to enforce
     that the hypervisor either measures or zeroes each section.*/
  {
    size_t measured=0;

    while(measured < section->size) {
      gva_t gva = section->pal_gva + measured;
      hpt_pmeo_t pmeo;
      gpa_t gpa;
      size_t to_measure;
      size_t remaining_on_page;

      hptw_get_pmeo(&pmeo, &wle->hpt_guest_walk_ctx, &wle->pal_gpt_root, 1, gva);
      /* trustvisor should have already mapped this section in before measuring it */
      /* XXX should this be a proper run-time check? */
      ASSERT(hpt_pmeo_is_present(&pmeo));
      ASSERT(hpt_pmeo_is_page(&pmeo));

      gpa = hpt_pmeo_va_to_pa(&pmeo, gva);

      remaining_on_page = hpt_remaining_on_page(&pmeo, gva);
      to_measure = MIN(section->size-measured, remaining_on_page);

      SHA1_Update(&ctx, gpa2hva(gpa), to_measure);
      measured += to_measure;
    }
  }

  SHA1_Final(sha1sum.value, &ctx);

  /* extend pcr 0 */
  utpm_extend(&sha1sum, utpm, 0);

  return 0;
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
  dprintf(LOG_TRACE, "[TV] alloc %dKB mem for scode_list at %x!\n", (WHITELIST_LIMIT/1024), (unsigned int)whitelist);
  scode_pfn_bitmap = (unsigned char *)malloc(PFN_BITMAP_LIMIT);
  dprintf(LOG_TRACE, "[TV] alloc %dKB mem for pfn_bitmap at %x!\n", (PFN_BITMAP_LIMIT/1024), (unsigned int)scode_pfn_bitmap);
  scode_pfn_bitmap_2M = (unsigned short *)malloc(PFN_BITMAP_2M_LIMIT);
  dprintf(LOG_TRACE, "[TV] alloc %dKB mem for pfn_bitmap_2M at %x!\n", (PFN_BITMAP_LIMIT/1024), (unsigned int)scode_pfn_bitmap_2M);

  memset(whitelist, 0, WHITELIST_LIMIT); 
  memset(scode_pfn_bitmap, 0, PFN_BITMAP_LIMIT);
  memset(scode_pfn_bitmap_2M, 0, PFN_BITMAP_2M_LIMIT);

  whitelist_size = 0;
  whitelist_max = WHITELIST_LIMIT / sizeof(whitelist_entry_t);
  dprintf(LOG_TRACE, "[TV] whitelist max = %d!\n", whitelist_max);

  /* init scode_curr struct
   * NOTE that cpu_lapic_id could be bigger than midtable_numentries */
  max = 0;
  for( inum=0 ; inum < g_midtable_numentries ; inum++ )  {
    if ( g_midtable[inum].cpu_lapic_id > max)
      max = g_midtable[inum].cpu_lapic_id;
  }
  scode_curr = malloc((max+1) * sizeof(*scode_curr));
  memset(scode_curr, 0xFF, ((max+1) * sizeof(*scode_curr)));

  /* init PRNG and long-term crypto keys */
  if(trustvisor_master_crypto_init()) {
    dprintf(LOG_ERROR, "[TV] trustvisor_master_crypto_init() FAILED! SECURITY HALT!\n");
    HALT();			
  }
  dprintf(LOG_TRACE, "[TV] trustvisor_master_crypto_init successful.\n");
}

/* parse scode paramter info ( scode registration input) */
int parse_params_info(VCPU * vcpu, struct tv_pal_params* pm_info, u32 pm_addr)
{
  size_t i, num;
  u32 addr;

  /* get number of parameters */
  if (copy_from_current_guest(vcpu,
                              &pm_info->num_params,
                              pm_addr,
                              sizeof(pm_info->num_params))) {
    dprintf(LOG_ERROR, "ERROR: couldn't read num_params from gva 0x%08x\n", pm_addr);
    return 1;
  }
  num = pm_info->num_params;

  dprintf(LOG_TRACE, "[TV] pm_info %#x, # of parameters is %d\n", pm_addr, num);
  if (num > TV_MAX_PARAMS) {
    dprintf(LOG_ERROR, "[TV] number of scode sections exceeds limit!\n");
    return 1;
  }

  addr = pm_addr+4;
  if (copy_from_current_guest(vcpu,
                              &pm_info->params[0],
                              addr,
                              sizeof(pm_info->params[0]) * num)) {
    dprintf(LOG_ERROR, "ERROR: couldn't read parameter info from gva 0x%08x\n", addr);
    return 2;
  }

  for (i = 0; i < num; i++) {
    dprintf(LOG_TRACE, "[TV] parameter %d type %d size %d\n", i, pm_info->params[i].type, pm_info->params[i].size);
  }

  return 0;
}

int memsect_info_copy_from_guest(VCPU * vcpu, struct tv_pal_sections *ps_scode_info, u32 gva_scode_info)
{
  size_t gva_scode_info_offset = 0;

  /* get number of sections */
  if(copy_from_current_guest(vcpu,
                             &ps_scode_info->num_sections,
                             gva_scode_info,
                             sizeof(ps_scode_info->num_sections))) {
    dprintf(LOG_ERROR, "ERROR: couldn't read num_sections from %08x", gva_scode_info);
    return 1;
  }

  gva_scode_info_offset += 4;
  dprintf(LOG_TRACE, "[TV] scode_info addr %x, # of section is %d\n", gva_scode_info, ps_scode_info->num_sections);

  /* copy array of section descriptors */
  if( ps_scode_info->num_sections > TV_MAX_SECTIONS )  {
    dprintf(LOG_ERROR, "[TV] number of scode sections exceeds limit!\n");
    return 3;
  }

  if(copy_from_current_guest(vcpu,
                             &(ps_scode_info->sections[0]),
                             gva_scode_info+gva_scode_info_offset,
                             ps_scode_info->num_sections*sizeof(ps_scode_info->sections[0]))) {
    dprintf(LOG_ERROR, "ERROR: couldn't copy section info from gva %08x", gva_scode_info+gva_scode_info_offset);
    return 4;
  }

  return 0;
}

/* parse scode sections info (scode registration input) */
int memsect_info_register(VCPU * vcpu, struct tv_pal_sections *ps_scode_info, whitelist_entry_t * wle)
{
  size_t i;
  int is_get_param, is_get_stack;
  int type, size;
  unsigned int start;

  /* parse section type, start address and size */
  is_get_param=0;
  is_get_stack=0;
  for (i = 0; i < ps_scode_info->num_sections; i++) {
    size = ps_scode_info->sections[i].page_num;
    type = ps_scode_info->sections[i].type;
    start = ps_scode_info->sections[i].start_addr;
    /* make sure the addr is 4kb page aligned */
    if(!is_page_4K_aligned(start)) {
      dprintf(LOG_ERROR, "[TV] ERROR: Section %d start address %x is not 4K-aligned\n", i, start);
      return 1;
    }
    switch ( type )  {
    case TV_PAL_SECTION_PARAM :
      {
        /* set param page num and addr */
        if (!is_get_param) {
          wle->gpm_size=size;
          wle->gpmp=start+0x10;
          is_get_param=1;
          if (!guest_pt_range_is_user_rw(vcpu, start, size*PAGE_SIZE_4K)) {
            dprintf(LOG_ERROR, "[TV] ERROR: SCODE_PARAM pages are not user writable!\n");
            return 1;
          }
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
          dprintf(LOG_TRACE, "calling guest_pt_range_is_user_rw\n");
          if (!guest_pt_range_is_user_rw(vcpu, start, size*PAGE_SIZE_4K)) {
            dprintf(LOG_ERROR, "[TV] ERROR: SCODE_STACK pages are not user writable!\n");
            return 1;
          }
          dprintf(LOG_TRACE, "returned from guest_pt_range_is_user_rw\n");
        }
      }
      break;
    default :
      break;
    }
    dprintf(LOG_TRACE, "[TV] section %d type %d addr %#x size %d\n",i, type, start, size);
  }

  return 0;
}


/* register scode in whitelist */
u32 scode_register(VCPU *vcpu, u32 scode_info, u32 scode_pm, u32 gventry) 
{
  size_t i;
  whitelist_entry_t whitelist_new;
  u64 gcr3;
  hpt_pmo_t reg_gpmo_root, pal_npmo_root, pal_gpmo_root;
  hptw_ctx_t reg_guest_walk_ctx;
  u32 err=0;

  if (hpt_guest_walk_ctx_construct_vcpu(&reg_guest_walk_ctx, vcpu, NULL)) {
    dprintf(LOG_ERROR, "scode_register: hpt_guest_walk_ctx_construct_vcpu failed\n");
    return 1;
  }

  /* set all CPUs to use the same 'reg' nested page tables,
     and set up a corresponding hpt_pmo.
  */
  /* XXX would make more sense to do this in init_scode, but there
     seems to be a race condition with all cores simultaneously trying
     to set up their EPTs and call emhf_app_main.
  */
  {
    static bool did_change_root_mappings=false;

    if (!did_change_root_mappings) {
      hpt_emhf_get_root_pmo(vcpu, &g_reg_npmo_root);
#ifdef __MP_VERSION__
      {
        size_t i;
        for( i=0 ; i<g_midtable_numentries ; i++ )  {
          dprintf(LOG_TRACE, "cpu %d setting root pm from %p to %p\n",
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

  gcr3 = VCPU_gcr3(vcpu);

  dprintf(LOG_TRACE, "\n[TV] ************************************\n");
  dprintf(LOG_TRACE, "[TV] ********** scode register **********\n");
  dprintf(LOG_TRACE, "[TV] ************************************\n");

  if (whitelist_size == whitelist_max)
    {
      dprintf(LOG_ERROR, "[TV] FATAL ERROR: too many registered scode, the limitation is %d\n", whitelist_max);
      err=1;
      goto out;
    }

  dprintf(LOG_TRACE, "[TV] CPU(0x%02x): add to whitelist,  scode_info %#x, scode_pm %#x, gventry %#x\n", vcpu->id, scode_info, scode_pm, gventry);

  /* ATTN: we should assign a ID for each registered sensitive code
   * so we know what to verify each time
   */
  whitelist_new.id = 0;
  whitelist_new.gcr3 = gcr3;
  whitelist_new.grsp = (u32)-1;

  /* store scode entry point */
  whitelist_new.entry_v = gventry;
  whitelist_new.entry_p = gpt_vaddr_to_paddr_current(vcpu, gventry); 
  dprintf(LOG_TRACE, "[TV] CR3 value is %#llx, entry point vaddr is %#x, paddr is %#x\n", gcr3, whitelist_new.entry_v, whitelist_new.entry_p);

  /* parse parameter structure */
  if (parse_params_info(vcpu, &(whitelist_new.params_info), scode_pm)) {
    dprintf(LOG_ERROR, "[TV] Registration Failed. Scode param info incorrect! \n");
    err=2;
    goto out;
  }
  whitelist_new.gpm_num = whitelist_new.params_info.num_params;
  /* register scode sections into whitelist entry */
  if (memsect_info_copy_from_guest(vcpu, &(whitelist_new.scode_info), scode_info)
      || memsect_info_register(vcpu, &(whitelist_new.scode_info), &whitelist_new)) {
    dprintf(LOG_ERROR, "[TV] Registration Failed. Scode section info incorrect! \n");
    err=3;
    goto out;
  }

  whitelist_new.npl = malloc(sizeof(pagelist_t));
  pagelist_init(whitelist_new.npl);

  whitelist_new.gpl = malloc(sizeof(pagelist_t));
  pagelist_init(whitelist_new.gpl);

  hpt_emhf_get_guest_root_pmo(vcpu, &reg_gpmo_root);
  pal_npmo_root = (hpt_pmo_t) {
    .t = g_reg_npmo_root.t,
    .lvl = g_reg_npmo_root.lvl,
    .pm = pagelist_get_zeroedpage(whitelist_new.npl),
  };
  pal_gpmo_root = (hpt_pmo_t) {
    .t = reg_gpmo_root.t,
    .lvl = reg_gpmo_root.lvl,
    .pm = pagelist_get_zeroedpage(whitelist_new.gpl),
  };

  /* we can use the same walk ctx for guest page tables as for
     nested page tables, because guest physical addresses are
     unity-mapped to system physical addresses. we also use the same
     walk ctx for both 'pal' and 'reg' page table sets for
     simplicity. */
  whitelist_new.hpt_nested_walk_ctx = hpt_nested_walk_ctx; /* copy from template */
  whitelist_new.hpt_nested_walk_ctx.gzp_ctx = whitelist_new.npl;

  hpt_guest_walk_ctx_construct(&whitelist_new.hpt_guest_walk_ctx,
                               &pal_npmo_root,
                               &whitelist_new.hpt_nested_walk_ctx,
                               whitelist_new.gpl);

  /* add all gpl pages to pal's nested page tables, ensuring that
     the guest page tables allocated from it will be accessible to the
     pal */
  /* XXX breaks pagelist abstraction. will break if pagelist ever dynamically
     allocates more buffers */
  dprintf(LOG_TRACE, "adding gpl to pal's npt:\n");
  for (i=0; i < whitelist_new.gpl->num_allocd; i++) {
    hpt_pmeo_t pmeo = {
      .pme = 0,
      .t = pal_npmo_root.t,
      .lvl = 1,
    };
    void *page = whitelist_new.gpl->page_base + i*PAGE_SIZE_4K;
    int hpt_err;
    hpt_pmeo_setprot(&pmeo, HPT_PROTS_RWX);
    hpt_pmeo_set_address(&pmeo, hva2spa(page));
    hpt_err = hptw_insert_pmeo_alloc(&whitelist_new.hpt_nested_walk_ctx,
                                         &pal_npmo_root,
                                         &pmeo,
                                         hva2gpa(page));
    ASSERT(!hpt_err);
  }

  dprintf(LOG_TRACE, "adding sections to pal's npts and gpts:\n");
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
    scode_lend_section(&g_reg_npmo_root, &whitelist_new.hpt_nested_walk_ctx,
                       &reg_gpmo_root, &reg_guest_walk_ctx,
                       &pal_npmo_root, &whitelist_new.hpt_nested_walk_ctx,
                       &pal_gpmo_root, &whitelist_new.hpt_guest_walk_ctx,
                       &whitelist_new.sections[i]);
  }

  /* clone gdt */
  dprintf(LOG_TRACE, "cloning gdt:\n");
  scode_clone_gdt(vcpu,
                  VCPU_gdtr_base(vcpu), VCPU_gdtr_limit(vcpu),
                  &pal_gpmo_root, &whitelist_new.hpt_guest_walk_ctx,
                  whitelist_new.gpl);

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
    int hpt_err;
    hpt_pmeo_setprot(&pmeo, HPT_PROTS_RX);
    hpt_pmeo_setuser(&pmeo, true);
    /* the gpa address here shouldn't matter, so long as it's one not
       accessible by the pal. we'll also set that to the sentinel
       return address value
    */
    hpt_pmeo_set_address(&pmeo, RETURN_FROM_PAL_ADDRESS);

    dprintf(LOG_TRACE, "[TV] generated pme for return gva address %x: lvl:%d %llx\n",
            RETURN_FROM_PAL_ADDRESS, pmeo.lvl, pmeo.pme);
    hpt_err = hptw_insert_pmeo_alloc(&whitelist_new.hpt_guest_walk_ctx,
                                         &pal_gpmo_root,
                                         &pmeo,
                                         RETURN_FROM_PAL_ADDRESS);
    ASSERT(!hpt_err);
  }

  whitelist_new.pal_npt_root = pal_npmo_root;
  whitelist_new.pal_gpt_root = pal_gpmo_root;
  whitelist_new.reg_gpt_root = reg_gpmo_root;
  whitelist_new.pal_gcr3 = hpt_cr3_set_address(whitelist_new.pal_gpt_root.t,
                                               VCPU_gcr3(vcpu), /* XXX should build trusted cr3 from scratch */
                                               hva2gpa(whitelist_new.pal_gpt_root.pm));

  /* flush TLB for page table modifications to take effect */
  emhf_memprot_flushmappings(vcpu);

  /* initialize Micro-TPM instance */
  utpm_init_instance(&whitelist_new.utpm);

  /* extent uTPM PCR[0] with with hash of each section metadata and contents */
  if (scode_measure_sections(&whitelist_new.utpm, &whitelist_new))
    {
      dprintf(LOG_ERROR, "[TV] SECURITY: Registration Failed. sensitived code cannot be verified.\n");
      err=4;
      goto out;
    }

#ifdef __MP_VERSION__
  /* initialize PAL running lock */
  whitelist_new.pal_running_lock=1;
  whitelist_new.pal_running_vcpu_id=-1;
#endif

  /* add new entry into whitelist */
  /* CRITICAL SECTION in MP scenario: need to quiesce other CPUs or at least acquire spinlock */
  for (i = 0; (whitelist[i].gcr3!=0); i ++);
  if (i >= whitelist_max) {
    dprintf(LOG_ERROR, "[TV] FATAL ERROR: no room for new scode, the limitation is %d\n", whitelist_max);
    err=5;
    goto out;
  }
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

 out:
  hpt_guest_walk_ctx_destroy(&reg_guest_walk_ctx);
  return err;
}

/* unregister scode in whitelist */
u32 scode_unregister(VCPU * vcpu, u32 gvaddr) 
{
  size_t i, j;

  u64 gcr3;

  gcr3 = VCPU_gcr3(vcpu);

  dprintf(LOG_TRACE, "\n[TV] ************************************\n");
  dprintf(LOG_TRACE, "[TV] ********* scode unregister *********\n");
  dprintf(LOG_TRACE, "[TV] ************************************\n");

  if (whitelist_size == 0) {
    dprintf(LOG_ERROR, "[TV] FATAL ERROR: no scode registered currently\n");
    return 1;
  }

  dprintf(LOG_TRACE, "[TV] CPU(%02x): remove from whitelist gcr3 %#llx, gvaddr %#x\n", vcpu->id, gcr3, gvaddr);

  for (i = 0; i < whitelist_max; i ++) {
    /* find scode with correct cr3 and entry point */
    if ((whitelist[i].gcr3 == gcr3) && (whitelist[i].entry_v == gvaddr))
      break;
  }

  if (i >= whitelist_max) {
    dprintf(LOG_ERROR, "[TV] SECURITY: UnRegistration Failed. no matching sensitive code found\n");
    return 1;
  }

  /* dump perf counters */
  dprintf(LOG_PROFILE, "performance counters:\n");
  for(j=0; j<TV_PERF_CTRS_COUNT; j++) {
    dprintf(LOG_PROFILE, "  %s total: %Lu count: %Lu\n",
            g_tv_perf_ctr_strings[j],
            perf_ctr_get_total_time(&g_tv_perf_ctrs[j]),
            perf_ctr_get_count(&g_tv_perf_ctrs[j]));
  }
  dprintf(LOG_PROFILE, "total mem mallocd: %u\n", heapmem_get_used_size());

  /* restore permissions for remapped sections */
  for(j = 0; j < whitelist[i].sections_num; j++) {
    /* zero the contents of any sections that are writable by the PAL, and not readable by the reg guest */
    if ((whitelist[i].sections[j].pal_prot & HPT_PROTS_W)
        && !(whitelist[i].sections[j].reg_prot & HPT_PROTS_R)) {
      int err;
      dprintf(LOG_TRACE, "[TV] zeroing section %d\n", j);
      err = hptw_checked_memset_va(&whitelist[i].hpt_guest_walk_ctx, &whitelist[i].pal_gpt_root,
                                   HPTW_CPL3,
                                   whitelist[i].sections[j].pal_gva, 0, whitelist[i].sections[j].size);
      /* should only fail if insufficient permissions in the guest
         page tables, which TV constructed and the PAL should not have
         been able to modify */
      ASSERT(!err);
    }

    scode_return_section(&g_reg_npmo_root, &whitelist[i].hpt_nested_walk_ctx,
                         &whitelist[i].pal_npt_root, &whitelist[i].hpt_nested_walk_ctx,
                         &whitelist[i].pal_gpt_root, &whitelist[i].hpt_guest_walk_ctx,
                         &whitelist[i].sections[j]);
  }
  /* flush TLB for page table modifications to take effect */
  emhf_memprot_flushmappings(vcpu);

  /* delete entry from scode whitelist */
  /* CRITICAL SECTION in MP scenario: need to quiesce other CPUs or at least acquire spinlock */
  whitelist_size --;
  whitelist[i].gcr3 = 0;

  hpt_guest_walk_ctx_destroy(&whitelist[i].hpt_guest_walk_ctx);

  pagelist_free_all(whitelist[i].npl);
  free(whitelist[i].npl);

  pagelist_free_all(whitelist[i].gpl);
  free(whitelist[i].gpl);

  return 0; 
}

/* test if the page is already in page_list
 * in order to avoid redundency in expose_page() */
int test_page_in_list(pte_t * page_list, pte_t page, u32 count)
{
  size_t i;
  for( i=0 ; i<count ; i++ )  {
    if (page_list[i]==page)
      return 1;
  }
  return 0;
}

u32 scode_marshall(VCPU * vcpu)
{
  u32 pm_addr, pm_addr_base, pm_value, pm_tmp;  /*parameter stack base address*/
  u32 pm_type, pm_size, pm_size_sum; /*save pm information*/
  int pm_i;
  u32 grsp;
  u32 new_rsp;
  int curr=scode_curr[vcpu->id];
  u32 err=0;
  hptw_ctx_t vcpu_guest_walk_ctx;
  hpt_pmo_t vcpu_guest_root;

  if (hpt_guest_walk_ctx_construct_vcpu(&vcpu_guest_walk_ctx, vcpu, NULL)) {
    dprintf(LOG_ERROR, "scode_marshall: hpt_guest_walk_ctx_construct_vcpu failed\n");
    err=1;
    goto out;
  }
  hpt_emhf_get_guest_root_pmo(vcpu, &vcpu_guest_root);

  perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_MARSHALL], vcpu->idx);

  dprintf(LOG_TRACE, "[TV] marshalling scode parameters!\n");
  if(whitelist[curr].gpm_num == 0) {
    dprintf(LOG_TRACE, "[TV] params number is 0. Return!\n");
    goto out;
  }

  /* memory address for input parameter in sensitive code */
  pm_addr_base = whitelist[curr].gpmp;
  dprintf(LOG_TRACE, "[TV] parameter page base address is %#x\n", pm_addr_base);

  /* address for parameters in guest stack */
  grsp = (u32)whitelist[curr].grsp + 4; /*the stack pointer of parameters in guest stack*/

  /* save params number */
  pm_addr = pm_addr_base;
  put_32bit_aligned_value_to_guest(&whitelist[curr].hpt_guest_walk_ctx,
                                   &whitelist[curr].pal_gpt_root,
                                   pm_addr,
                                   whitelist[curr].gpm_num);
  pm_addr += 4;
  pm_size_sum = 4; /*memory used in input pms section*/
  dprintf(LOG_TRACE, "[TV] params number is %d\n", whitelist[curr].gpm_num);

  if (whitelist[curr].gpm_num > TV_MAX_PARAMS) {
    dprintf(LOG_ERROR, "[TV] Fail: param num is too big!\n");
    err=1;
    goto out;
  }

  /* begin to process the params*/
  for (pm_i = whitelist[curr].gpm_num-1; pm_i >= 0; pm_i--) /*the last parameter should be pushed in stack first*/
    {
      /* get param information*/
      pm_type = whitelist[curr].params_info.params[pm_i].type;
      pm_size = whitelist[curr].params_info.params[pm_i].size;
      /* get param value from guest stack */
      if (copy_from_current_guest(vcpu, &pm_value, grsp + pm_i*4, sizeof(u32))) {
        dprintf(LOG_ERROR, "[TV] scode_marshall failed to copy from guest\n");
        err=2;
        goto out;
      }
      dprintf(LOG_TRACE, "scode_marshal copied param %d\n", pm_i);

      pm_size_sum += 12;
      if (pm_size_sum > (whitelist[curr].gpm_size*PAGE_SIZE_4K)) {
        dprintf(LOG_ERROR, "[TV] Fail: No enough space to save input params data!\n");
        err=3;
        goto out;
      }

      /* save input params in input params memory for sensitive code */
      if (hptw_checked_copy_to_va(&whitelist[curr].hpt_guest_walk_ctx,
                                  &whitelist[curr].pal_gpt_root,
                                  HPTW_CPL3,
                                  pm_addr,
                                  &pm_type, sizeof(pm_type))
          ||
          hptw_checked_copy_to_va(&whitelist[curr].hpt_guest_walk_ctx,
                                  &whitelist[curr].pal_gpt_root,
                                  HPTW_CPL3,
                                  pm_addr+sizeof(pm_type),
                                  &pm_size, sizeof(pm_size))
          ||
          hptw_checked_copy_to_va(&whitelist[curr].hpt_guest_walk_ctx,
                                  &whitelist[curr].pal_gpt_root,
                                  HPTW_CPL3,
                                  pm_addr+sizeof(pm_type)+sizeof(pm_size),
                                  &pm_value, sizeof(pm_value))) {
        dprintf(LOG_ERROR, "[TV] scode_marshall: couldn't write to param area\n");
        err=4;
        goto out;
      }
      pm_addr += sizeof(pm_type)+sizeof(pm_size)+sizeof(pm_addr);
      dprintf(LOG_TRACE, "scode_marshal copied metadata to params area\n");      

      switch (pm_type)
        {
        case TV_PAL_PM_INTEGER: /* integer */
          {        
            /* put the parameter value in sensitive code stack */
            pm_tmp = pm_value;
            dprintf(LOG_TRACE, "[TV]   PM %d is a integer (size %d, value %#x)\n", pm_i, pm_size, pm_value);
            break;
          }
        case TV_PAL_PM_POINTER: /* pointer */
          {
            /*copy data from guest space to sensitive code*/
            pm_size_sum += 4*pm_size;
            if (pm_size_sum > (whitelist[curr].gpm_size*PAGE_SIZE_4K)) {
              dprintf(LOG_ERROR, "[TV] Fail: Not enough space to save input params data!\n");
              err=5;
              goto out;
            }
            dprintf(LOG_TRACE, "[TV]   PM %d is a pointer (size %d, value %#x)\n", pm_i, pm_size, pm_value);

            if (hptw_checked_copy_va_to_va(&whitelist[curr].hpt_guest_walk_ctx,
                                           &whitelist[curr].pal_gpt_root,
                                           HPTW_CPL3,
                                           pm_addr,
                                           &vcpu_guest_walk_ctx,
                                           &vcpu_guest_root,
                                           HPTW_CPL3,
                                           pm_value,
                                           pm_size*4)) {
              dprintf(LOG_ERROR, "[TV] scode_marshall failed to copy to params\n");
              err=6;
              goto out;
            }

            /* put pointer address in sensitive code stack*/
            pm_tmp = pm_addr;
            pm_addr += 4*pm_size;
            break;
          }
        default: /* other */
          dprintf(LOG_ERROR, "[TV] Fail: unknown parameter %d type %d \n", pm_i, pm_type);
          err=7;
          goto out;
        }
      new_rsp = VCPU_grsp(vcpu)-4;
      VCPU_grsp_set(vcpu, new_rsp);
      put_32bit_aligned_value_to_guest(&whitelist[curr].hpt_guest_walk_ctx,
                                       &whitelist[curr].pal_gpt_root,
                                       new_rsp, pm_tmp);
    }

 out:
  hpt_guest_walk_ctx_destroy(&vcpu_guest_walk_ctx);
  perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_MARSHALL], vcpu->idx);
  return err;
}



//todo: switch from regular code to sensitive code
u32 hpt_scode_switch_scode(VCPU * vcpu)
{
  int curr=scode_curr[vcpu->id];

  perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_SWITCH_SCODE], vcpu->idx);

  dprintf(LOG_TRACE, "\n[TV] ************************************\n");
  dprintf(LOG_TRACE, "[TV] ********* switch to scode **********\n");
  dprintf(LOG_TRACE, "[TV] ************************************\n");

  /* save the guest stack pointer and set new stack pointer to scode stack */
  dprintf(LOG_TRACE, "[TV] saved guest regular stack %#x, switch to sensitive code stack %#x\n", (u32)VCPU_grsp(vcpu), whitelist[curr].gssp);
  whitelist[curr].grsp = (u32)VCPU_grsp(vcpu);
  VCPU_grsp_set(vcpu, whitelist[curr].gssp);

  if (copy_from_current_guest(vcpu,
                              &whitelist[curr].return_v,
                              whitelist[curr].grsp,
                              sizeof(void*))) {
    dprintf(LOG_ERROR, "switch_scode: Couldn't read return address\n");
  }
  dprintf(LOG_TRACE, "[TV] scode return vaddr is %#x\n", whitelist[curr].return_v);

  /* input parameter marshalling */
  if (scode_marshall(vcpu)){
    /* error in parameter marshalling */
    /* restore regular code stack */
    VCPU_grsp_set(vcpu, whitelist[curr].grsp);
    whitelist[curr].grsp = (u32)-1; 
    return 1;
  }

  /* find all PTE pages related to access scode and GDT */
  /* change NPT permission for all PTE pages and scode pages */
  dprintf(LOG_TRACE, "[TV] change NPT permission to run PAL!\n");
  hpt_emhf_set_root_pm(vcpu, whitelist[curr].pal_npt_root.pm);
  VCPU_gcr3_set(vcpu, whitelist[curr].pal_gcr3);
  emhf_memprot_flushmappings(vcpu); /* XXX */

  /* disable interrupts */
  VCPU_grflags_set(vcpu, VCPU_grflags(vcpu) & ~EFLAGS_IF);

  /* XXX FIXME- what's the right thing here? Keeping 'legacy' behavior
     of setting this flag for AMD only and doing nothing for INTEL for
     now */
  if(vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    /* set the sensitive code to run in ring 3 */
    ((struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr))->cpl = 3;
  }

  /* write the sentinel return address to scode stack */
  VCPU_grsp_set(vcpu, VCPU_grsp(vcpu)-4);
  put_32bit_aligned_value_to_guest(&whitelist[curr].hpt_guest_walk_ctx,
                                   &whitelist[curr].pal_gpt_root,
                                   (u32)VCPU_grsp(vcpu), RETURN_FROM_PAL_ADDRESS);
  dprintf(LOG_TRACE, "[TV] host stack pointer before running scode is %#x\n",(u32)VCPU_grsp(vcpu));

  perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_SWITCH_SCODE], vcpu->idx);
  return 0;
}

u32 scode_unmarshall(VCPU * vcpu)
{
  u32 pm_addr_base, pm_addr;
  size_t i;
  u32 pm_num, pm_type, pm_size, pm_value;

  int curr=scode_curr[vcpu->id];

  dprintf(LOG_TRACE, "[TV] unmarshalling scode parameters!\n");
  if (whitelist[curr].gpm_num == 0)
    {
      dprintf(LOG_TRACE, "[TV] unmarshall pm numbuer is 0. Return!\n");
      return 0;
    }

  /* memory address for input parameter in sensitive code */
  pm_addr_base = whitelist[curr].gpmp;
  dprintf(LOG_TRACE, "[TV] parameter page base address is %#x\n", pm_addr_base);

  /* get params number */
  pm_addr = pm_addr_base;
  pm_num = get_32bit_aligned_value_from_guest(&whitelist[curr].hpt_guest_walk_ctx,
                                              &whitelist[curr].pal_gpt_root,
                                              (u32)pm_addr);
  pm_addr += 4;
  dprintf(LOG_TRACE, "[TV] params number is %d\n", pm_num);
  if (pm_num > TV_MAX_PARAMS)
    {
      dprintf(LOG_ERROR, "[TV] Fail: parameter number too big!\n");
      return 1;
    }
  /* begin to process the params*/
  for (i = 0; i < pm_num; i++) /*the last parameter should be pushed in stack first*/
    {
      /* get param information*/
      pm_type =  get_32bit_aligned_value_from_guest(&whitelist[curr].hpt_guest_walk_ctx,
                                                    &whitelist[curr].pal_gpt_root,
                                                    (u32)pm_addr);
      pm_addr += 4;

      switch (pm_type)
        {
        case TV_PAL_PM_INTEGER: /*integer*/
          {
            /* don't need to put integer back to regular code stack */
            pm_addr += 8; 
            dprintf(LOG_TRACE, "[TV]   skip an integer parameter!\n"); 
            break;
          }
        case TV_PAL_PM_POINTER: /* pointer */
          {
            pm_size =  get_32bit_aligned_value_from_guest(&whitelist[curr].hpt_guest_walk_ctx,
                                                          &whitelist[curr].pal_gpt_root,
                                                          (u32)pm_addr);
            /* get pointer adddress in regular code */
            pm_value = get_32bit_aligned_value_from_guest(&whitelist[curr].hpt_guest_walk_ctx,
                                                          &whitelist[curr].pal_gpt_root,
                                                          (u32)pm_addr+4);
            pm_addr += 8;

            dprintf(LOG_TRACE, "[TV]   PM %d is a pointer (size %d, addr %#x)\n", i,  pm_size*4, pm_value);
            /* copy data from sensitive code (param space) to guest */
            hptw_checked_copy_va_to_va(&whitelist[curr].hpt_guest_walk_ctx,
                                       &whitelist[curr].reg_gpt_root,
                                       HPTW_CPL3,
                                       pm_value,
                                       &whitelist[curr].hpt_guest_walk_ctx,
                                       &whitelist[curr].reg_gpt_root,
                                       HPTW_CPL3,
                                       pm_addr,
                                       pm_size*4);
            pm_addr += 4*pm_size;
            break;
          }

        default: /* other */
          dprintf(LOG_ERROR, "[TV] Fail: unknown parameter %d type %d \n", i, pm_type);
          return 1;
        } // end switch

    } //end for loop 
  return 0;
}

//switch from sensitive code to regular code
u32 hpt_scode_switch_regular(VCPU * vcpu)
{
  int curr=scode_curr[vcpu->id];

  perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_SWITCH_REGULAR], vcpu->idx);

  dprintf(LOG_TRACE, "\n[TV] ************************************\n");
  dprintf(LOG_TRACE, "[TV] ***** switch to regular code  ******\n");
  dprintf(LOG_TRACE, "[TV] ************************************\n");

  /* marshalling parameters back to regular code */
  if (scode_unmarshall(vcpu)){
    dprintf(LOG_ERROR, "hpt_scode_switch_regular: error in scode_unmarshall\n");
    return 1;
  }

  /* release shared pages */
  scode_release_all_shared_pages(vcpu, &whitelist[curr]);

  /* clear the NPT permission setting in switching into scode */
  dprintf(LOG_TRACE, "[TV] change NPT permission to exit PAL!\n"); 
  hpt_emhf_set_root_pm(vcpu, g_reg_npmo_root.pm);
  VCPU_gcr3_set(vcpu, whitelist[curr].gcr3);
  emhf_memprot_flushmappings(vcpu); /* XXX */

  /* switch back to regular stack */
  dprintf(LOG_TRACE, "[TV] switch from scode stack %#x back to regular stack %#x\n", (u32)VCPU_grsp(vcpu), (u32)whitelist[curr].grsp);
  VCPU_grsp_set(vcpu, whitelist[curr].grsp + 4);
  whitelist[curr].grsp = (u32)-1;

  /* enable interrupts */
  VCPU_grflags_set(vcpu, VCPU_grflags(vcpu) | EFLAGS_IF);

  dprintf(LOG_TRACE, "[TV] stack pointer before exiting scode is %#x\n",(u32)VCPU_grsp(vcpu));

  /* return to actual return address */
  VCPU_grip_set(vcpu, whitelist[curr].return_v);

  perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_SWITCH_REGULAR], vcpu->idx);

  return 0;
}

static bool hpt_error_wasInsnFetch(VCPU *vcpu, u64 errorcode)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return (errorcode & EPT_ERRORCODE_EXEC);
  } else if (vcpu->cpu_vendor != CPU_VENDOR_AMD) {
    ASSERT(0);
  }	
  return (errorcode & PF_ERRORCODE_INST);
}

/*  EPT violation handler */
u32 hpt_scode_npf(VCPU * vcpu, u32 gpaddr, u64 errorcode)
{
  int index = -1;

  int * curr=&(scode_curr[vcpu->id]);
  u64 gcr3 = VCPU_gcr3(vcpu);
  u32 rip = (u32)VCPU_grip(vcpu);

  perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_NPF], vcpu->idx);

  dprintf(LOG_TRACE, "[TV] CPU(%02x): nested page fault!(rip %#x, gcr3 %#Lx, gpaddr %#x, errorcode %Lx)\n",
          vcpu->id, rip, gcr3, gpaddr, errorcode);

  if(!hpt_error_wasInsnFetch(vcpu, errorcode)) {
    /* data read or data write */
    dprintf(LOG_ERROR, "[TV] SECURITY: nested page fault on non-instruction fetch.\n");
    goto npf_error;
  }

  index = scode_in_list(gcr3, rip);
  if ((*curr == -1) && (index >= 0)) {
    /* regular code to sensitive code */

    *curr = index;
    if (!((whitelist[*curr].entry_v == rip) && (whitelist[*curr].entry_p == gpaddr))) { 
      dprintf(LOG_ERROR, "[TV] SECURITY: invalid scode entry point!\n");
      goto npf_error;
    }

    /* valid entry point, switch from regular code to sensitive code */
#ifdef __MP_VERSION__
    spin_lock(&(whitelist[*curr].pal_running_lock));
    whitelist[*curr].pal_running_vcpu_id=vcpu->id;
    dprintf(LOG_TRACE, "got pal_running lock!\n");
#endif
    if (hpt_scode_switch_scode(vcpu)) {
      dprintf(LOG_ERROR, "[TV] error in switch to scode!\n");
#ifdef __MP_VERSION__
      spin_unlock(&(whitelist[*curr].pal_running_lock));
      whitelist[*curr].pal_running_vcpu_id=-1;
      dprintf(LOG_TRACE, "released pal_running lock!\n");
#endif
      goto npf_error;
    }
  } else if ((*curr >=0) && (index < 0)) {
    /* sensitive code to regular code */

    if (RETURN_FROM_PAL_ADDRESS != rip) {
      dprintf(LOG_ERROR, "[TV] SECURITY: invalid scode return point!\n");
      goto npf_error;
    }
    /* valid return point, switch from sensitive code to regular code */

    /* XXX FIXME: now return ponit is extracted from regular code stack, only support one scode function call */
    if (hpt_scode_switch_regular(vcpu)) {
      dprintf(LOG_ERROR, "[TV] error in switch to regular code!\n");
#ifdef __MP_VERSION__
      spin_unlock(&(whitelist[*curr].pal_running_lock));
      whitelist[*curr].pal_running_vcpu_id=-1;
      dprintf(LOG_TRACE, "released pal_running lock!\n");
#endif
      goto npf_error;
    }
#ifdef __MP_VERSION__
    spin_unlock(&(whitelist[*curr].pal_running_lock));
    whitelist[*curr].pal_running_vcpu_id=-1;
    dprintf(LOG_TRACE, "released pal_running lock!\n");
#endif
    *curr = -1;
  } else if ((*curr >=0) && (index >= 0)) {
    /* sensitive code to sensitive code */
    if (*curr == index)
      dprintf(LOG_ERROR, "[TV] SECURITY: incorrect scode EPT configuration!\n");
    else
      dprintf(LOG_ERROR, "[TV] SECURITY: invalid access to scode mem region from other scodes!\n"); 
#ifdef __MP_VERSION__
    spin_unlock(&(whitelist[*curr].pal_running_lock));
    whitelist[*curr].pal_running_vcpu_id=-1;
    dprintf(LOG_TRACE, "released pal_running lock!\n");
#endif
    goto npf_error;	
  } else {
    /* regular code to regular code */
    dprintf(LOG_ERROR, "[TV] incorrect regular code EPT configuration!\n"); 
    goto npf_error;
  }

  /* no errors, pseodu page fault canceled by nested paging */
  if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->eventinj.bytes = 0ull;
  } /* FIXME - equivalent for intel? */

  perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_NPF], vcpu->idx);
  return 0;

 npf_error:
  perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_NPF], vcpu->idx);

  if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    /* errors, inject segfault to guest */
    struct vmcb_struct* vmcb = (struct vmcb_struct*)(vcpu->vmcb_vaddr_ptr);
    vmcb->eventinj.bytes=0;
    vmcb->eventinj.fields.vector=0xd;
    vmcb->eventinj.fields.vector=EVENTTYPE_EXCEPTION;
    vmcb->eventinj.fields.v=0x1;
  } /* FIXME - equivalent for intel? */

  *curr = -1;
  return 1;
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
    dprintf(LOG_TRACE, "returning shared section num %d at 0x%08llx\n", i, wle->sections[i].pal_gva);
    scode_return_section(&g_reg_npmo_root, &wle->hpt_nested_walk_ctx,
                         &wle->pal_npt_root, &wle->hpt_nested_walk_ctx,
                         &wle->pal_gpt_root, &wle->hpt_guest_walk_ctx,
                         &wle->sections[i]);
    wle->sections_num--;
  }
}

/* note- caller is responsible for flushing page tables afterwards */
u32 scode_share_range(VCPU * vcpu, whitelist_entry_t *wle, u32 gva_base, u32 gva_len)
{
  u32 err=0;
  hptw_ctx_t vcpu_guest_walk_ctx;
  hpt_pmo_t vcpu_guest_root;
  if (hpt_guest_walk_ctx_construct_vcpu(&vcpu_guest_walk_ctx, vcpu, NULL)) {
    dprintf(LOG_ERROR, "[TV] scode_share_range: scode_share_range failed\n");
    err=1;
    goto out;
  }
  hpt_emhf_get_guest_root_pmo(vcpu, &vcpu_guest_root);

  if (wle->sections_num >= TV_MAX_SECTIONS) {
    dprintf(LOG_ERROR, "[TV] scode_share_range: max sections (%d) limit exceeded\n", TV_MAX_SECTIONS);
    err=2;
    goto out;
  }

  wle->sections[wle->sections_num] = (tv_pal_section_int_t) {
    .reg_gva = gva_base,
    .pal_gva = gva_base,
    .size = gva_len,
    .pal_prot = pal_prot_of_type(TV_PAL_SECTION_SHARED),
    .reg_prot = reg_prot_of_type(TV_PAL_SECTION_SHARED),
    .section_type = TV_PAL_SECTION_SHARED,
  };

  scode_lend_section(&g_reg_npmo_root, &wle->hpt_nested_walk_ctx,
                     &vcpu_guest_root, &vcpu_guest_walk_ctx,
                     &wle->pal_npt_root, &wle->hpt_nested_walk_ctx,
                     &wle->pal_gpt_root, &wle->hpt_guest_walk_ctx,
                     &wle->sections[wle->sections_num]);

  wle->sections_num++;

 out:
  hpt_guest_walk_ctx_destroy(&vcpu_guest_walk_ctx);

  return err;
}

u32 scode_share_ranges(VCPU * vcpu, u32 scode_entry, u32 gva_base[], u32 gva_len[], u32 count)
{
  size_t i;
  whitelist_entry_t* entry;

  if (!(entry = find_scode_by_entry(VCPU_gcr3(vcpu), scode_entry))) {
    dprintf(LOG_ERROR, "[TV] scode_share: Invalid entry pt %x\n", scode_entry);
    return 1;
  }

  for(i=0; i<count; i++) {
    if(scode_share_range(vcpu, entry, gva_base[i], gva_len[i])) {
      dprintf(LOG_TRACE, "[TV] scode_share_ranges releasing all shared pages\n");
      scode_release_all_shared_pages(vcpu, entry);
      return 1;
    }
  }

  /* flush TLB for page table modifications to take effect */
  emhf_memprot_flushmappings(vcpu);
  
  return 0;
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:nil */
/* c-basic-offset:2 */
/* End:             */
