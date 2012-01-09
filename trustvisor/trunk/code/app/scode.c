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
#include <pt2.h>
#include <tv_utpm.h> /* formerly utpm.h */
#include <rsa.h>
#include <random.h>
#include <crypto_init.h>
#include <sha1.h>

static void scode_expose_arch(VCPU *vcpu, whitelist_entry_t *wle);
static void scode_unexpose_arch(VCPU *vcpu, whitelist_entry_t *wle);

hpt_walk_ctx_t hpt_nested_walk_ctx;
hpt_walk_ctx_t hpt_guest_walk_ctx;

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
					dprintf(LOG_TRACE, "[TV] find gvaddr %#x in scode %d section No.%d !\n", gvaddr, i, j+1);
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

/* FIXME: should this be in crypto_init.c? */
u32 scode_measure(utpm_master_state_t *utpm, pte_t *pte_pages, u32 size)
{
	size_t i; 
	u32 paddr;
	SHA_CTX ctx;
	TPM_DIGEST sha1sum;

	dprintf(LOG_TRACE, "[TV] measure scode and extend uTPM PCR value!\n");
	SHA1_Init(&ctx);
	for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
	{
		/* only measure SCODE, STEXT, SDATA pages */
		paddr = PAGE_ALIGN_4K(pte_pages[i]);
		switch(SCODE_PTE_TYPE_GET(pte_pages[i])) {
		case TV_PAL_SECTION_CODE:
		case TV_PAL_SECTION_SHARED_CODE:
		case TV_PAL_SECTION_DATA:
			dprintf(LOG_TRACE, "[TV]   measure scode page %d paddr %#x\n", i+1, paddr);
			SHA1_Update(&ctx, (u8 *)paddr, PAGE_SIZE_4K);
			break;
		case TV_PAL_SECTION_PARAM:
		case TV_PAL_SECTION_STACK:
		case TV_PAL_SECTION_SHARED:
			dprintf(LOG_TRACE, "[TV]   ignore scode page %d paddr %#x\n", i+1, paddr);
			break;
		default:
			ASSERT(0);
		}
	}
	SHA1_Final(sha1sum.value, &ctx);

	/* extend pcr 0 */
	utpm_extend(&sha1sum, utpm, 0);

	return 0;
}

hpt_pa_t hpt_nested_ptr2pa(void __attribute__((unused)) *ctx, void *ptr)
{
	return hva2spa(ptr);
}
void* hpt_nested_pa2ptr(void __attribute__((unused)) *ctx, hpt_pa_t ptr)
{
	return spa2hva(ptr);
}

hpt_pa_t hpt_guest_ptr2pa(void __attribute__((unused)) *ctx, void *ptr)
{
	return hva2gpa(ptr);
}
void* hpt_guest_pa2ptr(void __attribute__((unused)) *ctx, hpt_pa_t ptr)
{
	return gpa2hva(ptr);
}

void* hpt_get_zeroed_page(void *ctx, size_t alignment, size_t sz)
{
	pagelist_t *pl = ctx;
	ASSERT(PAGE_SIZE_4K % alignment == 0);
	ASSERT(sz <= PAGE_SIZE_4K);
	return pagelist_get_zeroedpage(pl);
}

/* initialize all the scode related variables and buffers */
void init_scode(VCPU * vcpu)
{
	size_t inum, max;

	/* initialize perf counters. this needs to happen before anythings gets profiled
	 * to prevent deadlock.
	 */
	{
		int j;
		for(j=0; j<TV_PERF_CTRS_COUNT; j++) {
			perf_ctr_init(&g_tv_perf_ctrs[j]);
		}
	}

	/* set up page walk context */
	{
		hpt_type_t t;
		if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
			t = HPT_TYPE_EPT;
		} else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
			t = HPT_TYPE_PAE;
		} else {
			ASSERT(0);
		}
		hpt_nested_walk_ctx = (hpt_walk_ctx_t) {
			.t = t,
			.gzp = hpt_get_zeroed_page,
			.gzp_ctx = NULL, /* we'll copy this struct for
													each pal and give each it's own allocation
													pool */
			.pa2ptr = hpt_nested_pa2ptr,
			.ptr2pa = hpt_nested_ptr2pa,
			.ptr2pa_ctx = NULL,
		};
	}
	{
		hpt_guest_walk_ctx = (hpt_walk_ctx_t) {
			.t = HPT_TYPE_INVALID, /* need to check gcr4 after OS is up and running */
			.gzp = hpt_get_zeroed_page,
			.gzp_ctx = NULL, /* add allocation pool on-demand */
			.pa2ptr = hpt_guest_pa2ptr,
			.ptr2pa = hpt_guest_ptr2pa,
			.ptr2pa_ctx = NULL,
		};
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
	scode_curr = (int *)malloc((max+1)<<2);
	memset(scode_curr, 0xFF, ((max+1)<<2));

	/* init PRNG and long-term crypto keys */
	if(trustvisor_master_crypto_init()) {
			dprintf(LOG_ERROR, "[TV] trustvisor_master_crypto_init() FAILED! SECURITY HALT!\n");
			HALT();			
	}
	dprintf(LOG_TRACE, "[TV] trustvisor_master_crypto_init successful.\n");
}

/* HPT related SCODE routines */

/* ************************************
 * set up scode pages permission
 *
 * on all CPUs:
 * Section type		Real Permission  PTE permission
 * SENTRY(SCODE) 	RE					unpresent
 * STEXT			RE					RE
 * SDATA 			RW					unpresent
 * SPARAM			RW					unpresent
 * SSTACK			RW					unpresent
 *
 * **************************************/
u32 hpt_scode_set_prot(VCPU *vcpu, pte_t *pte_pages, u32 size)
{
	size_t i; 
	u32 pfn;
	u32 k;
	VCPU * tmpcpu;

	dprintf(LOG_TRACE, "[TV] scode registration on local CPU %02x!\n", vcpu->id);
	for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
	{
		pfn = pte_pages[i] >> PAGE_SHIFT_4K;
		if (test_page_scode_bitmap(pfn)) {
			dprintf(LOG_ERROR, "[TV] Set scode page permission error! pfn %#x have already been registered!\n", pfn);
			break;
		}
	}

	for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
	{
		pfn = pte_pages[i] >> PAGE_SHIFT_4K;
		set_page_scode_bitmap(pfn);
//			set_page_scode_bitmap_2M(pfn);

		/* XXX FIXME: temporary disable DEV setting here! */
		//	set_page_dev_prot(pfn);

		/* XXX FIXME: do we need to grab a lock? */
		for(k=0; k<g_midtable_numentries; k++) {
			tmpcpu = (VCPU *)(g_midtable[k].vcpu_vaddr_ptr);
			hpt_nested_set_prot(tmpcpu, pte_pages[i]);
		}
	}

	return 0;
}

void hpt_scode_clear_prot(VCPU * vcpu, pte_t *pte_pages, u32 size)
{
	size_t i; 
	u32 pfn;
#ifdef __MP_VERSION__
	size_t k;
	VCPU * tmpcpu;
#endif

	/* set up page permission in local CPU */
	dprintf(LOG_TRACE, "[TV] scode unreg on local CPU %02x!\n", vcpu->id);
	for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
	{
		pfn = pte_pages[i] >> PAGE_SHIFT_4K;
		if (test_page_scode_bitmap(pfn))
		{
			/* XXX FIXME: temporary disable DEV setting here! */
			//clear_page_dev_prot(pfn);
			hpt_nested_clear_prot(vcpu, pte_pages[i]);

			clear_page_scode_bitmap(pfn);
//			if (clear_page_scode_bitmap_2M(pfn) == 0)
//				nested_promote(vcpu, pfn);
		}
	}

#ifdef __MP_VERSION__
	/* not local CPU, set all mem sections unpresent */
	for( k=0 ; k<g_midtable_numentries ; k++ )  {
		tmpcpu = (VCPU *)(g_midtable[k].vcpu_vaddr_ptr);
		if (tmpcpu->id != vcpu->id) {
			dprintf(LOG_TRACE, "[TV] scode unreg on CPU %02x!\n", tmpcpu->id);
			for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
			{
				pfn = pte_pages[i] >> PAGE_SHIFT_4K;
				/* XXX FIXME: temporary disable DEV setting here! */
				//	set_page_dev_prot(pfn);
				hpt_nested_clear_prot(tmpcpu, pte_pages[i]);
			}
		}
	}
#endif

}

/* parse scode paramter info ( scode registration input) */
int parse_params_info(VCPU * vcpu, struct tv_pal_params* pm_info, u32 pm_addr)
{
	size_t i, num;
	u32 addr;
	addr = pm_addr;
	/* get parameter number */
	num = pm_info->num_params = get_32bit_aligned_value_from_current_guest(vcpu,
																																				 addr);
	addr += 4;
	dprintf(LOG_TRACE, "[TV] pm_info %#x, # of paramters is %d\n", pm_addr, num);
	if (num > TV_MAX_PARAMS) {
		dprintf(LOG_ERROR, "[TV] number of scode sections exceeds limit!\n");
		return 1;
	}

	for (i = 0; i < num; i++)
	{
		pm_info->params[i].type = get_32bit_aligned_value_from_current_guest(vcpu, addr);
		pm_info->params[i].size = get_32bit_aligned_value_from_current_guest(vcpu, addr+4);
		dprintf(LOG_TRACE, "[TV] parameter %d type %d size %d\n", i+1, pm_info->params[i].type, pm_info->params[i].size);
		addr += 8;
	}
	return 0;
}

int memsect_info_copy_from_guest(VCPU * vcpu, struct tv_pal_sections *ps_scode_info, u32 gva_scode_info)
{
	size_t gva_scode_info_offset = 0;

	/* get parameter number */
	ps_scode_info->num_sections = get_32bit_aligned_value_from_current_guest(vcpu, gva_scode_info);
	gva_scode_info_offset += 4;
	dprintf(LOG_TRACE, "[TV] scode_info addr %x, # of section is %d\n", gva_scode_info, ps_scode_info->num_sections);

	/* copy array of parameter descriptors */
	if( ps_scode_info->num_sections > TV_MAX_SECTIONS )  {
		dprintf(LOG_ERROR, "[TV] number of scode sections exceeds limit!\n");
		return 1;
	}
	copy_from_current_guest(vcpu,
													(u8*)&(ps_scode_info->sections[0]),
													gva_scode_info+gva_scode_info_offset,
													ps_scode_info->num_sections*sizeof(ps_scode_info->sections[0]));
	return 0;
}

/* parse scode sections info (scode registration input) */
int memsect_info_register(VCPU * vcpu, struct tv_pal_sections *ps_scode_info, whitelist_entry_t * wle)
{
	size_t i;
	int pnum, is_get_param, is_get_stack;
	int type, size;
	unsigned int start;

	/* parse section type, start address and size */
	pnum = 0;
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
						if (guest_pt_check_user_rw(vcpu, start, size)) {
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
						if (guest_pt_check_user_rw(vcpu, start, size)) {
							dprintf(LOG_ERROR, "[TV] ERROR: SCODE_STACK pages are not user writable!\n");
							return 1;
						}
					}
				}
				break;
			default :
				break;
		}
		pnum += size;
		dprintf(LOG_TRACE, "[TV] section %d type %d addr %#x size %d\n",i+1, type, start, size);
	}

	if (pnum > MAX_REGPAGES_NUM) {
		dprintf(LOG_ERROR, "[TV] number of scode pages exceeds limit!\n");
		return 1;
	}

	return 0;
}


/* register scode in whitelist */
u32 scode_register(VCPU *vcpu, u32 scode_info, u32 scode_pm, u32 gventry) 
{

  size_t i;
	whitelist_entry_t whitelist_new;
	struct tv_pal_section * ginfo; 
	u64 gcr3;

	gcr3 = VCPU_gcr3(vcpu);

	dprintf(LOG_TRACE, "\n[TV] ************************************\n");
	dprintf(LOG_TRACE, "[TV] ********** scode register **********\n");
	dprintf(LOG_TRACE, "[TV] ************************************\n");

	if (whitelist_size == whitelist_max)
	{
		dprintf(LOG_ERROR, "[TV] FATAL ERROR: too many registered scode, the limitation is %d\n", whitelist_max);
		return 1;
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
		return 1;
	}
	whitelist_new.gpm_num = whitelist_new.params_info.num_params;
	/* register scode sections into whitelist entry */
	if (memsect_info_copy_from_guest(vcpu, &(whitelist_new.scode_info), scode_info)
			|| memsect_info_register(vcpu, &(whitelist_new.scode_info), &whitelist_new)) {
		dprintf(LOG_ERROR, "[TV] Registration Failed. Scode section info incorrect! \n");
		return 1;
	}

	/********************************/
	{
		hpt_pmo_t reg_npmo_root, reg_gpmo_root, pal_npmo_root, pal_gpmo_root;

		hpt_type_t guest_t = (VCPU_gcr4(vcpu) & CR4_PAE) ? HPT_TYPE_PAE : HPT_TYPE_NORM;

		whitelist_new.npl = malloc(sizeof(pagelist_t));
		pagelist_init(whitelist_new.npl);

		whitelist_new.gpl = malloc(sizeof(pagelist_t));
		pagelist_init(whitelist_new.gpl);

		reg_npmo_root = (hpt_pmo_t) {
			.t = hpt_nested_walk_ctx.t,
			.lvl = hpt_root_lvl(hpt_nested_walk_ctx.t),
			.pm = VCPU_get_current_root_pm(vcpu),
		};
		reg_gpmo_root = (hpt_pmo_t) {
			.t = guest_t,
			.lvl = hpt_root_lvl(guest_t),
			.pm = gpa2hva(hpt_cr3_get_address(guest_t, VCPU_gcr3(vcpu))),
		};
		dprintf(LOG_TRACE, "is-pae:%d, gcr3:%016llx, pae_get_addr:%08x npae_get_addr:%08x pm:%p\n",
						(guest_t == HPT_TYPE_PAE),
						VCPU_gcr3(vcpu),
						(u32)pae_get_addr_from_32bit_cr3(VCPU_gcr3(vcpu)),
						(u32)npae_get_addr_from_32bit_cr3(VCPU_gcr3(vcpu)),
						reg_gpmo_root.pm);
		{
			size_t i;
			dprintf(LOG_TRACE, "page map dump:\n");
			for(i=0; i < (4096/4); i++) {
				dprintf(LOG_TRACE, "%4u: 0x%08x\n", i, ((u32*)reg_gpmo_root.pm)[i]);
			}
		}
		pal_npmo_root = (hpt_pmo_t) {
			.t = reg_npmo_root.t,
			.lvl = reg_npmo_root.lvl,
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

		whitelist_new.hpt_guest_walk_ctx = hpt_nested_walk_ctx;
		whitelist_new.hpt_guest_walk_ctx.gzp_ctx = whitelist_new.gpl;
		whitelist_new.hpt_guest_walk_ctx.t = reg_gpmo_root.t;

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
			hpt_err = hpt_walk_insert_pmeo_alloc(&whitelist_new.hpt_nested_walk_ctx,
																					 &pal_npmo_root,
																					 &pmeo,
																					 hva2gpa(page));
			ASSERT(!hpt_err);
		}

		dprintf(LOG_TRACE, "adding sections to pal's npts and gpts:\n");
		/* map each requested section into the pal */
		for (i=0; i<whitelist_new.scode_info.num_sections; i++) {
			section_t section = {
				.reg_gva = whitelist_new.scode_info.sections[i].start_addr,
				.pal_gva = whitelist_new.scode_info.sections[i].start_addr,
				.size = whitelist_new.scode_info.sections[i].page_num * PAGE_SIZE_4K,
				.prot = pal_prot_of_type(whitelist_new.scode_info.sections[i].type),
			};
			scode_lend_section(&reg_npmo_root, &whitelist_new.hpt_nested_walk_ctx,
												 &reg_gpmo_root, &whitelist_new.hpt_guest_walk_ctx,
												 &pal_npmo_root, &whitelist_new.hpt_nested_walk_ctx,
												 &pal_gpmo_root, &whitelist_new.hpt_guest_walk_ctx,
												 &section);
		}

		/* clone gdt */
		dprintf(LOG_TRACE, "cloning gdt:\n");
		scode_clone_gdt(VCPU_gdtr_base(vcpu), VCPU_gdtr_limit(vcpu),
										&reg_gpmo_root, &whitelist_new.hpt_guest_walk_ctx,
										&pal_gpmo_root, &whitelist_new.hpt_guest_walk_ctx,
										whitelist_new.gpl);

		whitelist_new.pal_npt_root = pal_npmo_root;
		whitelist_new.pal_gpt_root = pal_gpmo_root;
		whitelist_new.reg_gpt_root = reg_gpmo_root;
		whitelist_new.pal_gcr3 = hpt_cr3_set_address(whitelist_new.pal_gpt_root.t,
																								 VCPU_gcr3(vcpu), /* XXX should build trusted cr3 from scratch */
																								 hva2gpa(whitelist_new.pal_gpt_root.pm));
		/* XXX flush TLB to ensure 'reg' is now correctly denied access */
	}
	/********************************/

	/* register pages in each scode section */
	whitelist_new.scode_pages = (pte_t*)malloc(MAX_REGPAGES_NUM*sizeof(whitelist_new.scode_pages[0]));
	whitelist_new.scode_size = 0;
	for( i=0 ; i < (u32)(whitelist_new.scode_info.num_sections) ; i++ )  {
		ginfo = &(whitelist_new.scode_info.sections[i]);
		if (guest_pt_copy(vcpu, &(whitelist_new.scode_pages[whitelist_new.scode_size]), ginfo->start_addr, (ginfo->page_num)<<PAGE_SHIFT_4K, ginfo->type)) {
			free(whitelist_new.scode_pages);
			dprintf(LOG_ERROR, "[TV] SECURITY: Registration Failed. Probably some page of sensitive code is not in memory yet\n");
			return 1;
		}
		whitelist_new.scode_size += ginfo->page_num;
	}
	whitelist_new.scode_size = (whitelist_new.scode_size) << PAGE_SHIFT_4K;

	/* set up scode pages permission (also flush TLB) */
	/* CRITICAL SECTION in MP scenario: need to quiesce other CPUs or at least acquire spinlock */
	if (hpt_scode_set_prot(vcpu, whitelist_new.scode_pages, whitelist_new.scode_size))
	{
		free(whitelist_new.scode_pages);
		dprintf(LOG_ERROR, "[TV] SECURITY: Registration Failed. Probably some page has already been used by other sensitive code.\n");
		return 1;
	}

	/* register guest page table pages. TODO: cloneguest page table
		 instead of checking on every switch to ensure it hasn't been
		 tampered. */
	scode_expose_arch(vcpu, &whitelist_new);
	hpt_insert_pal_pmes(vcpu, &whitelist_new.hpt_nested_walk_ctx,
											whitelist_new.pal_npt_root.pm,
											whitelist_new.pal_npt_root.lvl,
											whitelist_new.pte_page,
											whitelist_new.pte_size>>PAGE_SHIFT_4K);
	scode_unexpose_arch(vcpu, &whitelist_new);

	/* initialize Micro-TPM instance */
	utpm_init_instance(&whitelist_new.utpm);

	/* hash the entire SSCB code, and then extend the hash value into uTPM PCR[0] */
	if (scode_measure(&whitelist_new.utpm, whitelist_new.scode_pages, whitelist_new.scode_size))
	{
		hpt_scode_clear_prot(vcpu, whitelist_new.scode_pages, whitelist_new.scode_size);
		free(whitelist_new.scode_pages);
		dprintf(LOG_ERROR, "[TV] SECURITY: Registration Failed. sensitived code cannot be verified.\n");
		return 1;
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
		return 1;
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


	return 0; 
}

/* unregister scode in whitelist */
u32 scode_unregister(VCPU * vcpu, u32 gvaddr) 
{
	size_t i;

	u64 gcr3;

	gcr3 = VCPU_gcr3(vcpu);

	dprintf(LOG_TRACE, "\n[TV] ************************************\n");
	dprintf(LOG_TRACE, "[TV] ********* scode unregister *********\n");
	dprintf(LOG_TRACE, "[TV] ************************************\n");

	if (whitelist_size == 0)
	{
		dprintf(LOG_ERROR, "[TV] FATAL ERROR: no scode registered currently\n");
		return 1;
	}

	dprintf(LOG_TRACE, "[TV] CPU(%02x): remove from whitelist gcr3 %#llx, gvaddr %#x\n", vcpu->id, gcr3, gvaddr);

	for (i = 0; i < whitelist_max; i ++)
	{
		/* find scode with correct cr3 and entry point */
		if ((whitelist[i].gcr3 == gcr3) && (whitelist[i].entry_v == gvaddr))
			break;
	}

	if (i >= whitelist_max) 
	{
		dprintf(LOG_ERROR, "[TV] SECURITY: UnRegistration Failed. no matching sensitive code found\n");
		return 1;
	}

	/* dump perf counters */
	dprintf(LOG_PROFILE, "performance counters:\n");
	{
		int j;
		for(j=0; j<TV_PERF_CTRS_COUNT; j++) {
			dprintf(LOG_PROFILE, "  %s total: %Lu count: %Lu\n",
							g_tv_perf_ctr_strings[j],
							perf_ctr_get_total_time(&g_tv_perf_ctrs[j]),
							perf_ctr_get_count(&g_tv_perf_ctrs[j]));
		}
	}
	dprintf(LOG_PROFILE, "total mem mallocd: %u\n", heapmem_get_used_size());

	/* if we find one to remove, we also need to clear the physcial page number
	 * vector 
	 */
	/* CRITICAL SECTION in MP scenario: need to quiesce other CPUs or at least acquire spinlock */
	if (whitelist[i].scode_pages)
	{
		hpt_scode_clear_prot(vcpu, whitelist[i].scode_pages, whitelist[i].scode_size);
		free((void *)(whitelist[i].scode_pages));
		whitelist[i].scode_pages = NULL;
	}

	/* delete entry from scode whitelist */
	/* CRITICAL SECTION in MP scenario: need to quiesce other CPUs or at least acquire spinlock */
	whitelist_size --;
	whitelist[i].gcr3 = 0;

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

#define EXPOSE_PAGE(x) expose_page(pte_page,x, &pte_count)
/* expose one page, helper function used by scode_expose_arch() */
void expose_page (pte_t *page_list, pte_t page, u32 * count)
{
	dprintf(LOG_TRACE, "[TV] expose page %#Lx \n", page);
	if (page != 0xFFFFFFFF) {
		page = SCODE_PTE_TYPE_SET(page, TV_PAL_SECTION_GUEST_PAGE_TABLES);
		if (!test_page_in_list(page_list, page, *count)) {
			page_list[(*count)]=page;
			*count = (*count)+1;
			/* set up DEV vector to prevent DMA attack */
			/* XXX FIXME: temporarily disable */
			//set_page_dev_prot(pfn);
			dprintf(LOG_TRACE, "[TV]   expose page %#Lx \n", page);
		}
	}
}

/* find all PTE entry pages that is related to access scode and GDT */
static void scode_expose_arch(VCPU *vcpu, whitelist_entry_t *wle)
{
	size_t i;
	size_t j;
	pte_t *pte_page;
	u32 pte_count = 0;
	u32 gpaddr = 0;
	u32 is_pae;
	u32 gdtr;
	struct tv_pal_section * ginfo;
	pte_t tmp_page[3];
	u32 tmp_count=0;
	pte_t *sp = wle->scode_pages;
	u32 gcr3_flag=0;

	perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_EXPOSE_ARCH], vcpu->idx);

	is_pae = VCPU_gcr4(vcpu) & CR4_PAE;
	gdtr = VCPU_gdtr_base(vcpu);

	/* alloc memory for page table entry holder */
	wle->pte_page = malloc(MAX_REGPAGES_NUM*sizeof(pte_t));
	pte_page = wle->pte_page;

	/* get related page tables for scode */
	/* Here we walk guest page table, and find out all the pdp,pd,pt entry
	   that is necessary to translate gvaddr */
	dprintf(LOG_TRACE, "[TV] expose SCODE related PTE pages\n");
	for( i=0 ; i < wle->scode_info.num_sections ; i++ )  {
		ginfo = &(wle->scode_info.sections[i]);
		for( j=0 ; j< ginfo->page_num; j++ )  {
			gpaddr = gpt_get_ptpages(vcpu, ginfo->start_addr+(j<<PAGE_SHIFT_4K), &tmp_page[0], &tmp_page[1], &tmp_page[2]);

			/* check gvaddr to gpaddr mapping */
			if( gpaddr != (sp[tmp_count+j] & ~0x7)) {
				dprintf(LOG_ERROR, "[TV] SECURITY: scode vaddr %x -> paddr %#Lx mapping changed! invalide gpaddr is %x!\n", ginfo->start_addr+(j<<PAGE_SHIFT_4K), sp[tmp_count+j], gpaddr);
				free(wle->pte_page);
				HALT();
			}

			/* write pdp, pd, pt entry into pte_page */
			if (is_pae) {
				/* PAE mode */
				if (gcr3_flag == 0) {
					gcr3_flag = 1;
					EXPOSE_PAGE(tmp_page[0]);
				}

				EXPOSE_PAGE(tmp_page[1]); 
				EXPOSE_PAGE(tmp_page[2]);
			} else {
				/* NPAE mode */
				/* PD table has 1024 entries, which is two page */
				if (gcr3_flag == 0) {
					gcr3_flag = 1;
					EXPOSE_PAGE(tmp_page[0]);
					EXPOSE_PAGE(tmp_page[0]+(1<<PAGE_SHIFT_4K));
				}
				EXPOSE_PAGE(tmp_page[1]);
				EXPOSE_PAGE(tmp_page[1]+(1<<PAGE_SHIFT_4K));
			}
		}
		tmp_count += (ginfo->page_num);
	}

	/* get related page tables for gdt */
	/* Here we walk guest page table, and find out all the pages
	   that is necessary to translate gdtr.base */
	/* GDP table can be fit into one page and already be noted down in the
	   page table walking for scode, no need to do it again, 
	   that is why we put NULL below, and take gpaddr instead(protect the page contains GDT table */ 
	dprintf(LOG_TRACE, "[TV] expose GDT related PTE pages\n");
	gpaddr = gpt_get_ptpages(vcpu, gdtr, NULL, &tmp_page[1], &tmp_page[2]);

	EXPOSE_PAGE(gpaddr);
	EXPOSE_PAGE(tmp_page[1]);
	EXPOSE_PAGE(tmp_page[2]);

	wle->pte_size = pte_count << PAGE_SHIFT_4K;

	perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_EXPOSE_ARCH], vcpu->idx);
}

void memcpy_guest_to_guest(VCPU * vcpu, u32 src, u32 dst, u32 len)
{
	u32 src_gpaddr, dst_gpaddr;
	u8 *src_hvaddr, *dst_hvaddr;
	//u32 i;
	u32 is_pae;

	is_pae = VCPU_gcr4(vcpu) & CR4_PAE;

	src_gpaddr = gpt_vaddr_to_paddr_current(vcpu, src);
  	dst_gpaddr = gpt_vaddr_to_paddr_current(vcpu, dst);

//	/* make sure the entire string are in same page */
//	if (is_pae) {
//		ASSERT (SAME_PAGE_PAE(src_gpaddr, src_gpaddr+len));
//		ASSERT (SAME_PAGE_PAE(dst_gpaddr, dst_gpaddr+len));
//	} else {
//		ASSERT (SAME_PAGE_NPAE(src_gpaddr, src_gpaddr+len));
//		ASSERT (SAME_PAGE_NPAE(dst_gpaddr, dst_gpaddr+len));
//	}
	src_hvaddr = (u8 *)(gpa2hva(src_gpaddr));
	dst_hvaddr = (u8 *)(gpa2hva(dst_gpaddr));
	//printf("[TV]   PM string value is:");
	//for( i=0 ; i<len ; i++ )  {
	//	printf("%x ", *(src_hvaddr+i));
	//}
	//printf("!\n");
	memcpy(dst_hvaddr, src_hvaddr, len);
}

u32 scode_marshall(VCPU * vcpu)
{
	u32 pm_addr, pm_addr_base, pm_value, pm_tmp;  /*parameter stack base address*/
	u32 pm_num, pm_type, pm_size, pm_size_sum; /*save pm information*/
	u32 grsp;
	u32 new_rsp;
	int curr=scode_curr[vcpu->id];

	perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_MARSHALL], vcpu->idx);

	dprintf(LOG_TRACE, "[TV] marshalling scode parameters!\n");
	if(whitelist[curr].gpm_num == 0)
	{
		dprintf(LOG_TRACE, "[TV] params number is 0. Return!\n");
		perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_MARSHALL], vcpu->idx);
		return 0;
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

	if (whitelist[curr].gpm_num > TV_MAX_PARAMS)
	{
		dprintf(LOG_ERROR, "[TV] Fail: param num is too big!\n");
		perf_ctr_timer_discard(&g_tv_perf_ctrs[TV_PERF_CTR_MARSHALL], vcpu->idx);
		return 1;
	}

	/* begin to process the params*/
	for (pm_num = whitelist[curr].gpm_num; pm_num > 0; pm_num--) /*the last parameter should be pushed in stack first*/
	{
		/* get param information*/
		pm_type = whitelist[curr].params_info.params[pm_num-1].type;
		pm_size = whitelist[curr].params_info.params[pm_num-1].size;
		/* get param value from guest stack */
		pm_value = get_32bit_aligned_value_from_guest(&whitelist[curr].hpt_guest_walk_ctx,
																									&whitelist[curr].reg_gpt_root,
																									grsp+(pm_num-1)*4);
		pm_size_sum += 12;

		if (pm_size_sum > (whitelist[curr].gpm_size*PAGE_SIZE_4K))
		{
			dprintf(LOG_ERROR, "[TV] Fail: No enough space to save input params data!\n");
			perf_ctr_timer_discard(&g_tv_perf_ctrs[TV_PERF_CTR_MARSHALL], vcpu->idx);
			return 1;
		}

		/* save input params in input params memory for sensitive code */
		put_32bit_aligned_value_to_guest(&whitelist[curr].hpt_guest_walk_ctx,
																		 &whitelist[curr].pal_gpt_root,
																		 (u32)pm_addr, pm_type);
		put_32bit_aligned_value_to_guest(&whitelist[curr].hpt_guest_walk_ctx,
																		 &whitelist[curr].pal_gpt_root,
																		 (u32)pm_addr+4, pm_size);
		put_32bit_aligned_value_to_guest(&whitelist[curr].hpt_guest_walk_ctx,
																		 &whitelist[curr].pal_gpt_root,
																		 (u32)pm_addr+8, pm_value);
		pm_addr += 12;
		switch (pm_type)
		{
			case TV_PAL_PM_INTEGER: /* integer */
				{        
					/* put the parameter value in sensitive code stack */
					pm_tmp = pm_value;
					dprintf(LOG_TRACE, "[TV]   PM %d is a integer (size %d, value %#x)\n", pm_num, pm_size, pm_value);
					break;
				}
			case TV_PAL_PM_POINTER: /* pointer */
				{
					/*copy data from guest space to sensitive code*/
					pm_size_sum += 4*pm_size;
					if (pm_size_sum > (whitelist[curr].gpm_size*PAGE_SIZE_4K))
					{
						dprintf(LOG_TRACE, "[TV] Fail: No enough space to save input params data!\n");
						return 1;
					}

					/* make sure that this pointer point to mem regeion that can be r/w by user */
					if (guest_pt_check_user_rw(vcpu, pm_value, (pm_value+pm_size*4-(pm_value & (~0xFFF)))/4096+1)) {
						dprintf(LOG_ERROR, "[TV] Fail: input param data region is not user writable!\n");
						return 1;
					}

					hpt_copy_guest_to_guest(&whitelist[curr].hpt_guest_walk_ctx,
																	&whitelist[curr].pal_gpt_root,
																	pm_addr,
																	&whitelist[curr].hpt_guest_walk_ctx,
																	&whitelist[curr].reg_gpt_root,
																	pm_value,
																	pm_size*4);

					/* put pointer address in sensitive code stack*/
					pm_tmp = pm_addr;
					dprintf(LOG_TRACE, "[TV]   PM %d is a pointer (size %d, addr %#x)\n", pm_num, pm_size*4, pm_value);
					pm_addr += 4*pm_size;
					break;
				}
			default: /* other */
				perf_ctr_timer_discard(&g_tv_perf_ctrs[TV_PERF_CTR_MARSHALL], vcpu->idx);
				dprintf(LOG_ERROR, "[TV] Fail: unknown parameter %d type %d \n", pm_num, pm_type);
				return 1;
		}
		new_rsp = VCPU_grsp(vcpu)-4;
		VCPU_grsp_set(vcpu, new_rsp);
		put_32bit_aligned_value_to_guest(&whitelist[curr].hpt_guest_walk_ctx,
																		 &whitelist[curr].pal_gpt_root,
																		 new_rsp, pm_tmp);
	}
	perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_MARSHALL], vcpu->idx);
	return 0;
}



//todo: switch from regular code to sensitive code
u32 hpt_scode_switch_scode(VCPU * vcpu)
{
	u32 addr;
	int curr=scode_curr[vcpu->id];

	perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_SWITCH_SCODE], vcpu->idx);

	dprintf(LOG_TRACE, "\n[TV] ************************************\n");
	dprintf(LOG_TRACE, "[TV] ********* switch to scode **********\n");
	dprintf(LOG_TRACE, "[TV] ************************************\n");

	/* save the guest stack pointer and set new stack pointer to scode stack */
	dprintf(LOG_TRACE, "[TV] saved guest regular stack %#x, switch to sensitive code stack %#x\n", (u32)VCPU_grsp(vcpu), whitelist[curr].gssp);
	whitelist[curr].grsp = (u32)VCPU_grsp(vcpu);
	VCPU_grsp_set(vcpu, whitelist[curr].gssp);

	/* input parameter marshalling */
	if (scode_marshall(vcpu)){
		/* error in parameter marshalling */
		/* restore regular code stack */
		VCPU_grsp_set(vcpu, whitelist[curr].grsp);
		whitelist[curr].grsp = (u32)-1; 
		return 1;
	}

	/* find all PTE pages related to access scode and GDT */
	scode_expose_arch(vcpu, &whitelist[curr]);
	/* change NPT permission for all PTE pages and scode pages */
	dprintf(LOG_TRACE, "[TV] change NPT permission to run PAL!\n");
	VCPU_set_current_root_pm(vcpu, whitelist[curr].pal_npt_root.pm);
	emhf_hwpgtbl_flushall(vcpu); /* XXX */

	/* hpt_nested_switch_scode(vcpu, whitelist[curr].scode_pages, whitelist[curr].scode_size, */
	/* 												whitelist[curr].pte_page, whitelist[curr].pte_size); */
		
	/* disable interrupts */
	VCPU_grflags_set(vcpu, VCPU_grflags(vcpu) & ~EFLAGS_IF);

	/* XXX FIXME- what's the right thing here? Keeping 'legacy' behavior
		 of setting this flag for AMD only and doing nothing for INTEL for
		 now */
	if(vcpu->cpu_vendor == CPU_VENDOR_AMD) {
		/* set the sensitive code to run in ring 3 */
		((struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr))->cpl = 3;
	}

	/* write the return address to scode stack */
	addr = get_32bit_aligned_value_from_guest(&whitelist[curr].hpt_guest_walk_ctx,
																						&whitelist[curr].reg_gpt_root,
																						(u32)whitelist[curr].grsp);
	VCPU_grsp_set(vcpu, VCPU_grsp(vcpu)-4);
	put_32bit_aligned_value_to_guest(&whitelist[curr].hpt_guest_walk_ctx,
																	 &whitelist[curr].pal_gpt_root,
																	 (u32)VCPU_grsp(vcpu), addr);
	/* store the return address in whitelist structure */
	whitelist[curr].return_v = addr;
	dprintf(LOG_TRACE, "[TV] scode return vaddr is %#x\n", whitelist[curr].return_v);

	/* we add the page containing the return address to the
		 guest page tables, but not the nested page tables. failure to
		 add to the guest page tables will cause a triple fault in the
		 guest. */
	{
		hpt_pmeo_t pmeo = {
			.pme = 0,
			.t = whitelist[curr].pal_gpt_root.t,
			.lvl = 1,
		};
		hpt_pmeo_t orig;
		int hpt_err;
		hpt_walk_get_pmeo(&orig,
											&whitelist[curr].hpt_guest_walk_ctx,
											&whitelist[curr].reg_gpt_root,
											1,
											addr);
		hpt_pmeo_setprot(&pmeo, HPT_PROTS_RX);
		hpt_pmeo_setuser(&pmeo, true);
		/* the gpa address here shouldn't matter, so long as it's one not
			 accessible by the pal.  we'll copy the original for now to be
			 cautious */
		hpt_pmeo_set_address(&pmeo, hpt_pmeo_get_address(&orig));

		dprintf(LOG_TRACE, "[TV] original pme for return gva address %x: lvl:%d %llx\n",
						addr, orig.lvl, orig.pme);
		dprintf(LOG_TRACE, "[TV] generated pme for return gva address %x: lvl:%d %llx\n",
						addr, pmeo.lvl, pmeo.pme);
		hpt_err = hpt_walk_insert_pmeo_alloc(&whitelist[curr].hpt_guest_walk_ctx,
																				 &whitelist[curr].pal_gpt_root,
																				 &pmeo,
																				 addr);
		ASSERT(!hpt_err);
	}

	dprintf(LOG_TRACE, "[TV] host stack pointer before running scode is %#x\n",(u32)VCPU_grsp(vcpu));

	perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_SWITCH_SCODE], vcpu->idx);
	return 0;
}

static void scode_unexpose_arch(VCPU __attribute__((unused)) *vcpu, whitelist_entry_t *wle)
{
	size_t i;
	pte_t * page = wle->pte_page;
	dprintf(LOG_TRACE, "[TV] unexpose SCODE and GDT related to PTE pages\n");
	/* clear page bitmap set in scode_expose_arch() */
	for (i=0; i<((wle->pte_size)>>PAGE_SHIFT_4K);i++) {
		clear_page_scode_bitmap(((page[i])>>PAGE_SHIFT_4K));
		/* XXX FIXME: temporarily disable */
	//	clear_page_dev_prot(((page[i])>>PAGE_SHIFT_4K));
	}

	/* free pte_page to save heap space,
	 * next expose will alloc a new pte_page */
	free(wle->pte_page);
	wle->pte_page = 0;
	wle->pte_size = 0;
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
	for (i = 1; i <= pm_num; i++) /*the last parameter should be pushed in stack first*/
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
					hpt_copy_guest_to_guest(&whitelist[curr].hpt_guest_walk_ctx,
																	&whitelist[curr].reg_gpt_root,
																	pm_value,
																	&whitelist[curr].hpt_guest_walk_ctx,
																	&whitelist[curr].reg_gpt_root,
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
	if (!scode_unmarshall(vcpu)){
		/* clear the NPT permission setting in switching into scode */
		dprintf(LOG_TRACE, "[TV] change NPT permission to exit PAL!\n"); 
		VCPU_set_current_root_pm(vcpu, VCPU_get_default_root_pm(vcpu));
		emhf_hwpgtbl_flushall(vcpu); /* XXX */
		/* hpt_nested_switch_regular(vcpu, whitelist[curr].scode_pages, whitelist[curr].scode_size, */
		/* 													whitelist[curr].pte_page, whitelist[curr].pte_size); */
		scode_unexpose_arch(vcpu, &whitelist[curr]);

		/* release shared pages */
		scode_release_all_shared_pages(vcpu, &whitelist[curr]);

		/* switch back to regular stack */
		dprintf(LOG_TRACE, "[TV] switch from scode stack %#x back to regular stack %#x\n", (u32)VCPU_grsp(vcpu), (u32)whitelist[curr].grsp);
		VCPU_grsp_set(vcpu, whitelist[curr].grsp + 4);
		whitelist[curr].grsp = (u32)-1;

		/* enable interrupts */
		VCPU_grflags_set(vcpu, VCPU_grflags(vcpu) | EFLAGS_IF);

		dprintf(LOG_TRACE, "[TV] stack pointer before exiting scode is %#x\n",(u32)VCPU_grsp(vcpu));

		perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_SWITCH_REGULAR], vcpu->idx);

		return 0;
	}
	/* error in scode unmarshalling */
	return 1;
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

		if (whitelist[*curr].return_v != rip) {
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

void scode_release_all_shared_pages(VCPU *vcpu, whitelist_entry_t* entry)
{
	size_t i;
	u32 shared_page_count=0;
	const u32 scode_pages = entry->scode_size>>PAGE_SHIFT_4K;
	u32 scode_pages_shared_start;

	/* remove from section info, and count the number of shared pages */
	for(i=(entry->scode_info.num_sections-1);
			entry->scode_info.sections[i].type == TV_PAL_SECTION_SHARED;
			i--) {
		entry->scode_info.num_sections--;
		shared_page_count += entry->scode_info.sections[i].page_num;
	}
	dprintf(LOG_TRACE, "scode_release_all_shared_pages: releasing %d shared pages\n",
				 shared_page_count);
	if(shared_page_count == 0) {
		return;
	}

	ASSERT(scode_pages >= shared_page_count);
	scode_pages_shared_start = scode_pages - shared_page_count;

	/* exactly last shared_page_count pages of entry->scode_pages should be shared.
		 check this assumption for debugging. */
	ASSERT(scode_pages_shared_start == 0
				 || (SCODE_PTE_TYPE_GET(entry->scode_pages[scode_pages_shared_start-1])
						 != TV_PAL_SECTION_SHARED));
	for(i=scode_pages_shared_start; i<scode_pages; i++) {
		ASSERT(SCODE_PTE_TYPE_GET(entry->scode_pages[i]) == TV_PAL_SECTION_SHARED);
	}

	/* clear protections */
	hpt_scode_clear_prot(vcpu,
											 &entry->scode_pages[scode_pages_shared_start],
											 shared_page_count<<PAGE_SHIFT_4K);

	/* remove from pal's page tables */
	hpt_walk_set_prots(&entry->hpt_nested_walk_ctx,
										 entry->pal_npt_root.pm,
										 hpt_root_lvl(entry->hpt_nested_walk_ctx.t),
										 &entry->scode_pages[scode_pages_shared_start],
										 shared_page_count,
										 HPT_PROTS_NONE);

	/* XXX Should also revoke access to corresponding guest page table
	 * pages. Not doing it for now since won't normally hurt anything,
	 * and likely to rewrite handling of guest page tables soon.
	 */

	/* remove from pte's */
	entry->scode_size -= shared_page_count<<PAGE_SHIFT_4K;
}

u32 scode_share_range(VCPU * vcpu, whitelist_entry_t *entry, u32 gva_base, u32 gva_len)
{
	u32 gva_len_pages;

	pte_t *new_scode_pages=NULL;
	
	/* for backout\error handling */
	u32 section_num_added=0, scode_size_added=0;
	bool did_set_prot=false;
	u32 rv=0;

	/* XXX locking? */

	dprintf(LOG_TRACE, "[TV] scode_share: gva-base %08x, size %x\n", gva_base, gva_len);

	if (!PAGE_ALIGNED_4K(gva_base) || !PAGE_ALIGNED_4K(gva_len)) {
		dprintf(LOG_ERROR, "[TV] scode_share: addr %x or len %d not page aligned\n",
					 gva_base, gva_len);
		rv=1;
		goto outerr;
	}
	gva_len_pages = gva_len >> PAGE_SHIFT_4K;

	/* add the section entry info */
	if (entry->scode_info.num_sections >= TV_MAX_SECTIONS) {
		dprintf(LOG_ERROR, "[TV] scode_share: maximum number of sections %d exceeded\n", TV_MAX_SECTIONS);
		rv=2;
		goto outerr;
	}
	entry->scode_info.sections[entry->scode_info.num_sections] =
		(struct tv_pal_section)
		{
			.type = TV_PAL_SECTION_SHARED,
			.start_addr = gva_base,
			.page_num = gva_len_pages,
		};
	entry->scode_info.num_sections++;
	section_num_added++;

	/* create pt entries */
	{
		u32 scode_num_pages = entry->scode_size >> PAGE_SHIFT_4K;
		new_scode_pages = &entry->scode_pages[scode_num_pages];
		if ((scode_num_pages+gva_len_pages) > MAX_REGPAGES_NUM) {
			dprintf(LOG_ERROR, "[TV] scode_share registered-page-limit exceeded:"
						 " reg'd:%d addtl:%d limit:%d\n",
						 scode_num_pages, gva_len_pages, MAX_REGPAGES_NUM);
		}
		if (guest_pt_copy(vcpu,
											new_scode_pages,
											gva_base,
											gva_len,
											TV_PAL_SECTION_SHARED)) {
			dprintf(LOG_ERROR, "[TV] scode_share registration Failed. Probably some pages not in memory yet\n");
			rv=3;
			goto outerr;
		}
		entry->scode_size += gva_len;
		scode_size_added += gva_len;
	}

	/* set up protection of newly registered pt entries */
	if(hpt_scode_set_prot(vcpu, new_scode_pages, gva_len)) {
		dprintf(LOG_ERROR, "[TV] SECURITY: Registration Failed. Probably some page has already been used by other sensitive code.\n");
		rv=4;
		goto outerr;
	}
	did_set_prot=true;

	/* add to pal's page tables */
	{
		hpt_insert_pal_pmes(vcpu, &entry->hpt_nested_walk_ctx,
												entry->pal_npt_root.pm,
												hpt_root_lvl(entry->hpt_nested_walk_ctx.t),
												new_scode_pages,
												gva_len_pages);
		scode_expose_arch(vcpu, entry);
		hpt_insert_pal_pmes(vcpu, &entry->hpt_nested_walk_ctx,
												entry->pal_npt_root.pm,
												hpt_root_lvl(entry->hpt_nested_walk_ctx.t),
												entry->pte_page,
												entry->pte_size>>PAGE_SHIFT_4K);
		scode_unexpose_arch(vcpu, entry);
	}

  return rv;

 outerr:
	if (entry!=NULL) {
		entry->scode_size -= scode_size_added;
		entry->scode_info.num_sections -= section_num_added;
	}
	if (did_set_prot) {
		hpt_scode_clear_prot(vcpu, new_scode_pages, gva_len_pages);
	}
	return rv;
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

	return 0;
}


/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */
