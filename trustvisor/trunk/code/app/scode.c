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

#include  <target.h>
#include  <globals.h>
#include  "./include/scode.h"
#include  "./include/puttymem.h"
#include "./include/utpm.h"
#include "./include/sha1.h"
#include  "./include/rsa.h"
#include  "./include/random.h"
#include <perf.h>

static void scode_expose_arch(VCPU *vcpu, whitelist_entry_t *wle);
static void scode_unexpose_arch(VCPU *vcpu, whitelist_entry_t *wle);

hpt_walk_ctx_t hpt_nested_walk_ctx;

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
u32 * scode_whitelist;
whitelist_entry_t *whitelist=NULL;
u32 whitelist_size=0, whitelist_max=0;

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

/* keys for software TPM seal ,unseal and quote operations */
/* only initialized during bootstrap time, no need to apply a lock on it */
/* FIXME: put all of these keys into a struct so that all long-term
 * secrets are well-identified and therefore easy to wipe, etc. */
u8 aeskey[TPM_AES_KEY_LEN/8];
u8 hmackey[TPM_HMAC_KEY_LEN];
rsa_context g_rsa;

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
	u32 i, j;

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
	u32 i;

	for (i = 0; i < whitelist_max; i ++)
	{
		/* find scode with correct cr3 and entry point */
		if ((whitelist[i].gcr3 == gcr3) && (whitelist[i].entry_v == gv_entry))
			return &whitelist[i];
	}
	return NULL;
}

u32 scode_measure(utpm_master_state_t *utpm, pte_t *pte_pages, u32 size)
{
	u32 i; 
	u32 paddr;
	sha1_context ctx;
	TPM_DIGEST sha1sum;

	dprintf(LOG_TRACE, "[TV] measure scode and extend uTPM PCR value!\n");
	sha1_starts(&ctx);
	for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
	{
		/* only measure SCODE, STEXT, SDATA pages */
		paddr = PAGE_ALIGN_4K(pte_pages[i]);
		switch(SCODE_PTE_TYPE_GET(pte_pages[i])) {
		case TV_PAL_SECTION_CODE:
		case TV_PAL_SECTION_SHARED_CODE:
		case TV_PAL_SECTION_DATA:
			dprintf(LOG_TRACE, "[TV]   measure scode page %d paddr %#x\n", i+1, paddr);
			sha1_update(&ctx, (u8 *)paddr, PAGE_SIZE_4K);
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
	sha1_finish(&ctx, sha1sum.value);

	/* extend pcr 0 */
	utpm_extend(&sha1sum, utpm, 0);

	return 0;
}

hpt_pa_t hpt_nested_ptr2pa(void *ctx, void *ptr)
{
	return hva2spa(ptr);
}
void* hpt_nested_pa2ptr(void *ctx, hpt_pa_t ptr)
{
	return spa2hva(ptr);
}
void* hpt_nested_get_zeroed_page(void *ctx, size_t alignment, size_t sz)
{
	pagelist_t *pl = ctx;
	ASSERT(PAGE_SIZE_4K % alignment == 0);
	ASSERT(sz <= PAGE_SIZE_4K);
	return pagelist_get_zeroedpage(pl);
}

/* initialize all the scode related variables and buffers */
void init_scode(VCPU * vcpu)
{
	u32 inum, max;

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
		hpt_nested_walk_ctx.t = t;
		hpt_nested_walk_ctx.gzp = hpt_nested_get_zeroed_page;
		hpt_nested_walk_ctx.gzp_ctx = NULL; /* we'll copy this struct for
														each pal and give each it's own allocation
														pool */
		hpt_nested_walk_ctx.pa2ptr = hpt_nested_pa2ptr;
		hpt_nested_walk_ctx.ptr2pa = hpt_nested_ptr2pa;
		hpt_nested_walk_ctx.ptr2pa_ctx = NULL;
	}

	/* initialize heap memory */
	mem_init();

	scode_whitelist = (unsigned int *)vmalloc(WHITELIST_LIMIT);
	dprintf(LOG_TRACE, "[TV] alloc %dKB mem for scode_list at %x!\n", (WHITELIST_LIMIT/1024), (unsigned int)scode_whitelist);
	scode_pfn_bitmap = (unsigned char *)vmalloc(PFN_BITMAP_LIMIT);
	dprintf(LOG_TRACE, "[TV] alloc %dKB mem for pfn_bitmap at %x!\n", (PFN_BITMAP_LIMIT/1024), (unsigned int)scode_pfn_bitmap);
	scode_pfn_bitmap_2M = (unsigned short *)vmalloc(PFN_BITMAP_2M_LIMIT);
	dprintf(LOG_TRACE, "[TV] alloc %dKB mem for pfn_bitmap_2M at %x!\n", (PFN_BITMAP_LIMIT/1024), (unsigned int)scode_pfn_bitmap_2M);

	vmemset(scode_whitelist, 0, WHITELIST_LIMIT); 
	vmemset(scode_pfn_bitmap, 0, PFN_BITMAP_LIMIT);
	vmemset(scode_pfn_bitmap_2M, 0, PFN_BITMAP_2M_LIMIT);

	whitelist = (whitelist_entry_t *)scode_whitelist;
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
	scode_curr = (int *)vmalloc((max+1)<<2);
	vmemset(scode_curr, 0xFF, ((max+1)<<2));

	/* init pseudo random number generator */
	rand_init();
	dprintf(LOG_TRACE, "[TV] PRNG init!\n");

	/* aeskey and hmac are identical for different PAL, so that we can seal data from one PAL to another PAL */
	rand_bytes(aeskey, (TPM_AES_KEY_LEN>>3));
	dprintf(LOG_TRACE, "[TV] AES key generated!\n");
	rand_bytes(hmackey, 20);
	dprintf(LOG_TRACE, "[TV] HMAC key generated!\n");

	/* init RSA key required in uTPM Quote */
	rsa_init(&g_rsa, RSA_PKCS_V15, RSA_SHA1);
	rsa_gen_key(&g_rsa, (TPM_RSA_KEY_LEN<<3), 65537);
	dprintf(LOG_TRACE, "[TV] RSA key pair generated!\n");
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
	u32 i; 
	u32 pfn;
	int type =0; 
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
	u32 i; 
	u32 pfn;
#ifdef __MP_VERSION__
	u32 k;
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
	u32 i, num;
	u32 addr;
	addr = pm_addr;
	/* get parameter number */
	num = pm_info->num_params = get_32bit_aligned_value_from_guest(vcpu, addr);
	addr += 4;
	dprintf(LOG_TRACE, "[TV] pm_info %#x, # of paramters is %d\n", pm_addr, num);
	if (num > TV_MAX_PARAMS) {
		dprintf(LOG_ERROR, "[TV] number of scode sections exceeds limit!\n");
		return 1;
	}

	for (i = 0; i < num; i++)
	{
		pm_info->params[i].type = get_32bit_aligned_value_from_guest(vcpu, addr);
		pm_info->params[i].size = get_32bit_aligned_value_from_guest(vcpu, addr+4);
		dprintf(LOG_TRACE, "[TV] parameter %d type %d size %d\n", i+1, pm_info->params[i].type, pm_info->params[i].size);
		addr += 8;
	}
	return 0;
}

int memsect_info_copy_from_guest(VCPU * vcpu, struct tv_pal_sections *ps_scode_info, u32 gva_scode_info)
{
	u32 gva_scode_info_offset = 0;

	/* get parameter number */
	ps_scode_info->num_sections = get_32bit_aligned_value_from_guest(vcpu, gva_scode_info);
	gva_scode_info_offset += 4;
	dprintf(LOG_TRACE, "[TV] scode_info addr %x, # of section is %d\n", gva_scode_info, ps_scode_info->num_sections);

	/* copy array of parameter descriptors */
	if( ps_scode_info->num_sections > TV_MAX_SECTIONS )  {
		dprintf(LOG_ERROR, "[TV] number of scode sections exceeds limit!\n");
		return 1;
	}
	copy_from_guest(vcpu,
									(u8*)&(ps_scode_info->sections[0]),
									gva_scode_info+gva_scode_info_offset,
									ps_scode_info->num_sections*sizeof(ps_scode_info->sections[0]));
	return 0;
}

/* parse scode sections info (scode registration input) */
int memsect_info_register(VCPU * vcpu, struct tv_pal_sections *ps_scode_info, whitelist_entry_t * wle)
{
	unsigned int i;
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

	u32 i, j;
	whitelist_entry_t whitelist_new;
	u32 ret;
	u32 inum;
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
	whitelist_new.entry_p = gpt_vaddr_to_paddr(vcpu, gventry); 
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

	/* register pages in each scode section */
	whitelist_new.scode_pages = (pte_t*)vmalloc(MAX_REGPAGES_NUM*sizeof(whitelist_new.scode_pages[0]));
	whitelist_new.scode_size = 0;
	for( i=0 ; i < (u32)(whitelist_new.scode_info.num_sections) ; i++ )  {
		ginfo = &(whitelist_new.scode_info.sections[i]);
		if (guest_pt_copy(vcpu, &(whitelist_new.scode_pages[whitelist_new.scode_size]), ginfo->start_addr, (ginfo->page_num)<<PAGE_SHIFT_4K, ginfo->type)) {
			vfree(whitelist_new.scode_pages);
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
		vfree(whitelist_new.scode_pages);
		dprintf(LOG_ERROR, "[TV] SECURITY: Registration Failed. Probably some page has already been used by other sensitive code.\n");
		return 1;
	}

	/* initialize pal's hardware page tables */
	whitelist_new.hpt_nested_walk_ctx = hpt_nested_walk_ctx; /* copy from template */
	whitelist_new.pl = vmalloc(sizeof(pagelist_t));
	pagelist_init(whitelist_new.pl);
	whitelist_new.hpt_nested_walk_ctx.gzp_ctx = whitelist_new.pl; /* assign page allocator */
	whitelist_new.pal_hpt_root = pagelist_get_zeroedpage(whitelist_new.pl);

	hpt_insert_pal_pmes(vcpu, &whitelist_new.hpt_nested_walk_ctx,
											whitelist_new.pal_hpt_root,
											hpt_root_lvl(hpt_nested_walk_ctx.t),
											whitelist_new.scode_pages,
											whitelist_new.scode_size>>PAGE_SHIFT_4K);
	/* register guest page table pages. TODO: clone guest page table
		 instead of checking on every switch to ensure it hasn't been
		 tampered. */
	scode_expose_arch(vcpu, &whitelist_new);
	hpt_insert_pal_pmes(vcpu, &whitelist_new.hpt_nested_walk_ctx,
											whitelist_new.pal_hpt_root,
											hpt_root_lvl(hpt_nested_walk_ctx.t),
											whitelist_new.pte_page,
											whitelist_new.pte_size>>PAGE_SHIFT_4K);
	scode_unexpose_arch(vcpu, &whitelist_new);

	/* initialize Micro-TPM instance */
	utpm_init_internal(&whitelist_new.utpm);

	/* hash the entire SSCB code, and then extend the hash value into uTPM PCR[0] */
	if (scode_measure(&whitelist_new.utpm, whitelist_new.scode_pages, whitelist_new.scode_size))
	{
		hpt_scode_clear_prot(vcpu, whitelist_new.scode_pages, whitelist_new.scode_size);
		vfree(whitelist_new.scode_pages);
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
	vmemcpy(whitelist + i, &whitelist_new, sizeof(whitelist_entry_t));

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
	u32 i, j;

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
	dprintf(LOG_PROFILE, "total mem mallocd: %u\n", puttymem_get_used_size());

	/* if we find one to remove, we also need to clear the physcial page number
	 * vector 
	 */
	/* CRITICAL SECTION in MP scenario: need to quiesce other CPUs or at least acquire spinlock */
	if (whitelist[i].scode_pages)
	{
		hpt_scode_clear_prot(vcpu, whitelist[i].scode_pages, whitelist[i].scode_size);
		vfree((void *)(whitelist[i].scode_pages));
		whitelist[i].scode_pages = NULL;
	}

	/* delete entry from scode whitelist */
	/* CRITICAL SECTION in MP scenario: need to quiesce other CPUs or at least acquire spinlock */
	whitelist_size --;
	whitelist[i].gcr3 = 0;

	pagelist_free_all(whitelist[i].pl);
	vfree(whitelist[i].pl);

	return 0; 
}

/* test if the page is already in page_list
 * in order to avoid redundency in expose_page() */
int test_page_in_list(pte_t * page_list, pte_t page, u32 count)
{
	u32 i;
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
	unsigned int i;
	unsigned int j;
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
	wle->pte_page = vmalloc(MAX_REGPAGES_NUM*sizeof(pte_t));
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
				vfree(wle->pte_page);
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
	u32 i;

	void * linux_vmcb;
	u32 is_pae;

	is_pae = VCPU_gcr4(vcpu) & CR4_PAE;

	src_gpaddr = gpt_vaddr_to_paddr(vcpu, src);
  	dst_gpaddr = gpt_vaddr_to_paddr(vcpu, dst);

//	/* make sure the entire string are in same page */
//	if (is_pae) {
//		ASSERT (SAME_PAGE_PAE(src_gpaddr, src_gpaddr+len));
//		ASSERT (SAME_PAGE_PAE(dst_gpaddr, dst_gpaddr+len));
//	} else {
//		ASSERT (SAME_PAGE_NPAE(src_gpaddr, src_gpaddr+len));
//		ASSERT (SAME_PAGE_NPAE(dst_gpaddr, dst_gpaddr+len));
//	}
	src_hvaddr = (u8 *)(__gpa2hva__(src_gpaddr));
	dst_hvaddr = (u8 *)(__gpa2hva__(dst_gpaddr));
	//printf("[TV]   PM string value is:");
	//for( i=0 ; i<len ; i++ )  {
	//	printf("%x ", *(src_hvaddr+i));
	//}
	//printf("!\n");
	vmemcpy(dst_hvaddr, src_hvaddr, len);
}

u32 scode_marshall(VCPU * vcpu)
{
	u32 pm_addr, pm_addr_base, pm_value, pm_tmp;  /*parameter stack base address*/
	u32 pm_num, pm_type, pm_size, pm_size_sum; /*save pm information*/
	u32 grsp;
	u32 is_pae;
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
	put_32bit_aligned_value_to_guest(vcpu, (u32)pm_addr, whitelist[curr].gpm_num);
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
		pm_value = get_32bit_aligned_value_from_guest(vcpu, grsp+(pm_num-1)*4);
		pm_size_sum += 12;

		if (pm_size_sum > (whitelist[curr].gpm_size*PAGE_SIZE_4K))
		{
			dprintf(LOG_ERROR, "[TV] Fail: No enough space to save input params data!\n");
			perf_ctr_timer_discard(&g_tv_perf_ctrs[TV_PERF_CTR_MARSHALL], vcpu->idx);
			return 1;
		}

		/* save input params in input params memory for sensitive code */
		put_32bit_aligned_value_to_guest(vcpu, (u32)pm_addr, pm_type);
		put_32bit_aligned_value_to_guest(vcpu, (u32)pm_addr+4, pm_size);
		put_32bit_aligned_value_to_guest(vcpu, (u32)pm_addr+8, pm_value);
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

					memcpy_guest_to_guest(vcpu, pm_value, pm_addr, pm_size*4);

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
		put_32bit_aligned_value_to_guest(vcpu, new_rsp, pm_tmp);
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
	VCPU_set_current_root_pm(vcpu, whitelist[curr].pal_hpt_root);
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
	addr = get_32bit_aligned_value_from_guest(vcpu, (u32)whitelist[curr].grsp);
	VCPU_grsp_set(vcpu, VCPU_grsp(vcpu)-4);
	put_32bit_aligned_value_to_guest(vcpu, (u32)VCPU_grsp(vcpu), addr);
	/* store the return address in whitelist structure */
	whitelist[curr].return_v = addr;
	dprintf(LOG_TRACE, "[TV] scode return vaddr is %#x\n", whitelist[curr].return_v);

	dprintf(LOG_TRACE, "[TV] host stack pointer before running scode is %#x\n",(u32)VCPU_grsp(vcpu));

	perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_SWITCH_SCODE], vcpu->idx);
	return 0;
}

static void scode_unexpose_arch(VCPU * vcpu, whitelist_entry_t *wle)
{
	u32 i;
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
	vfree(wle->pte_page);
	wle->pte_page = 0;
	wle->pte_size = 0;
}

u32 scode_unmarshall(VCPU * vcpu)
{
	u32 pm_addr_base, pm_addr;
	u32 i, pm_num, pm_type, pm_size, pm_value;
	u32 value;

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
	pm_num = get_32bit_aligned_value_from_guest(vcpu, (u32)pm_addr);
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
		pm_type =  get_32bit_aligned_value_from_guest(vcpu, (u32)pm_addr);
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
					pm_size =  get_32bit_aligned_value_from_guest(vcpu, (u32)pm_addr);
					/* get pointer adddress in regular code */
					pm_value = get_32bit_aligned_value_from_guest(vcpu, (u32)pm_addr+4);
					pm_addr += 8;

					dprintf(LOG_TRACE, "[TV]   PM %d is a pointer (size %d, addr %#x)\n", i,  pm_size*4, pm_value);
					/*copy data from guest space to sensitive code*/
					memcpy_guest_to_guest(vcpu, pm_addr, pm_value, pm_size*4);
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
	} else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
		return (errorcode & PF_ERRORCODE_INST);
	} else {
		ASSERT(0);
	}
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

uint32_t scode_seal(VCPU * vcpu, uint32_t input_addr, uint32_t input_len, uint32_t tpmPcrInfo_addr, uint32_t output_addr, uint32_t output_len_addr)
{
	uint8_t indata[MAX_SEALDATA_LEN];  
	uint8_t output[MAX_SEALDATA_LEN]; 
	uint32_t outlen;
	uint32_t i, rv=0;

	TPM_PCR_INFO tpmPcrInfo;
	
	dprintf(LOG_TRACE, "\n[TV] ********** uTPM seal **********\n");
	dprintf(LOG_TRACE, "[TV] input addr: %x, len %d, pcr addr: %x, output addr: %x!\n", input_addr, input_len, tpmPcrInfo_addr, output_addr);

	if(!vcpu || !input_addr || !tpmPcrInfo_addr || !output_addr || !output_len_addr) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: !vcpu || !input_addr || !tpmPcrInfo_addr || !output_addr || !output_len_addr\n");
		return 1;
	}

	/**
	 * check input data length
	 */
	/* include seal data header and possible AES encryption padding */
	if (input_len > (MAX_SEALDATA_LEN - SEALDATA_HEADER_LEN - 16) ) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: input data length is too large, lenth %#x\n", input_len);
		return 1;
	}

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: no PAL is running!\n");
		return 1;
	}

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* copy input data to host */
	copy_from_guest(vcpu, indata, input_addr, input_len);
	copy_from_guest(vcpu, (uint8_t*)&tpmPcrInfo, tpmPcrInfo_addr, sizeof(TPM_PCR_INFO));

	dprintf(LOG_TRACE, "[TV] input len = %d!\n", input_len);
	print_hex("  indata: ", indata, input_len);
	print_hex("  tpmPcrInfo: ", (uint8_t*)&tpmPcrInfo, sizeof(TPM_PCR_INFO));


	/* seal, verifying output is not too large */
	rv = utpm_seal(&whitelist[scode_curr[vcpu->id]].utpm,
								 &tpmPcrInfo,
								 indata, input_len,
								 output, &outlen,
								 hmackey, aeskey);
	if (rv != 0 || outlen > MAX_SEALDATA_LEN) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: output data length is too large, lenth %#x\n", outlen);
		return rv;
	}
	print_hex("  sealedData: ", output, outlen);

	/*copy output to guest */
	copy_to_guest(vcpu, output_addr, output, outlen);

	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(vcpu, output_len_addr, outlen);

	return rv;
}

uint32_t scode_unseal(VCPU * vcpu, uint32_t input_addr, uint32_t input_len,
											uint32_t output_addr, uint32_t output_len_addr,
											uint32_t digestAtCreation_addr)
{
	uint32_t i;
	uint8_t indata[MAX_SEALDATA_LEN]; 
	uint8_t outdata[MAX_SEALDATA_LEN];
	uint32_t outlen;
	uint32_t ret;
	int index;
	TPM_COMPOSITE_HASH digestAtCreation;

	dprintf(LOG_TRACE, "\n[TV:scode] ********** uTPM unseal **********\n");
	dprintf(LOG_TRACE, "[TV:scode] input addr: %x, len %d, output addr: %x!\n",
					input_addr, input_len, output_addr);
	/* check input data length */
	if (input_len > MAX_SEALDATA_LEN) {
		dprintf(LOG_ERROR, "[TV:scode] Unseal ERROR: input data length is too large, lenth %#x\n", input_len);
		return 1;
	}

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV:scode] Seal ERROR: no PAL is running!\n");
		return 1;
	}

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* copy input data from guest */
	copy_from_guest(vcpu, indata, input_addr, input_len);

	print_hex("  [TV:scode] input data: ", indata, input_len);	

	/* unseal */
	if ((ret = utpm_unseal(&whitelist[scode_curr[vcpu->id]].utpm, indata, input_len,
												 outdata, &outlen, &digestAtCreation,
												 hmackey, aeskey))) {
		dprintf(LOG_ERROR, "[TV:scode] Unseal ERROR: utpm_unseal fail!\n");
		return 1;
	}

	print_hex("  [TV:scode] output (unsealed) data: ", outdata, outlen);	

	/* check output data length */
	if (outlen > MAX_SEALDATA_LEN ) {
		dprintf(LOG_ERROR, "[TV:scode] Unseal ERROR: output data length is too large, lenth %#x\n", outlen);
		return 1;
	}

	/* copy output to guest */
	copy_to_guest(vcpu, output_addr, outdata, outlen);
	copy_to_guest(vcpu, digestAtCreation_addr, (uint8_t*)&digestAtCreation, TPM_HASH_SIZE);
	
	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(vcpu, output_len_addr, outlen);
	return 0;
}


u32 scode_seal_deprecated(VCPU * vcpu, u32 input_addr, u32 input_len, u32 pcrAtRelease_addr, u32 output_addr, u32 output_len_addr)
{
	unsigned int i;
	int index;
	u32 outlen;
	u8 pcr[TPM_PCR_SIZE];
	u8 indata[MAX_SEALDATA_LEN];  
	u8 output[MAX_SEALDATA_LEN]; 

	dprintf(LOG_TRACE, "\n[TV] ********** uTPM seal DEPRECATED **********\n");
	dprintf(LOG_TRACE, "[TV] input addr: %x, len %d, pcr addr: %x, output addr: %x!\n", input_addr, input_len, pcrAtRelease_addr, output_addr);
	/* check input data length */
	/* include seal data header and possible AES encryption padding */
	if (input_len > (MAX_SEALDATA_LEN-SEALDATA_HEADER_LEN - 16) ) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: input data length is too large, lenth %#x\n", input_len);
		return 1;
	}

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: no PAL is running!\n");
		return 1;
	}

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* copy input data to host */
	copy_from_guest(vcpu, indata, input_addr, input_len);

#if 0
	dprintf(LOG_TRACE, "[TV] input len = %d!\n", input_len);
	dprintf(LOG_TRACE, "[TV] input data is:");
	for(i=0;i<input_len;i++) {
		dprintf(LOG_TRACE, "%x ", indata[i]);
	}
	dprintf(LOG_TRACE, "[TV] \n");
#endif

	if (pcrAtRelease_addr != 0) {
		/* seal data to other PAL */
		/* copy pcr value at release to host */
		copy_from_guest(vcpu, pcr, pcrAtRelease_addr, TPM_PCR_SIZE);
	} else {
		/* seal data to our own */
		/* use current PAL's PCR value */
		dprintf(LOG_TRACE, "[TV] get pcr from current PAL's softTPM!\n");
		vmemcpy(pcr, whitelist[scode_curr[vcpu->id]].utpm.pcr_bank, TPM_PCR_SIZE);
	}

#if 1
	dprintf(LOG_TRACE, "[TV] pcr value is:");
	for(i=0;i<TPM_PCR_SIZE;i++) {
		dprintf(LOG_TRACE, "%x ", pcr[i]);
	}
	dprintf(LOG_TRACE, "\n");
#endif

	/* seal */
	utpm_seal_deprecated(pcr, indata, input_len, output, &outlen, hmackey, aeskey);

#if 1
	dprintf(LOG_TRACE, "[TV] sealed data len = %d!\n", outlen);
	dprintf(LOG_TRACE, "[TV] sealed data is: ");
	for(i=0;i<outlen;i++) {
		dprintf(LOG_TRACE, "%x ", output[i]);
	}
	dprintf(LOG_TRACE, "\n");
#endif

	/* check output data length */
	if (outlen > MAX_SEALDATA_LEN) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: output data length is too large, lenth %#x\n", outlen);
		return 1;
	}

	/*copy output to guest */
	copy_to_guest(vcpu, output_addr, output, outlen);

	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(vcpu, output_len_addr, outlen);

	return 0;
}

u32 scode_unseal_deprecated(VCPU * vcpu, u32 input_addr, u32 input_len, u32 output_addr, u32 output_len_addr)
{
	unsigned int i;
	u8 indata[MAX_SEALDATA_LEN]; 
	u8 outdata[MAX_SEALDATA_LEN];
	u32 outlen;
	u32 ret;
	int index;

	dprintf(LOG_TRACE, "\n[TV] ********** uTPM unseal DEPRECATED **********\n");
	dprintf(LOG_TRACE, "[TV] input addr: %x, len %d, output addr: %x!\n", input_addr, input_len, output_addr);
	/* check input data length */
	if (input_len > MAX_SEALDATA_LEN) {
		dprintf(LOG_ERROR, "[TV] Unseal ERROR: input data length is too large, lenth %#x\n", input_len);
		return 1;
	}

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: no PAL is running!\n");
		return 1;
	}

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* copy input data from guest */
	copy_from_guest(vcpu, indata, input_addr, input_len);

#if 0
	dprintf(LOG_TRACE, "[TV] input len = %d!\n", input_len);
	dprintf(LOG_TRACE, "[TV] input data is:");
	for(i=0;i<input_len;i++) {
		dprintf(LOG_TRACE, "%x ", indata[i]);
	}
	dprintf(LOG_TRACE, "[TV] \n");
#endif

	/* unseal */
	if ((ret = utpm_unseal_deprecated(&whitelist[scode_curr[vcpu->id]].utpm, indata, input_len, outdata, &outlen, hmackey, aeskey))) {
		dprintf(LOG_ERROR, "[TV] Unseal ERROR: utpm_unseal fail!\n");
		return 1;
	}

#if 1
	dprintf(LOG_TRACE, "[TV] unsealed data len = %d!\n", outlen);
	dprintf(LOG_TRACE, "[TV] unsealed data is: ");
	for(i=0;i<outlen;i++) {
		dprintf(LOG_TRACE, "%x ", outdata[i]);
	}
	dprintf(LOG_TRACE, "\n");
#endif

	/* check output data length */
	if (outlen > MAX_SEALDATA_LEN ) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: output data length is too large, lenth %#x\n", outlen);
		return 1;
	}

	/* copy output to guest */
	copy_to_guest(vcpu, output_addr, outdata, outlen);

	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(vcpu, output_len_addr, outlen);
	return 0;
}

u32 scode_quote_deprecated(VCPU * vcpu, u32 nonce_addr, u32 tpmsel_addr, u32 out_addr, u32 out_len_addr)
{
	u8 outdata[TPM_QUOTE_SIZE];
	u8 nonce[TPM_NONCE_SIZE];
	u8 tpmsel[MAX_PCR_SEL_SIZE];
	u32 outlen, ret;
	u32 i, num;
	int index;
	u32 tpmsel_len;

	dprintf(LOG_TRACE, "\n[TV] ********** uTPM Quote [DEPRECATED] **********\n");
	dprintf(LOG_TRACE, "[TV] nonce addr: %x, tpmsel addr: %x, output addr %x, outlen addr: %x!\n", nonce_addr, tpmsel_addr, out_addr, out_len_addr);
	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] Quote ERROR: no PAL is running!\n");
		return 1;
	}	

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* get TPM PCR selection from guest */
	num = get_32bit_aligned_value_from_guest(vcpu, tpmsel_addr);
	if (num > MAX_PCR_SEL_NUM) {
		dprintf(LOG_ERROR, "[TV] Quote ERROR: select too many PCR!\n");
		return 1;
	}
	tpmsel_len = 4+4*num;
	dprintf(LOG_TRACE, "[TV] %d pcrs are selected!\n", num);

	copy_from_guest(vcpu, tpmsel, tpmsel_addr, tpmsel_len);
	for( i=0 ; i< num ; i++ )  {
		if (*(((u32 *)(tpmsel+4))+i) >= TPM_PCR_NUM) {
			dprintf(LOG_ERROR, "[TV] Quote ERROR: bad format of TPM PCR num!\n");
			return 1;
		}
	}

	/* get external nonce from guest */
	copy_from_guest(vcpu, nonce, nonce_addr, TPM_NONCE_SIZE);

#if 1
	dprintf(LOG_TRACE, "[TV] external nonce is: ");
	for(i=0;i<TPM_NONCE_SIZE;i++) {
		dprintf(LOG_TRACE, "%x ", nonce[i]);
	}
	dprintf(LOG_TRACE, "\n");
#endif

	if ((ret = utpm_quote_deprecated(nonce, outdata, &outlen, &whitelist[scode_curr[vcpu->id]].utpm, tpmsel, tpmsel_len, (u8 *)(&g_rsa))) != 0) {
		dprintf(LOG_ERROR, "[TV] quote ERROR: utpm_quote fail!\n");
		return 1;
	}

#if 0
	dprintf(LOG_TRACE, "[TV] quote data len = %d!\n", outlen);
	dprintf(LOG_TRACE, "[TV] quote data is: ");
	for(i=0;i<outlen;i++) {
		dprintf(LOG_TRACE, "%x ", outdata[i]);
	}
	dprintf(LOG_TRACE, "\n");
#endif

	/* copy output to guest */
	copy_to_guest(vcpu, out_addr, outdata, outlen);

	/* copy public key to guest */
	copy_to_guest(vcpu, out_addr + outlen, (u8 *)(g_rsa.N.p), TPM_RSA_KEY_LEN);
	outlen += TPM_RSA_KEY_LEN;

	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(vcpu, out_len_addr, outlen);
	return 0;
}

u32 scode_quote(VCPU * vcpu, u32 nonce_addr, u32 tpmsel_addr, u32 out_addr, u32 out_len_addr)
{
  uint8_t *outdata=NULL;
	TPM_NONCE nonce;
	TPM_PCR_SELECTION tpmsel;
	u32 outlen, ret=0;
	u32 i;
	int index;

	dprintf(LOG_TRACE, "\n[TV] ********** uTPM Quote **********\n");
	dprintf(LOG_TRACE, "[TV] nonce addr: %x, tpmsel addr: %x, output addr %x, outlen addr: %x!\n",
					nonce_addr, tpmsel_addr, out_addr, out_len_addr);

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] Quote ERROR: no PAL is running!\n");
		ret = 1;
		goto out;
	}	

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* get external nonce from guest */
	copy_from_guest(vcpu, (void*)&nonce, nonce_addr, sizeof(TPM_NONCE));

	/* get TPM PCR selection from guest */
	/* FIXME: sizeof(TPM_PCR_SELECTION) may eventually change dynamically */
	copy_from_guest(vcpu, (void*)&tpmsel, tpmsel_addr, sizeof(TPM_PCR_SELECTION));

	/* Get size of guest's output buffer */
	copy_from_guest(vcpu, (void*)&outlen, out_len_addr, sizeof(uint32_t));

	dprintf(LOG_TRACE, "[TV] Guest provided output buffer of %d bytes\n", outlen);

	/* FIXME: This is just a rough sanity check that catches some uninitialized variables. */
	if(outlen > 5*TPM_QUOTE_SIZE) {
			dprintf(LOG_ERROR, "[TV] ERROR: Guest-provided outlen value of %d seems ridiculous\n", outlen);
			ret = 1;
			goto out;
	}
	
	/**
	 * Allocate space to do internal processing
	 */
	if(NULL == (outdata = vmalloc(outlen))) {
			dprintf(LOG_ERROR, "[TV] ERROR: vmalloc(%d) failed!\n", outlen);
			ret = 1;
			goto out;
	}
	
	/* FIXME: Still want to return a modified "outlen" in case the input buffer was too small.
	   I.e., this fails too aggressively. */
	if ((ret = utpm_quote(&nonce, &tpmsel, outdata, &outlen, &whitelist[scode_curr[vcpu->id]].utpm,
												(u8 *)(&g_rsa))) != 0) {
		dprintf(LOG_ERROR, "[TV] ERROR: utpm_quote failed!\n");
		return 1;
	}

	/* Some sanity-checking. TODO: replace with asserts & use tighter bound */
	if(outlen > 2*TPM_QUOTE_SIZE) {
			dprintf(LOG_ERROR, "[TV] ERROR: outlen (%d) > 2*TPM_QUOTE_SIZE\n", outlen);
			outlen = TPM_QUOTE_SIZE; /* FIXME: We should return some kind of error code */
			/* return 1; */ /* Don't return from here; it causes some kind of crash in the PAL */
	}
	
	dprintf(LOG_TRACE, "[TV] quote data len = %d!\n", outlen);
	//print_hex("  QD: ", outdata, outlen);

	/* copy quote output to guest */
	copy_to_guest(vcpu, out_addr, outdata, outlen);

	dprintf(LOG_TRACE, "[TV] scode_quote: Survived copy_to_guest of %d bytes\n", outlen);
	
	/* copy quote output length to guest */
	put_32bit_aligned_value_to_guest(vcpu, out_len_addr, outlen);
	dprintf(LOG_TRACE, "[TV] scode_quote: Survived put_32bit_aligned_value_to_guest\n");

	out:

	if(outdata) { vfree(outdata); outdata = NULL; }
	
	return ret;
}

uint32_t scode_utpm_id_getpub(VCPU * vcpu, uint32_t gvaddr)
{
  uint8_t rsaModulus[TPM_RSA_KEY_LEN];
	dprintf(LOG_TRACE, "\n[TV] ********** uTPM id_getpub **********\n");

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] ID_GETPUB ERROR: no PAL is running!\n");
		return 1;
	}

	/* Must use MPI export function to get big endian N */
	if(mpi_write_binary(&g_rsa.N, rsaModulus, TPM_RSA_KEY_LEN) != 0) {
			dprintf(LOG_ERROR, "mpi_write_binary ERROR\n");
			return 1;
	}

	//print_hex("  N  : ", rsaModulus, TPM_RSA_KEY_LEN);
	
	/* XXX TODO FIXME: RSA public identity key should be part of uTPM
	 * structure and not a global variable here in scode.c */
	copy_to_guest(vcpu, gvaddr, rsaModulus, TPM_RSA_KEY_LEN);
	
	return 0;
}


void scode_release_all_shared_pages(VCPU *vcpu, whitelist_entry_t* entry)
{
	u32 i;
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
	hpt_remove_pal_pmes(vcpu,
											&entry->hpt_nested_walk_ctx,
											entry->pal_hpt_root,
											hpt_root_lvl(entry->hpt_nested_walk_ctx.t),
											&entry->scode_pages[scode_pages_shared_start],
											shared_page_count);
	/* XXX Should also revoke access to corresponding guest page table
	 * pages. Not doing it for now since won't normally hurt anything,
	 * and likely to rewrite handling of guest page tables soon.
	 */

	/* remove from pte's */
	entry->scode_size -= shared_page_count<<PAGE_SHIFT_4K;
}

u32 scode_share_range(VCPU * vcpu, whitelist_entry_t *entry, u32 gva_base, u32 gva_len)
{
	struct scode_sections_struct* section;
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
												entry->pal_hpt_root,
												hpt_root_lvl(entry->hpt_nested_walk_ctx.t),
												new_scode_pages,
												gva_len_pages);
		scode_expose_arch(vcpu, entry);
		hpt_insert_pal_pmes(vcpu, &entry->hpt_nested_walk_ctx,
												entry->pal_hpt_root,
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
	u32 i;
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

u32 scode_pcrread(VCPU * vcpu, u32 gvaddr, u32 num)
{
	int i;
	int index;
	TPM_DIGEST pcr;

	dprintf(LOG_TRACE, "\n[TV] ********** uTPM pcrread **********\n");

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] PCRRead ERROR: no PAL is running!\n");
		return 1;
	}

	/* make sure requested PCR number is in reasonable range */
	if (num >= TPM_PCR_NUM)
	{
		dprintf(LOG_ERROR, "[TV] PCRRead ERROR: pcr num %d not correct!\n", num);
		return 1;
	}

	/* read pcr value */
	utpm_pcrread(&pcr, &whitelist[scode_curr[vcpu->id]].utpm, num);

	/* return pcr value to guest */
	copy_to_guest(vcpu, gvaddr, pcr.value, TPM_PCR_SIZE);

	return 0;
}


u32 scode_pcrextend(VCPU * vcpu, u32 gvaddr, u32 len, u32 num)
{
	int index;
	u8 data[MAX_TPM_EXTEND_DATA_LEN]; 
	TPM_DIGEST hash;

	dprintf(LOG_TRACE, "\n[TV] ********** uTPM pcrextend **********\n");

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] PCRExtend ERROR: no PAL is running!\n");
		return 1;
	}

	/* make sure requested PCR number is in reasonable range */
	if (num >= TPM_PCR_NUM)
	{
		dprintf(LOG_ERROR, "[TV] PCRExtend ERROR: pcr num %d not correct!\n", num);
		return 1;
	}

	/* make sure the extended data is not too big */
	if (len > MAX_TPM_EXTEND_DATA_LEN)
	{
		dprintf(LOG_ERROR, "[TV] PCRExtend ERROR: extend data len %d not correct!\n", len);
		return 1;
	}

	/* get data from guest */
	copy_from_guest(vcpu, (u8 *)data, gvaddr, len);

	/* hash input data */
	sha1_csum((unsigned char*)data, len, hash.value);

	/* extend pcr */
	utpm_extend(&hash, &whitelist[scode_curr[vcpu->id]].utpm, num);

	return 0;
}

u32 scode_rand(VCPU * vcpu, u32 buffer_addr, u32 numbytes_addr)
{
	u32 ret;
	u8 buffer[MAX_TPM_RAND_DATA_LEN]; 
	u32 numbytes;

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] GenRandom ERROR: no PAL is running!\n");
		return 1;
	}

	// get the byte number requested
	numbytes = get_32bit_aligned_value_from_guest(vcpu, numbytes_addr);
	if (numbytes > MAX_TPM_RAND_DATA_LEN)
	{
		dprintf(LOG_ERROR, "[TV] GenRandom ERROR: requested rand data len %d not correct!\n", numbytes);
		return 1;
	}

	ret = utpm_rand(buffer, numbytes);
	if (ret == 0)
	{
		dprintf(LOG_ERROR, "[TV] GenRandom ERROR: rand byte error!");
		return 1;
	}

	/* copy random data to guest */
	copy_to_guest(vcpu, buffer_addr, buffer, ret);

	/* copy data length to guest */
	put_32bit_aligned_value_to_guest(vcpu, numbytes_addr, ret);

	return 0;
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */
