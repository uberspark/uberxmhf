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
#include "./include/tpm_sw.h"
#include "./include/sha1.h"
#include  "./include/rsa.h"
#include  "./include/random.h"

struct trustvisor_context * tv_ctx = 0;

/* SVM trustvisor context */
struct trustvisor_context svm_tv_ctx = {
	.nested_set_prot = svm_nested_set_prot,
	.nested_clear_prot = svm_nested_clear_prot,
	.nested_switch_scode = svm_nested_switch_scode,
	.nested_switch_regular = svm_nested_switch_regular,
	.nested_make_pt_accessible = svm_nested_make_pt_accessible,
	.nested_make_pt_unaccessible = svm_nested_make_pt_unaccessible,
	//.nested_breakpde = svm_nested_breakpde,
	//.nested_promote = svm_nested_promote,

	.scode_set_prot = svm_scode_set_prot,
	.scode_clear_prot = svm_scode_clear_prot,
	.scode_switch_scode = svm_scode_switch_scode,
	.scode_switch_regular = svm_scode_switch_regular,
	.scode_npf = svm_scode_npf,
};

/* VMX trustvisor context */
struct trustvisor_context vmx_tv_ctx = {
	.nested_set_prot = vmx_nested_set_prot,
	.nested_clear_prot = vmx_nested_clear_prot,
	.nested_switch_scode = vmx_nested_switch_scode,
	.nested_switch_regular = vmx_nested_switch_regular,
	.nested_make_pt_accessible = vmx_nested_make_pt_accessible,
	.nested_make_pt_unaccessible = vmx_nested_make_pt_unaccessible,
	//.nested_breakpde = 0,
	//.nested_promote = 0,

	.scode_set_prot = vmx_scode_set_prot,
	.scode_clear_prot = vmx_scode_clear_prot,
	.scode_switch_scode = vmx_scode_switch_scode,
	.scode_switch_regular = vmx_scode_switch_regular,
	.scode_npf = vmx_scode_npf,
};

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
		printf("FATAL ERROR: exceed the limitation of 2M page\n");
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
		printf("FATAL ERROR: exceed the limitation of 2M page\n");
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



/* search scode in whitelist */
int scode_in_list(u64 gcr3, u32 gvaddr)
{
	u32 i, j;

	for (i = 0; i < whitelist_max; i ++)
	{
		if (gcr3 == whitelist[i].gcr3) {
			for( j=0 ; j<(u32)(whitelist[i].scode_info.section_num) ; j++ )  {
				if( (gvaddr >= whitelist[i].scode_info.ps_str[j].start_addr) &&
						(gvaddr < ((whitelist[i].scode_info.ps_str[j].start_addr)+((whitelist[i].scode_info.ps_str[j].page_num)<<PAGE_SHIFT_4K)))  )  {
					printf("[TV] find gvaddr %#x in scode %d section No.%d !\n", gvaddr, i, j+1);
					return i;
				}
			}
		}
	}
	printf("[TV] no matching scode found for gvaddr %#x!\n", gvaddr);
	return -1;
}

u32 scode_measure(u8 * pcr, u32 pte_page, u32 size)
{
	u32 i; 
	u32 paddr;
	pt_t pte_pages = (pt_t)pte_page;
	sha1_context ctx;
	u8 sha1sum[SHA1_CHECKSUM_LEN];

	printf("[TV] measure scode and extend uTPM PCR value!\n");
	sha1_starts(&ctx);
	for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
	{
		/* only measure SENTRY, STEXT, SDATA pages */
		paddr = PAGE_ALIGN_4K(pte_pages[i]);
		if((pte_pages[i] & 0x7)!=0)  {
			printf("[TV]   measure scode page %d paddr %#x\n", i+1, paddr);
			sha1_update(&ctx, (u8 *)paddr, PAGE_SIZE_4K);
		} else {
			printf("[TV]   ignore scode page %d paddr %#x\n", i+1, paddr);
		}
	}
	sha1_finish(&ctx, sha1sum);

	/* extend pcr 0 */
	stpm_extend(sha1sum, pcr, 0);

	return 0;
}

/* initialize all the scode related variables and buffers */
void init_scode(VCPU * vcpu)
{
	u32 inum, max;
	/* populate TrustVisor context acorrding to CPU vendor */
	if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
		printf("set up VMX context!\n");
		tv_ctx = (struct trustvisor_context *)&vmx_tv_ctx;
	} else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
		printf("set up SVM context!\n");
		tv_ctx = (struct trustvisor_context *)&svm_tv_ctx;
	} else {
		printf("unknow cpu vendor type!\n");
		HALT();
	}

	/* initialize heap memory */
	mem_init();

	scode_whitelist = (unsigned int *)vmalloc(WHITELIST_LIMIT);
	printf("[TV] alloc %dKB mem for scode_list at %x!\n", (WHITELIST_LIMIT/1024), (unsigned int)scode_whitelist);
	scode_pfn_bitmap = (unsigned char *)vmalloc(PFN_BITMAP_LIMIT);
	printf("[TV] alloc %dKB mem for pfn_bitmap at %x!\n", (PFN_BITMAP_LIMIT/1024), (unsigned int)scode_pfn_bitmap);
	scode_pfn_bitmap_2M = (unsigned short *)vmalloc(PFN_BITMAP_2M_LIMIT);
	printf("[TV] alloc %dKB mem for pfn_bitmap_2M at %x!\n", (PFN_BITMAP_LIMIT/1024), (unsigned int)scode_pfn_bitmap_2M);

	vmemset(scode_whitelist, 0, WHITELIST_LIMIT); 
	vmemset(scode_pfn_bitmap, 0, PFN_BITMAP_LIMIT);
	vmemset(scode_pfn_bitmap_2M, 0, PFN_BITMAP_2M_LIMIT);

	whitelist = (whitelist_entry_t *)scode_whitelist;
	whitelist_size = 0;
	whitelist_max = WHITELIST_LIMIT / sizeof(whitelist_entry_t);
	printf("[TV] whitelist max = %d!\n", whitelist_max);

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
	printf("[TV] PRNG init!\n");

	/* aeskey and hmac are identical for different PAL, so that we can seal data from one PAL to another PAL */
	rand_bytes(aeskey, (TPM_AES_KEY_LEN>>3));
	printf("[TV] AES key generated!\n");
	rand_bytes(hmackey, 20);
	printf("[TV] HMAC key generated!\n");

	/* init RSA key required in uTPM Quote */
	rsa_init(&g_rsa, RSA_PKCS_V15, RSA_SHA1);
	rsa_gen_key(&g_rsa, (TPM_RSA_KEY_LEN<<3), 65537);
	printf("[TV] RSA key pair generated!\n");
}

/* VMX related SCODE routines */

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
u32 vmx_scode_set_prot(VCPU *vcpu, u32 pte_page, u32 size)
{
	u32 i; 
	u32 pfn;
	pt_t pte_pages = (pt_t)pte_page;
	int type =0; 
#ifdef __MP_VERSION__
	u32 k;
	VCPU * tmpcpu;
#endif

	printf("[TV] scode registration on local CPU %02x!\n", vcpu->id);
	for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
	{
		pfn = pte_pages[i] >> PAGE_SHIFT_4K;
		if (!test_page_scode_bitmap(pfn))
		{
			set_page_scode_bitmap(pfn);
//			set_page_scode_bitmap_2M(pfn);

			/* XXX FIXME: temporary disable DEV setting here! */
		//	set_page_dev_prot(pfn);
			vmx_nested_set_prot(vcpu, pte_pages[i], 0);
		}else
		{
			printf("[TV] Set scode page permission error! pfn %#x have already been registered!\n", pfn);
			break;
		}
	}

	/* exception detected above, need to recover the previous changes */
	if (i < (size >> PAGE_SHIFT_4K))
	{
		printf("[TV] recover scode page permission!\n");
		for (; i > 0; i --)
		{
			pfn = pte_pages[i - 1] >> PAGE_SHIFT_4K;
			/* XXX FIXME: temporary disable DEV setting here! */
			//clear_page_dev_prot(pfn);
			vmx_nested_clear_prot(vcpu, pte_pages[i-1]);

			clear_page_scode_bitmap(pfn);
//			if (clear_page_scode_bitmap_2M(pfn) == 0)
//				nested_promote(vcpu, pfn);
		}
		return 1;
	}

#ifdef __MP_VERSION__
	/* not local CPU, set all mem sections unpresent */
	for( k=0 ; k<g_midtable_numentries ; k++ )  {
		tmpcpu = (VCPU *)(g_midtable[k].vcpu_vaddr_ptr);
		if (tmpcpu->id != vcpu->id) {
			printf("[TV] scode registration on CPU %02x!\n", tmpcpu->id);
			for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
			{
				pfn = pte_pages[i] >> PAGE_SHIFT_4K;
				/* XXX FIXME: temporary disable DEV setting here! */
				//	set_page_dev_prot(pfn);
				vmx_nested_set_prot(tmpcpu, pte_pages[i],0);
			}
		}
	}
#endif

	return 0;
}

void vmx_scode_clear_prot(VCPU * vcpu, u32 pte_page, u32 size)
{
	u32 i; 
	u32 pfn;
	pt_t pte_pages = (pt_t)pte_page;
#ifdef __MP_VERSION__
	u32 k;
	VCPU * tmpcpu;
#endif

	/* set up page permission in local CPU */
	printf("[TV] scode unreg on local CPU %02x!\n", vcpu->id);
	for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
	{
		pfn = pte_pages[i] >> PAGE_SHIFT_4K;
		if (test_page_scode_bitmap(pfn))
		{
			/* XXX FIXME: temporary disable DEV setting here! */
			//clear_page_dev_prot(pfn);
			vmx_nested_clear_prot(vcpu, pte_pages[i]);

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
			printf("[TV] scode unreg on CPU %02x!\n", tmpcpu->id);
			for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
			{
				pfn = pte_pages[i] >> PAGE_SHIFT_4K;
				/* XXX FIXME: temporary disable DEV setting here! */
				//	set_page_dev_prot(pfn);
				vmx_nested_clear_prot(tmpcpu, pte_pages[i]);
			}
		}
	}
#endif

}

/* parse scode paramter info ( scode registration input) */
int parse_params_info(VCPU * vcpu, struct scode_params_info* pm_info, u32 pm_addr)
{
	u32 i, num;
	u32 addr;
	addr = pm_addr;
	/* get parameter number */
	num = pm_info->params_num = get_32bit_aligned_value_from_guest(vcpu, addr);
	addr += 4;
	printf("[TV] pm_info %#x, # of paramters is %d\n", pm_addr, num);
	if (num > MAX_PARAMS_NUM) {
		printf("[TV] number of scode sections exceeds limit!\n");
		return 1;
	}

	for (i = 0; i < num; i++)
	{
		pm_info->pm_str[i].type = get_32bit_aligned_value_from_guest(vcpu, addr);
		pm_info->pm_str[i].size = get_32bit_aligned_value_from_guest(vcpu, addr+4);
		printf("[TV] parameter %d type %d size %d\n", i+1, pm_info->pm_str[i].type, pm_info->pm_str[i].size);
		addr += 8;
	}
	return 0;
}



/* parse scode sections info (scode registration input) */
int parse_memsect_info(VCPU * vcpu, whitelist_entry_t * wle, u32 ps_addr)
{
	int i, num, pnum, is_get_param, is_get_stack;
	int type, size;
	unsigned int start;
	u32 addr = ps_addr;
	struct scode_sections_info * scode_info = &(wle->scode_info);

	/* get parameter number */
	num = scode_info->section_num = get_32bit_aligned_value_from_guest(vcpu, addr);
	addr += 4;
	printf("[TV] scode_info addr %x, # of section is %d\n", (int)(scode_info), num);
	if( num > MAX_SECTION_NUM )  {
		printf("[TV] number of scode sections exceeds limit!\n");
		return 1;
	}

	/* parse section type, start address and size */
	pnum = 0;
	is_get_param=0;
	is_get_stack=0;
	for (i = 0; i < num; i++) {
		type = scode_info->ps_str[i].type = get_32bit_aligned_value_from_guest(vcpu, addr);
		start = scode_info->ps_str[i].start_addr = get_32bit_aligned_value_from_guest(vcpu, addr+4);
		/* make sure the addr is 4kb page aligned */
		start = start & ~0xFFF;
		size = scode_info->ps_str[i].page_num = get_32bit_aligned_value_from_guest(vcpu, addr+8);
		switch ( type )  {
			case SECTION_TYPE_PARAM :
				{
					/* set param page num and addr */
					if (!is_get_param) {
						wle->gpm_size=size;
						wle->gpmp=start+0x10;
						is_get_param=1;
						if (guest_pt_check_user_rw(vcpu, start, size)) {
							printf("[TV] ERROR: SCODE_PARAM pages are not user writable!\n");
							return 1;
						}
					}
				}
				break;
			case SECTION_TYPE_STACK :
				{
					/* set stack page num and addr */
					if (!is_get_stack) {
						wle->gss_size=size;
						wle->gssp=start+(size<<PAGE_SHIFT_4K)-0x10;
						is_get_stack=1;
						if (guest_pt_check_user_rw(vcpu, start, size)) {
							printf("[TV] ERROR: SCODE_STACK pages are not user writable!\n");
							return 1;
						}
					}
				}
				break;
			default :
				break;
		}
		pnum += size;
		printf("[TV] section %d type %d addr %#x size %d\n",i+1, type, start, size);
		addr += 12;
	}

	if (pnum > MAX_REGPAGES_NUM) {
		printf("[TV] number of scode pages exceeds limit!\n");
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
	struct scode_sections_struct * ginfo; 
	void * linux_vmcb;
	u64 gcr3;

	if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
		linux_vmcb = (struct _vmx_vmcsfields *)(&(vcpu->vmcs));
		gcr3 = ((struct _vmx_vmcsfields *)linux_vmcb)->guest_CR3;
	} else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
		linux_vmcb = (struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr);
		gcr3 = ((struct vmcb_struct *)linux_vmcb)->cr3;
	} else {
		printf("unknown cpu vendor!\n");
		return 1;
	}

	printf("\n[TV] ************************************\n");
	printf("[TV] ********** scode register **********\n");
	printf("[TV] ************************************\n");

	if (whitelist_size == whitelist_max)
	{
		printf("[TV] FATAL ERROR: too many registered scode, the limitation is %d\n", whitelist_max);
		return 1;
	}

	printf("[TV] CPU(0x%02x): add to whitelist,  scode_info %#x, scode_pm %#x, gventry %#x\n", vcpu->id, scode_info, scode_pm, gventry);

	/* ATTN: we should assign a ID for each registered sensitive code
	 * so we know what to verify each time
	 */
	whitelist_new.id = 0;
	whitelist_new.gcr3 = gcr3;
	whitelist_new.grsp = (u32)-1;

	/* store scode entry point */
	whitelist_new.entry_v = gventry;
	whitelist_new.entry_p = gpt_vaddr_to_paddr(vcpu, gventry); 
	printf("[TV] CR3 value is %#llx, entry point vaddr is %#x, paddr is %#x\n", gcr3, whitelist_new.entry_v, whitelist_new.entry_p);

	/* parse parameter structure */
	if (parse_params_info(vcpu, &(whitelist_new.params_info), scode_pm)) {
		printf("[TV] Registration Failed. Scode param info incorrect! \n");
		return 1;
	}
	whitelist_new.gpm_num = whitelist_new.params_info.params_num;
	/* parse scode sections */
	if (parse_memsect_info(vcpu, &(whitelist_new), scode_info)) {
		printf("[TV] Registration Failed. Scode section info incorrect! \n");
		return 1;
	}

	/* register pages in each scode section */
	whitelist_new.scode_page = (u32)((u64 *)vmalloc(MAX_REGPAGES_NUM<<3));
	whitelist_new.scode_size = 0;
	for( i=0 ; i < (u32)(whitelist_new.scode_info.section_num) ; i++ )  {
		ginfo = &(whitelist_new.scode_info.ps_str[i]);
		if (guest_pt_copy(vcpu, whitelist_new.scode_page+((whitelist_new.scode_size)<<3), ginfo->start_addr, (ginfo->page_num)<<PAGE_SHIFT_4K, ginfo->type)) {
			vfree((void *)(whitelist_new.scode_page));
			printf("[TV] SECURITY: Registration Failed. Probably some page of sensitive code is not in memory yet\n");
			return 1;
		}
		whitelist_new.scode_size += ginfo->page_num;
	}
	whitelist_new.scode_size = (whitelist_new.scode_size) << PAGE_SHIFT_4K;

	/* set up scode pages permission (also flush TLB) */
	/* CRITICAL SECTION in MP scenario: need to quiesce other CPUs or at least acquire spinlock */
	if (tv_ctx->scode_set_prot(vcpu, whitelist_new.scode_page, whitelist_new.scode_size))
	{
		vfree((void *)(whitelist_new.scode_page));
		printf("[TV] SECURITY: Registration Failed. Probably some page has already been used by other sensitive code.\n");
		return 1;
	}

	/* initialize software TPM PCR */
	vmemset(whitelist_new.pcr, 0, TPM_PCR_SIZE*TPM_PCR_NUM); 

	/* hash the entire SSCB code, and then extend the hash value into uTPM PCR[0] */
	if (scode_measure(whitelist_new.pcr, whitelist_new.scode_page, whitelist_new.scode_size))
	{
		tv_ctx->scode_clear_prot(vcpu, whitelist_new.scode_page, whitelist_new.scode_size);
		vfree((void *)(whitelist_new.scode_page));
		printf("[TV] SECURITY: Registration Failed. sensitived code cannot be verified.\n");
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
		printf("[TV] FATAL ERROR: no room for new scode, the limitation is %d\n", whitelist_max);
		return 1;
	}
	whitelist_size ++;
	vmemcpy(whitelist + i, &whitelist_new, sizeof(whitelist_entry_t));


	return 0; 
}

/* unregister scode in whitelist */
u32 scode_unregister(VCPU * vcpu, u32 gvaddr) 
{
	u32 i, j;

	void * linux_vmcb;
	u64 gcr3;

	if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
		linux_vmcb = (struct _vmx_vmcsfields *)(&(vcpu->vmcs));
		gcr3 = ((struct _vmx_vmcsfields *)linux_vmcb)->guest_CR3;
	} else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
		linux_vmcb = (struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr);
		gcr3 = ((struct vmcb_struct *)linux_vmcb)->cr3;
	} else {
		printf("unknown cpu vendor!\n");
		return 1;
	}

	printf("\n[TV] ************************************\n");
	printf("[TV] ********* scode unregister *********\n");
	printf("[TV] ************************************\n");

	if (whitelist_size == 0)
	{
		printf("[TV] FATAL ERROR: no scode registered currently\n");
		return 1;
	}

	printf("[TV] CPU(%02x): remove from whitelist gcr3 %#llx, gvaddr %#x\n", vcpu->id, gcr3, gvaddr);

	for (i = 0; i < whitelist_max; i ++)
	{
		/* find scode with correct cr3 and entry point */
		if ((whitelist[i].gcr3 == gcr3) && (whitelist[i].entry_v == gvaddr))
			break;
	}

	if (i >= whitelist_max) 
	{
		printf("[TV] SECURITY: UnRegistration Failed. no matching sensitive code found\n");
		return 1;
	}

	/* if we find one to remove, we also need to clear the physcial page number
	 * vector 
	 */
	/* CRITICAL SECTION in MP scenario: need to quiesce other CPUs or at least acquire spinlock */
	if (whitelist[i].scode_page)
	{
		tv_ctx->scode_clear_prot(vcpu, whitelist[i].scode_page, whitelist[i].scode_size);
		vfree((void *)(whitelist[i].scode_page));
		whitelist[i].scode_page = 0;
	}

	/* delete entry from scode whitelist */
	/* CRITICAL SECTION in MP scenario: need to quiesce other CPUs or at least acquire spinlock */
	whitelist_size --;
	whitelist[i].gcr3 = 0;

	return 0; 
}

/* test if the page is already in page_list
 * in order to avoid redundency in expose_page() */
int test_page_in_list(u64 * page_list, u64 page, u32 count)
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
void expose_page (u64 * page_list, u64 page, u32 * count)
{
	if (page != 0xFFFFFFFF) {
		if (!test_page_in_list(page_list, page, *count)) {
			page_list[(*count)]=page;
			*count = (*count)+1;
			/* set up DEV vector to prevent DMA attack */
			/* XXX FIXME: temporarily disable */
			//set_page_dev_prot(pfn);
			printf("[TV]   expose page %#llx \n", page);
		}
	}
}

/* find all PTE entry pages that is related to access scode and GDT */
void scode_expose_arch(VCPU *vcpu)
{
	u32 i;
	u32 j;
	u64 *pte_page;
	u32 pte_count = 0;
	u32 gpaddr = 0;
	void * linux_vmcb;
	u32 is_pae;
	u32 gdtr;
	struct scode_sections_struct * ginfo;
	u64 tmp_page[3];
	u32 tmp_count=0;
	int curr=scode_curr[vcpu->id];
	pt_t sp = (pt_t)(whitelist[curr].scode_page);
	u32 gcr3_flag=0;

	if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
		linux_vmcb = (struct _vmx_vmcsfields *)(&(vcpu->vmcs));
		is_pae = ((struct _vmx_vmcsfields *)linux_vmcb)->guest_CR4 & CR4_PAE;
		gdtr = ((struct _vmx_vmcsfields *)linux_vmcb)->guest_GDTR_base;
	} else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
		linux_vmcb = (struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr);
		is_pae = ((struct vmcb_struct *)linux_vmcb)->cr4 & CR4_PAE;
		gdtr = ((struct vmcb_struct *)linux_vmcb)->gdtr.base;
	} else {
		printf("unknown cpu vendor!\n");
		HALT();
	}

	/* alloc memory for page table entry holder */
	whitelist[curr].pte_page = (u32)((u64 *)vmalloc(MAX_REGPAGES_NUM<<5));
	pte_page = (u64 *)(whitelist[curr].pte_page);

	/* get related page tables for scode */
	/* Here we walk guest page table, and find out all the pdp,pd,pt entry
	   that is necessary to translate gvaddr */
	printf("[TV] expose SCODE related PTE pages\n");
	for( i=0 ; i < (u32)(whitelist[curr].scode_info.section_num) ; i++ )  {
		ginfo = &(whitelist[curr].scode_info.ps_str[i]);
		for( j=0 ; j<(u32)(ginfo->page_num); j++ )  {
			gpaddr = gpt_get_ptpages(vcpu, ginfo->start_addr+(j<<PAGE_SHIFT_4K), tmp_page, &tmp_page[1], &tmp_page[2]);

			/* check gvaddr to gpaddr mapping */
			if( gpaddr != (((u32)(*(sp+tmp_count+j)))&(~(0x7))))  {
				printf("[TV] SECURITY: scode vaddr %x -> paddr %#llx mapping changed! invalide gpaddr is %x!\n", ginfo->start_addr+(j<<PAGE_SHIFT_4K), *(sp+tmp_count+j), gpaddr);
				vfree((void *)(whitelist[curr].pte_page));
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
	printf("[TV] expose GDT related PTE pages\n");
	gpaddr = gpt_get_ptpages(vcpu, gdtr, NULL, &tmp_page[1], &tmp_page[2]);

	EXPOSE_PAGE(gpaddr);
	EXPOSE_PAGE(tmp_page[1]);
	EXPOSE_PAGE(tmp_page[2]);

	whitelist[curr].pte_size = pte_count << PAGE_SHIFT_4K;
}

void memcpy_guest_to_guest(VCPU * vcpu, u32 src, u32 dst, u32 len)
{
	u32 src_gpaddr, dst_gpaddr;
	u8 *src_hvaddr, *dst_hvaddr;
	u32 i;

	void * linux_vmcb;
	u32 is_pae;

	if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
		linux_vmcb = (struct _vmx_vmcsfields *)(&(vcpu->vmcs));
		is_pae = ((struct _vmx_vmcsfields *)linux_vmcb)->guest_CR4 & CR4_PAE;
	} else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
		linux_vmcb = (struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr);
		is_pae = ((struct vmcb_struct *)linux_vmcb)->cr4 & CR4_PAE;
	} else {
		printf("unknown cpu vendor!\n");
		HALT();
	}

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
	void * linux_vmcb;
	u32 is_pae;
	u32 new_rsp;
	int curr=scode_curr[vcpu->id];

	if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
		linux_vmcb = (struct _vmx_vmcsfields *)(&(vcpu->vmcs));
	} else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
		linux_vmcb = (struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr);
	} else {
		printf("unknown cpu vendor!\n");
		return 1;
	}

	printf("[TV] marshalling scode parameters!\n");
	if(whitelist[curr].gpm_num == 0)
	{
		printf("[TV] params number is 0. Return!\n");
		return 0;
	}

	/* memory address for input parameter in sensitive code */
	pm_addr_base = whitelist[curr].gpmp;
	printf("[TV] parameter page base address is %#x\n", pm_addr_base);

	/* address for parameters in guest stack */
	grsp = (u32)whitelist[curr].grsp + 4; /*the stack pointer of parameters in guest stack*/

	/* save params number */
	pm_addr = pm_addr_base;
	put_32bit_aligned_value_to_guest(vcpu, (u32)pm_addr, whitelist[curr].gpm_num);
	pm_addr += 4;
	pm_size_sum = 4; /*memory used in input pms section*/
	printf("[TV] params number is %d\n", whitelist[curr].gpm_num);

	if (whitelist[curr].gpm_num > MAX_PARAMS_NUM)
	{
		printf("[TV] Fail: param num is too big!\n");
		return 1;
	}

	/* begin to process the params*/
	for (pm_num = whitelist[curr].gpm_num; pm_num > 0; pm_num--) /*the last parameter should be pushed in stack first*/
	{
		/* get param information*/
		pm_type = whitelist[curr].params_info.pm_str[pm_num-1].type;
		pm_size = whitelist[curr].params_info.pm_str[pm_num-1].size;
		/* get param value from guest stack */
		pm_value = get_32bit_aligned_value_from_guest(vcpu, grsp+(pm_num-1)*4);
		pm_size_sum += 12;

		if (pm_size_sum > (whitelist[curr].gpm_size*PAGE_SIZE_4K))
		{
			printf("[TV] Fail: No enough space to save input params data!\n");
			return 1;
		}

		/* save input params in input params memory for sensitive code */
		put_32bit_aligned_value_to_guest(vcpu, (u32)pm_addr, pm_type);
		put_32bit_aligned_value_to_guest(vcpu, (u32)pm_addr+4, pm_size);
		put_32bit_aligned_value_to_guest(vcpu, (u32)pm_addr+8, pm_value);
		pm_addr += 12;
		switch (pm_type)
		{
			case PM_TYPE_INTEGER: /* integer */
				{        
					/* put the parameter value in sensitive code stack */
					pm_tmp = pm_value;
					printf("[TV]   PM %d is a integer (size %d, value %#x)\n", pm_num, pm_size, pm_value);
					break;
				}
			case PM_TYPE_POINTER: /* pointer */
				{
					/*copy data from guest space to sensitive code*/
					pm_size_sum += 4*pm_size;
					if (pm_size_sum > (whitelist[curr].gpm_size*PAGE_SIZE_4K))
					{
						printf("[TV] Fail: No enough space to save input params data!\n");
						return 1;
					}

					/* make sure that this pointer point to mem regeion that can be r/w by user */
					if (guest_pt_check_user_rw(vcpu, pm_value, (pm_value+pm_size*4-(pm_value & (~0xFFF)))/4096+1)) {
						printf("[TV] Fail: input param data region is not user writable!\n");
						return 1;
					}

					memcpy_guest_to_guest(vcpu, pm_value, pm_addr, pm_size*4);

					/* put pointer address in sensitive code stack*/
					pm_tmp = pm_addr;
					printf("[TV]   PM %d is a pointer (size %d, addr %#x)\n", pm_num, pm_size*4, pm_value);
					pm_addr += 4*pm_size;
					break;
				}
			default: /* other */
				printf("[TV] Fail: unknown parameter %d type %d \n", pm_num, pm_type);
				return 1;
		}
		if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
			new_rsp = ((struct _vmx_vmcsfields *)linux_vmcb)->guest_RSP - 4;
			((struct _vmx_vmcsfields *)linux_vmcb)->guest_RSP = new_rsp;
		} else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
			new_rsp = ((struct vmcb_struct *)linux_vmcb)->rsp - 4;
			((struct vmcb_struct *)linux_vmcb)->rsp = new_rsp;
		} else {
			printf("unknown cpu vendor!\n");
			return 1;
		}
		put_32bit_aligned_value_to_guest(vcpu, new_rsp, pm_tmp);
	}
	return 0;
}



//todo: switch from regular code to sensitive code
u32 vmx_scode_switch_scode(VCPU * vcpu)
{
	u32 addr;
	int curr=scode_curr[vcpu->id];

	struct _vmx_vmcsfields * linux_vmcb = (struct _vmx_vmcsfields *)(&(vcpu->vmcs));

	printf("\n[TV] ************************************\n");
	printf("[TV] ********* switch to scode **********\n");
	printf("[TV] ************************************\n");

	/* save the guest stack pointer and set new stack pointer to scode stack */
	printf("[TV] saved guest regular stack %#x, switch to sensitive code stack %#x\n", (u32)linux_vmcb->guest_RSP, whitelist[curr].gssp);
	whitelist[curr].grsp = (u32)linux_vmcb->guest_RSP; 
	linux_vmcb->guest_RSP = whitelist[curr].gssp; 

	/* input parameter marshalling */
	if (scode_marshall(vcpu)){
		/* error in parameter marshalling */
		/* restore regular code stack */
		linux_vmcb->guest_RSP = whitelist[curr].grsp; 
		whitelist[curr].grsp = (u32)-1; 
		return 1;
	}

	/* find all PTE pages related to access scode and GDT */
	scode_expose_arch(vcpu);

	/* change NPT permission for all PTE pages and scode pages */
	printf("[TV] change NPT permission to run PAL!\n"); 
	vmx_nested_switch_scode(vcpu, whitelist[curr].scode_page, whitelist[curr].scode_size,
			(u32)whitelist[curr].pte_page, whitelist[curr].pte_size);
		
	/* disable interrupts */
	linux_vmcb->guest_RFLAGS &= ~EFLAGS_IF;

//	/* set the sensitive code to run in ring 3 */
//	linux_vmcb->cpl = 3;

	/* write the return address to scode stack */
	addr = get_32bit_aligned_value_from_guest(vcpu, (u32)whitelist[curr].grsp);
	linux_vmcb->guest_RSP -= 4;
	put_32bit_aligned_value_to_guest(vcpu, (u32)(linux_vmcb->guest_RSP), addr);
	/* store the return address in whitelist structure */
	whitelist[curr].return_v = addr;
	printf("[TV] scode return vaddr is %#x\n", whitelist[curr].return_v);

	printf("[TV] host stack pointer before running scode is %#x\n",(u32)linux_vmcb->guest_RSP);
	return 0;
}

void scode_unexpose_arch(VCPU * vcpu)
{
	u32 i;
	int curr=scode_curr[vcpu->id];
	u64 * page = (u64 *)(whitelist[curr].pte_page);
	printf("[TV] unexpose SCODE and GDT related to PTE pages\n");
	/* clear page bitmap set in scode_expose_arch() */
	for (i=0; i<((whitelist[curr].pte_size)>>PAGE_SHIFT_4K);i++) {
		clear_page_scode_bitmap(((page[i])>>PAGE_SHIFT_4K));
		/* XXX FIXME: temporarily disable */
	//	clear_page_dev_prot(((page[i])>>PAGE_SHIFT_4K));
	}

	/* free pte_page to save heap space,
	 * next expose will alloc a new pte_page */
	vfree((void *)(whitelist[curr].pte_page));
	whitelist[curr].pte_page = 0;
	whitelist[curr].pte_size = 0;
}

u32 scode_unmarshall(VCPU * vcpu)
{
	u32 pm_addr_base, pm_addr;
	u32 i, pm_num, pm_type, pm_size, pm_value;
	u32 value;

	int curr=scode_curr[vcpu->id];
	//struct _vmx_vmcsfields * linux_vmcb = (struct _vmx_vmcsfields *)(&(vcpu->vmcs));

	printf("[TV] unmarshalling scode parameters!\n");
	if (whitelist[curr].gpm_num == 0)
	{
		printf("[TV] unmarshall pm numbuer is 0. Return!\n");
		return 0;
	}

	/* memory address for input parameter in sensitive code */
	pm_addr_base = whitelist[curr].gpmp;
	printf("[TV] parameter page base address is %#x\n", pm_addr_base);

	/* get params number */
	pm_addr = pm_addr_base;
	pm_num = get_32bit_aligned_value_from_guest(vcpu, (u32)pm_addr);
	pm_addr += 4;
	printf("[TV] params number is %d\n", pm_num);
	if (pm_num > MAX_PARAMS_NUM)
	{
		printf("[TV] Fail: parameter number too big!\n");
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
			case PM_TYPE_INTEGER: /*integer*/
				{
					/* don't need to put integer back to regular code stack */
					pm_addr += 8; 
					printf("[TV]   skip an integer parameter!\n"); 
					break;
				}
			case PM_TYPE_POINTER: /* pointer */
				{
					pm_size =  get_32bit_aligned_value_from_guest(vcpu, (u32)pm_addr);
					/* get pointer adddress in regular code */
					pm_value = get_32bit_aligned_value_from_guest(vcpu, (u32)pm_addr+4);
					pm_addr += 8;

					printf("[TV]   PM %d is a pointer (size %d, addr %#x)\n", i,  pm_size*4, pm_value);
					/*copy data from guest space to sensitive code*/
					memcpy_guest_to_guest(vcpu, pm_addr, pm_value, pm_size*4);
					pm_addr += 4*pm_size;
					break;
				}

			default: /* other */
				printf("[TV] Fail: unknown parameter %d type %d \n", i, pm_type);
				return 1;
		} // end switch

	} //end for loop 
	return 0;
}

//switch from sensitive code to regular code
u32 vmx_scode_switch_regular(VCPU * vcpu)
{
	int curr=scode_curr[vcpu->id];
	struct _vmx_vmcsfields * linux_vmcb = (struct _vmx_vmcsfields *)(&(vcpu->vmcs));

	printf("\n[TV] ************************************\n");
	printf("[TV] ***** switch to regular code  ******\n");
	printf("[TV] ************************************\n");

	/* marshalling parameters back to regular code */
	if (!scode_unmarshall(vcpu)){
		/* clear the NPT permission setting in switching into scode */
		printf("[TV] change NPT permission to exit PAL!\n"); 
		vmx_nested_switch_regular(vcpu, whitelist[curr].scode_page, whitelist[curr].scode_size,
				(u32)whitelist[curr].pte_page, whitelist[curr].pte_size);
		scode_unexpose_arch(vcpu);

		/* switch back to regular stack */
		printf("[TV] switch from scode stack %#x back to regular stack %#x\n", (u32)linux_vmcb->guest_RSP, (u32)whitelist[curr].grsp);
		linux_vmcb->guest_RSP = whitelist[curr].grsp;
		linux_vmcb->guest_RSP += 4; 
		whitelist[curr].grsp = (u32)-1;

		/* enable interrupts */
		linux_vmcb->guest_RFLAGS |= EFLAGS_IF;

		printf("[TV] stack pointer before exiting scode is %#x\n",(u32)linux_vmcb->guest_RSP);
		return 0;
	}
	/* error in scode unmarshalling */
	return 1;
}

/*  EPT violation handler */
u32 vmx_scode_npf(VCPU * vcpu, u32 gpaddr, u64 errorcode)
{
	int index = -1;

	int * curr=&(scode_curr[vcpu->id]);
	struct _vmx_vmcsfields * linux_vmcb = (struct _vmx_vmcsfields *)(&(vcpu->vmcs));
	u64 gcr3 = (u64)linux_vmcb->guest_CR3;
	u32 rip = (u32)linux_vmcb->guest_RIP;

	printf("[TV] CPU(%02x): nested page fault!(rip %#x, gcr3 %#llx, gpaddr %#x, errorcode %llx)\n", vcpu->id, rip, gcr3, gpaddr, errorcode);

	index = scode_in_list(gcr3, rip);
	if ((*curr == -1) && (index >= 0)) {
		/* regular code to sensitive code */
		if ((errorcode & ((u32)EPT_ERRORCODE_EXEC)) && !(errorcode & ((u32)EPT_ERRORCODE_PRESENT))) {
			/* instruction read */
			*curr = index;
			if ((whitelist[*curr].entry_v == rip) && (whitelist[*curr].entry_p == gpaddr)) { 
				/* valid entry point, switch from regular code to sensitive code */
#ifdef __MP_VERSION__
				spin_lock(&(whitelist[*curr].pal_running_lock));
				whitelist[*curr].pal_running_vcpu_id=vcpu->id;
				printf("got pal_running lock!\n");
#endif
				if (vmx_scode_switch_scode(vcpu)) {
					printf("[TV] error in switch to scode!\n");
#ifdef __MP_VERSION__
					spin_unlock(&(whitelist[*curr].pal_running_lock));
					whitelist[*curr].pal_running_vcpu_id=-1;
					printf("released pal_running lock!\n");
#endif

					goto npf_error;
				}
			} else {
				printf("[TV] SECURITY: invalid scode entry point!\n");
				goto npf_error;
			}
		} else {
			printf("[TV] SECURITY: invalid access to scode mem region from regular code!\n");
			goto npf_error;
		}
	} else if ((*curr >=0) && (index < 0)) {
		/* sensitive code to regular code */
		if ((errorcode & ((u32)EPT_ERRORCODE_EXEC)) && !(errorcode & ((u32)EPT_ERRORCODE_PRESENT))) {
			/* instruction read */
			if (whitelist[*curr].return_v == rip) { 
				/* valid return point, switch from sensitive code to regular code */
				/* XXX FIXME: now return ponit is extracted from regular code stack, only support one scode function call */
				if (vmx_scode_switch_regular(vcpu)) {
					printf("[TV] error in switch to regular code!\n");
#ifdef __MP_VERSION__
					spin_unlock(&(whitelist[*curr].pal_running_lock));
					whitelist[*curr].pal_running_vcpu_id=-1;
					printf("released pal_running lock!\n");
#endif
					goto npf_error;
				}
#ifdef __MP_VERSION__
				spin_unlock(&(whitelist[*curr].pal_running_lock));
				whitelist[*curr].pal_running_vcpu_id=-1;
				printf("released pal_running lock!\n");
#endif
				*curr = -1;
			} else {
				printf("[TV] SECURITY: invalid scode return point!\n");
				goto npf_error;
			}
		} else { 
			/* data read or data write */
			printf("[TV] SECURITY: invalid access to regular mem region from scode!\n");
			goto npf_error;
		} 
	} else if ((*curr >=0) && (index >= 0)) {
		/* sensitive code to sensitive code */
		if (*curr == index) 
			printf("[TV] SECURITY: incorrect scode EPT configuration!\n");
		else
			printf("[TV] SECURITY: invalid access to scode mem region from other scodes!\n"); 
#ifdef __MP_VERSION__
		spin_unlock(&(whitelist[*curr].pal_running_lock));
		whitelist[*curr].pal_running_vcpu_id=-1;
		printf("released pal_running lock!\n");
#endif
		goto npf_error;	
	} else {
		/* regular code to regular code */
		printf("[TV] incorrect regular code EPT configuration!\n"); 
		goto npf_error;
	}

    //linux_vmcb->eventinj.bytes = (u64)0;
	return 0;

npf_error:
#if 0
	/* errors, inject segfault to guest */
	linux_vmcb->eventinj.bytes=0;
	linux_vmcb->eventinj.fields.vector=0xd;
	linux_vmcb->eventinj.fields.vector=EVENTTYPE_EXCEPTION;
	linux_vmcb->eventinj.fields.v=0x1;
#endif
	*curr = -1;
	return 1;
}


u32 scode_seal(VCPU * vcpu, u32 input_addr, u32 input_len, u32 pcrAtRelease_addr, u32 output_addr, u32 output_len_addr)
{
	unsigned int i;
	int index;
	u32 outlen;
	u8 pcr[TPM_PCR_SIZE];
	u8 indata[MAX_SEALDATA_LEN];  
	u8 output[MAX_SEALDATA_LEN]; 

	printf("\n[TV] ********** uTPM seal **********\n");
	printf("[TV] input addr: %x, len %d, pcr addr: %x, output addr: %x!\n", input_addr, input_len, pcrAtRelease_addr, output_addr);
	/* check input data length */
	/* include seal data header and possible AES encryption padding */
	if (input_len > (MAX_SEALDATA_LEN-SEALDATA_HEADER_LEN - 16) ) {
		printf("[TV] Seal ERROR: input data length is too large, lenth %#x\n", input_len);
		return 1;
	}

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		printf("[TV] Seal ERROR: no PAL is running!\n");
		return 1;
	}

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* copy input data to host */
	copy_from_guest(vcpu, indata, input_addr, input_len);

#if 0
	printf("[TV] input len = %d!\n", input_len);
	printf("[TV] input data is:");
	for(i=0;i<input_len;i++) {
		printf("%x ", indata[i]);
	}
	printf("[TV] \n");
#endif

	if (pcrAtRelease_addr != 0) {
		/* seal data to other PAL */
		/* copy pcr value at release to host */
		copy_from_guest(vcpu, pcr, pcrAtRelease_addr, TPM_PCR_SIZE);
	} else {
		/* seal data to our own */
		/* use current PAL's PCR value */
		printf("[TV] get pcr from current PAL's softTPM!\n");
		vmemcpy(pcr, whitelist[scode_curr[vcpu->id]].pcr, TPM_PCR_SIZE);
	}

#if 1
	printf("[TV] pcr value is:");
	for(i=0;i<TPM_PCR_SIZE;i++) {
		printf("%x ", pcr[i]);
	}
	printf("\n");
#endif

	/* seal */
	stpm_seal(pcr, indata, input_len, output, &outlen, hmackey, aeskey);

#if 1
	printf("[TV] sealed data len = %d!\n", outlen);
	printf("[TV] sealed data is: ");
	for(i=0;i<outlen;i++) {
		printf("%x ", output[i]);
	}
	printf("\n");
#endif

	/* check output data length */
	if (outlen > MAX_SEALDATA_LEN) {
		printf("[TV] Seal ERROR: output data length is too large, lenth %#x\n", outlen);
		return 1;
	}

	/*copy output to guest */
	copy_to_guest(vcpu, output_addr, output, outlen);

	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(vcpu, output_len_addr, outlen);

	return 0;
}

u32 scode_unseal(VCPU * vcpu, u32 input_addr, u32 input_len, u32 output_addr, u32 output_len_addr)
{
	unsigned int i;
	u8 indata[MAX_SEALDATA_LEN]; 
	u8 outdata[MAX_SEALDATA_LEN];
	u32 outlen;
	u32 ret;
	int index;

	printf("\n[TV] ********** uTPM unseal **********\n");
	printf("[TV] input addr: %x, len %d, output addr: %x!\n", input_addr, input_len, output_addr);
	/* check input data length */
	if (input_len > MAX_SEALDATA_LEN) {
		printf("[TV] Unseal ERROR: input data length is too large, lenth %#x\n", input_len);
		return 1;
	}

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		printf("[TV] Seal ERROR: no PAL is running!\n");
		return 1;
	}

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* copy input data from guest */
	copy_from_guest(vcpu, indata, input_addr, input_len);

#if 0
	printf("[TV] input len = %d!\n", input_len);
	printf("[TV] input data is:");
	for(i=0;i<input_len;i++) {
		printf("%x ", indata[i]);
	}
	printf("[TV] \n");
#endif

	/* unseal */
	if ((ret = stpm_unseal(whitelist[scode_curr[vcpu->id]].pcr, indata, input_len, outdata, &outlen, hmackey, aeskey))) {
		printf("[TV] Unseal ERROR: stpm_unseal fail!\n");
		return 1;
	}

#if 1
	printf("[TV] unsealed data len = %d!\n", outlen);
	printf("[TV] unsealed data is: ");
	for(i=0;i<outlen;i++) {
		printf("%x ", outdata[i]);
	}
	printf("\n");
#endif

	/* check output data length */
	if (outlen > MAX_SEALDATA_LEN ) {
		printf("[TV] Seal ERROR: output data length is too large, lenth %#x\n", outlen);
		return 1;
	}

	/* copy output to guest */
	copy_to_guest(vcpu, output_addr, outdata, outlen);

	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(vcpu, output_len_addr, outlen);
	return 0;
}

u32 scode_quote(VCPU * vcpu, u32 nonce_addr, u32 tpmsel_addr, u32 out_addr, u32 out_len_addr)
{
	u8 outdata[TPM_QUOTE_SIZE];
	u8 nonce[TPM_NONCE_SIZE];
	u8 tpmsel[MAX_PCR_SEL_SIZE];
	u32 outlen, ret;
	u32 i, num;
	int index;
	u32 tpmsel_len;

	printf("\n[TV] ********** uTPM Quote **********\n");
	printf("[TV] nonce addr: %x, tpmsel addr: %x, output addr %x, outlen addr: %x!\n", nonce_addr, tpmsel_addr, out_addr, out_len_addr);
	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		printf("[TV] Quote ERROR: no PAL is running!\n");
		return 1;
	}	

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* get TPM PCR selection from guest */
	num = get_32bit_aligned_value_from_guest(vcpu, tpmsel_addr);
	if (num > MAX_PCR_SEL_NUM) {
		printf("[TV] Quote ERROR: select too many PCR!\n");
		return 1;
	}
	tpmsel_len = 4+4*num;
	printf("[TV] %d pcrs are selected!\n", num);

	copy_from_guest(vcpu, tpmsel, tpmsel_addr, tpmsel_len);
	for( i=0 ; i< num ; i++ )  {
		if (*(((u32 *)(tpmsel+4))+i) >= TPM_PCR_NUM) {
			printf("[TV] Quote ERROR: bad format of TPM PCR num!\n");
			return 1;
		}
	}

	/* get external nonce from guest */
	copy_from_guest(vcpu, nonce, nonce_addr, TPM_NONCE_SIZE);

#if 1
	printf("[TV] external nonce is: ");
	for(i=0;i<TPM_NONCE_SIZE;i++) {
		printf("%x ", nonce[i]);
	}
	printf("\n");
#endif

	if ((ret = stpm_quote(nonce, outdata, &outlen, whitelist[scode_curr[vcpu->id]].pcr, tpmsel, tpmsel_len, (u8 *)(&g_rsa))) != 0) {
		printf("[TV] quote ERROR: stpm_quote fail!\n");
		return 1;
	}

#if 0
	printf("[TV] quote data len = %d!\n", outlen);
	printf("[TV] quote data is: ");
	for(i=0;i<outlen;i++) {
		printf("%x ", outdata[i]);
	}
	printf("\n");
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



#if 0
/* functions for software tpm, by yanlinl at March 4, 2009 */

u32 scode_pcrread(u64 gcr3, u32 gvaddr, u32 num)
{
	int i;
	int index;
	u8 pcr[TPM_PCR_SIZE];

	printf("[TV] PCRREAD cr3 %#x, gvaddr %#x\n", (u32)gcr3, gvaddr);
	index = scode_in_list(gcr3, (u32)linux_vmcb->rip); 

	if ((index >= 0) && (scode_curr >= 0))
	{
		scode_curr = index;
		stpm_pcrread(pcr, num);
		printf("[TV] PCRREAD %d pcr value\n", num);
		for ( i = 0; i < TPM_HASH_SIZE/4; i ++)
		{
			printf("[TV] PCRREAD %d %#x\n", num, ((u32 *)pcr)[i]);
		}

		copy_to_guest(gcr3, gvaddr, pcr, TPM_PCR_SIZE);
	} else 
	{
		printf("[TV] PCR Read ERROR: cr3 %#x, gvaddr %#x, index %#x\n", (u32)gcr3, gvaddr, index);
		return 1;
	}   

	return 0;
}


u32 scode_pcrextend(u64 gcr3, u32 gvaddr, u32 len, u32 num)
{
	int index;
	int data[2048]; /* the largest data size to extend pcr is 4k */
	u8 hash[TPM_HASH_SIZE];

	if (len > (2048))
	{
		printf("[TV] PCR extend ERROR: cr3 %#x, gvaddr %#x\n", (u32)gcr3, gvaddr);
		printf("[TV] PCR extend ERROR: data size is too large\n");
		return 1;
	}

	/* get scode_curr */
	printf("[TV] PCR extend cr3 %#x, gvaddr %#x, len %d, pcr num %d\n", (u32)gcr3, gvaddr, len, num);
	index = scode_in_list(gcr3, (u32)linux_vmcb->rip);

	if ((index >= 0) && (scode_curr >= 0))
	{
		scode_curr = index;
	}
	else
	{
		printf("[TV] PCR extend ERROR: cr3 %#x, gvaddr %#x\n", (u32)gcr3, gvaddr);
		printf("[TV] PCR extend ERROR: scode_curr error\n");
		return 1;
	}

	/* get data from guest */
	copy_from_guest((unsigned char *)data, gcr3, gvaddr, len);
	printf("[TV] copy data from guest");
	/* hash input data */
	sha1_csum((unsigned char*)data, len, hash);
	printf("[TV] PCR %d EXTEND, hash done!!", num);
	/* extend pcr */
	stpm_extend(hash, num);
	printf("[TV] PCR %d extend finish\n", num); 
	return 0;
}



u32 scode_rand(u64 gcr3, u32 buffer_addr, u32 numbytes_requested, u32 numbytes_addr)
{
	u32 ret;
	int index;
	u8 buffer[STPM_RANDOM_BUFFER_SIZE + STPM_RANDOM_BUFFER_SIZE]; // buffer to save the random data
	u32 numbytes;

	/* get scode_curr */
	printf("[TV] PCR rand cr3 %#x, buffaddr %#x, numbytes %d\n", (u32)gcr3, buffer_addr, numbytes_requested);
	index = scode_in_list(gcr3, (u32)linux_vmcb->rip);

	if ((index >= 0) && (scode_curr >= 0))
	{
		scode_curr = index;
	}
	else
	{
		printf("[TV] GEN RANDOM ERROR: cr3 %#x, buff_addr %#x\n", (u32)gcr3, buffer_addr);
		return 1;
	}

	// get the byte number requested
	numbytes = numbytes_requested;
	ret = stpm_rand(buffer, numbytes);
	if (ret != numbytes)
	{
		printf("[TV] utmp generate randon %d bytes, requested %d bytes\n", ret, numbytes);
	}
	numbytes = ret;

	printf("[TV] copy random data to guest\n");
	/* copy random data to guest */
	copy_to_guest(gcr3, buffer_addr, buffer, numbytes);
	printf("[TV] copy random data length to guest, %d bytes\n", numbytes);
	/* copy data length to guest */
	put_32bit_aligned_value_to_guest(gcr3, numbytes_addr, numbytes);

	return 0;
}

/*
   u32 scode_getpubkey(u64 gcr3, u32 gvaddr)
   {
   int i;
   int index;
   u8 aikdata[TPM_RSA_KEY_LEN];

   printf("[TV] GetPubKey cr3 %#x, gvaddr %#x\n", (u32)gcr3, gvaddr);
   index = scode_in_list(gcr3, (u32)linux_vmcb->rip);

   if ((index >= 0) && (scode_curr >= 0))
   {
   scode_curr = index;

   for ( i = 0; i < TPM_RSA_KEY_LEN; i ++)
   {
   aikdata[i] = ((u8*)g_rsa.N.p)[i];
   }
   copy_to_guest(gcr3, gvaddr, aikdata, TPM_RSA_KEY_LEN);
   }else
   {
   printf("[TV] GetPubKey ERROR: cr3 %#x, gvaddr %#x, index %#x\n", (u32)gcr3, gvaddr, index);
   return 1;
   }

   return 0;
   }
   */

#endif

/* SVM related SCODE routines */


/* ************************************
 * set up scode pages permission (SVM)
 * R 	-- 	read-only
 * R/W	--	read, write
 * NU	--	guest system cannot access
 * U	--	guest system can access
 *
 * on local CPU:
 * Section type		Permission
 * SENTRY(SCODE) 	R NU
 * STEXT			R U
 * SDATA 			RW NU
 * SPARAM			RW NU
 * SSTACK			RW NU
 *
 * on other CPU:
 * all sections		unpresent
 * **************************************/
u32 svm_scode_set_prot(VCPU *vcpu, u32 pte_page, u32 size)
{
	u32 i; 
	u32 pfn;
	pt_t pte_pages = (pt_t)pte_page;
	int type =0; 
#ifdef __MP_VERSION__
	u32 k;
	VCPU * tmpcpu;
#endif

	/* set up page permission in local CPU */
	printf("[TV] scode registration on local CPU %02x!\n", vcpu->id);
	for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
	{
		pfn = pte_pages[i] >> PAGE_SHIFT_4K;
		/* **********************************
		 * test page type
		 * type == 1 	SCODE(SENTRY)
		 * type == 2	STEXT
		 * type == 0	SDATA, SPARAM, SSTACK
		 * type == 3    all sections set to unpresent
		 * **********************************/
		if((pte_pages[i]) & 0x1)  {
			type = 1;
		} else if ((pte_pages[i]) & 0x4) {
			type = 2;
		} else {
			type = 0;
		}

		//printf("[TV] set_prot(pte %#x, size %#x): page No.%d, pfn %#x\n", pte_page, size, i+1, pfn);
		if (!test_page_scode_bitmap(pfn))
		{
			set_page_scode_bitmap(pfn);
			set_page_scode_bitmap_2M(pfn);

			/* XXX FIXME: temporary disable DEV setting here! */
		//	set_page_dev_prot(pfn);
			svm_nested_set_prot(vcpu, pte_pages[i], type);
		}else
		{
                  printf("[TV] Set scode page permission error! pfn %#x have already been registered!\n", pfn);
			break;
		}
	}

	/* exception detected above, need to recover the previous changes */
	if (i < (size >> PAGE_SHIFT_4K))
	{
		printf("[TV] recover scode page permission!\n");
		for (; i > 0; i --)
		{
			pfn = pte_pages[i - 1] >> PAGE_SHIFT_4K;

			/* XXX FIXME: temporary disable DEV setting here! */
			//clear_page_dev_prot(pfn);
			svm_nested_clear_prot(vcpu, pte_pages[i-1]);

			clear_page_scode_bitmap(pfn);
			//if (clear_page_scode_bitmap_2M(pfn) == 0)
			//	svm_nested_promote(vcpu, pfn);
		}
		return 1;
	}

#ifdef __MP_VERSION__
	/* not local CPU, set all mem sections unpresent */
	for( k=0 ; k<g_midtable_numentries ; k++ )  {
		tmpcpu = (VCPU *)(g_midtable[k].vcpu_vaddr_ptr);
		if (tmpcpu->id != vcpu->id) {
			printf("[TV] scode registration on CPU %02x!\n", tmpcpu->id);
			for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
			{
				pfn = pte_pages[i] >> PAGE_SHIFT_4K;
				/* XXX FIXME: temporary disable DEV setting here! */
				//	set_page_dev_prot(pfn);
				svm_nested_set_prot(tmpcpu, pte_pages[i], 3);
			}
		}
	}
#endif

	return 0;
}

void svm_scode_clear_prot(VCPU * vcpu, u32 pte_page, u32 size)
{
	u32 i; 
	u32 pfn;
	pt_t pte_pages = (pt_t)pte_page;
#ifdef __MP_VERSION__
	u32 k;
	VCPU * tmpcpu;
#endif

	/* set up page permission in local CPU */
	printf("[TV] scode unreg on local CPU %02x!\n", vcpu->id);
	for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
	{
		pfn = pte_pages[i] >> PAGE_SHIFT_4K;
		if (test_page_scode_bitmap(pfn))
		{
			printf("[TV] clear_prot(pte %#x, size %#x): page No.%d, pfn %#x\n", pte_page, size, i+1, pfn);
			/* XXX FIXME: temporary disable DEV setting here! */
			//clear_page_dev_prot(pfn);
			svm_nested_clear_prot(vcpu, pte_pages[i]);

			clear_page_scode_bitmap(pfn);
		//	if (clear_page_scode_bitmap_2M(pfn) == 0)
		//		svm_nested_promote(vcpu, pfn);
		}
	}

#ifdef __MP_VERSION__
	/* not local CPU, set all mem sections unpresent */
	for( k=0 ; k<g_midtable_numentries ; k++ )  {
		tmpcpu = (VCPU *)(g_midtable[k].vcpu_vaddr_ptr);
		if (tmpcpu->id != vcpu->id) {
			printf("[TV] scode unreg on CPU %02x!\n", tmpcpu->id);
			for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
			{
				pfn = pte_pages[i] >> PAGE_SHIFT_4K;
				/* XXX FIXME: temporary disable DEV setting here! */
				//	set_page_dev_prot(pfn);
				svm_nested_clear_prot(tmpcpu, pte_pages[i]);
			}
		}
	}
#endif

}

u32 svm_scode_switch_scode(VCPU * vcpu)
{
	u32 addr;
	int curr=scode_curr[vcpu->id];
	struct vmcb_struct * linux_vmcb = (struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr);

	printf("\n[TV] ************************************\n");
	printf("[TV] ********* switch to scode **********\n");
	printf("[TV] ************************************\n");

	/* save the guest stack pointer and set new stack pointer to scode stack */
	printf("[TV] saved guest regular stack %#x, switch to sensitive code stack %#x\n", (u32)linux_vmcb->rsp, whitelist[curr].gssp);
	whitelist[curr].grsp = (u32)linux_vmcb->rsp; 
	linux_vmcb->rsp = whitelist[curr].gssp; 

	/* input parameter marshalling */
	if (scode_marshall(vcpu)){
		/* error in parameter marshalling */
		/* restore regular code stack */
		linux_vmcb->rsp = whitelist[curr].grsp; 
		whitelist[curr].grsp = (u32)-1; 
		return 1;
	}

	/* find all PTE pages related to access scode and GDT */
	scode_expose_arch(vcpu);

	/* change NPT permission for all PTE pages and scode pages */
	printf("[TV] change NPT permission to run PAL!\n"); 
	svm_nested_switch_scode(vcpu, whitelist[curr].scode_page, whitelist[curr].scode_size,
			(u32)whitelist[curr].pte_page, whitelist[curr].pte_size);
		
	/* disable interrupts */
	linux_vmcb->rflags &= ~EFLAGS_IF;

	/* set the sensitive code to run in ring 3 */
	linux_vmcb->cpl = 3;

	/* write the return address to scode stack */
	addr = get_32bit_aligned_value_from_guest(vcpu, (u32)whitelist[curr].grsp);
	linux_vmcb->rsp -= 4;
	put_32bit_aligned_value_to_guest(vcpu, (u32)(linux_vmcb->rsp), addr);
	/* store the return address in whitelist structure */
	whitelist[curr].return_v = addr;
	printf("[TV] scode return vaddr is %#x\n", whitelist[curr].return_v);

	printf("[TV] host stack pointer before running scode is %#x\n",(u32)linux_vmcb->rsp);
	return 0;
}

u32 svm_scode_switch_regular(VCPU * vcpu)
{
	int curr=scode_curr[vcpu->id];
	struct vmcb_struct * linux_vmcb = (struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr);

	printf("\n[TV] ************************************\n");
	printf("[TV] ***** switch to regular code  ******\n");
	printf("[TV] ************************************\n");

	/* marshalling parameters back to regular code */
	if (!scode_unmarshall(vcpu)){
		/* clear the NPT permission setting in switching into scode */
		printf("[TV] change NPT permission to exit PAL!\n"); 
		svm_nested_switch_regular(vcpu, whitelist[curr].scode_page, whitelist[curr].scode_size,
				(u32)whitelist[curr].pte_page, whitelist[curr].pte_size);
		scode_unexpose_arch(vcpu);

		/* switch back to regular stack */
		printf("[TV] switch from scode stack %#x back to regular stack %#x\n", (u32)linux_vmcb->rsp, (u32)whitelist[curr].grsp);
		linux_vmcb->rsp = whitelist[curr].grsp;
		linux_vmcb->rsp += 4; 
		whitelist[curr].grsp = (u32)-1;

		/* enable interrupts */
		linux_vmcb->rflags |= EFLAGS_IF;

		printf("[TV] stack pointer before exiting scode is %#x\n",(u32)linux_vmcb->rsp);
		return 0;
	}
	/* error in scode unmarshalling */
	return 1;
}

u32 svm_scode_npf(VCPU * vcpu, u32 gpaddr, u64 errorcode)
{
	int index = -1;

	int * curr=&(scode_curr[vcpu->id]);
	struct vmcb_struct * linux_vmcb = (struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr);
	u64 gcr3 = (u64)linux_vmcb->cr3;
	u32 rip = (u32)linux_vmcb->rip;

	printf("[TV] CPU(%02x): nested page fault!(rip %#x, gcr3 %#llx, gpaddr %#x, errorcode %#llx)\n", vcpu->id, rip, gcr3, gpaddr, errorcode);

	if (!(errorcode & ((u64)PF_ERRORCODE_PRESENT))) {
		/* nested page not present */
		/* could be malicious apps or OS try to access memory range of trustvisor
		 * or program try to access PAL in different CPU (no the CPU where the registration is done) 
		 * */
		printf("[TV] SECURITY: invalid access to the mem region of Trustvisor or registered scode!\n"); 
		goto npf_error;
	}

	index = scode_in_list(gcr3, rip);
	if ((*curr == -1) && (index >= 0)) {
		/* regular code to sensitive code */
		if ((errorcode & ((u64)PF_ERRORCODE_INST))) {
			/* instruction read */
			*curr = index;
			if ((whitelist[*curr].entry_v == rip) && (whitelist[*curr].entry_p == gpaddr)) { 
#ifdef __MP_VERSION__
				spin_lock(&(whitelist[*curr].pal_running_lock));
				whitelist[*curr].pal_running_vcpu_id=vcpu->id;
				printf("got pal_running lock!\n");
#endif

				/* valid entry point, switch from regular code to sensitive code */
				if (svm_scode_switch_scode(vcpu)) {
					printf("[TV] error in switch to scode!\n");
#ifdef __MP_VERSION__
					spin_unlock(&(whitelist[*curr].pal_running_lock));
					whitelist[*curr].pal_running_vcpu_id=-1;
					printf("released pal_running lock!\n");
#endif
					goto npf_error;
				}
			} else {
				printf("[TV] SECURITY: invalid scode entry point!\n");
				goto npf_error;
			}
		} else {
			printf("[TV] SECURITY: invalid access to scode mem region from regular code!\n");
			goto npf_error;
		}
	} else if ((*curr >=0) && (index < 0)) {
		/* sensitive code to regular code */
		if ((errorcode & ((u64)PF_ERRORCODE_INST)) || ((errorcode & ((u64)PF_ERRORCODE_TABLEWALK)) || (errorcode & ((u64)PF_ERRORCODE_FINALWALK)))) {
			/* instruction read or table walk */
			if (whitelist[*curr].return_v == rip) { 
				/* valid return point, switch from sensitive code to regular code */
				/* XXX FIXME: now return ponit is extracted from regular code stack, only support one scode function call */
				if (svm_scode_switch_regular(vcpu)) {
					printf("[TV] error in switch to regular code!\n");
#ifdef __MP_VERSION__
					spin_unlock(&(whitelist[*curr].pal_running_lock));
					whitelist[*curr].pal_running_vcpu_id=-1;
					printf("released pal_running lock!\n");
#endif

					goto npf_error;
				}
#ifdef __MP_VERSION__
				spin_unlock(&(whitelist[*curr].pal_running_lock));
				whitelist[*curr].pal_running_vcpu_id=-1;
				printf("released pal_running lock!\n");
#endif
				*curr = -1;
			} else {
				printf("[TV] SECURITY: invalid scode return point!\n");
				goto npf_error;
			}
		} else { 
			/* data read or data write */
			printf("[TV] SECURITY: invalid access to regular mem region from scoe!\n");
			goto npf_error;
		} 
	} else if ((*curr >=0) && (index >= 0)) {
		/* sensitive code to sensitive code */
		if (*curr == index) 
			printf("[TV] SECURITY: incorrect scode NPT configuration!\n");
		else
			printf("[TV] SECURITY: invalid access to scode mem region from other scodes!\n"); 
#ifdef __MP_VERSION__
		spin_unlock(&(whitelist[*curr].pal_running_lock));
		whitelist[*curr].pal_running_vcpu_id=-1;
		printf("released pal_running lock!\n");
#endif
		goto npf_error;	
	} else {
		/* regular code to regular code */
		printf("[TV] incorrect regular code NPT configuration!\n"); 
		goto npf_error;
	}

    /* no errors, pseodu page fault canceled by nested paging */
    linux_vmcb->eventinj.bytes = (u64)0;
	return 0;

npf_error:
	/* errors, inject segfault to guest */
	linux_vmcb->eventinj.bytes=0;
	linux_vmcb->eventinj.fields.vector=0xd;
	linux_vmcb->eventinj.fields.vector=EVENTTYPE_EXCEPTION;
	linux_vmcb->eventinj.fields.v=0x1;
	*curr = -1;
	return 1;
}

