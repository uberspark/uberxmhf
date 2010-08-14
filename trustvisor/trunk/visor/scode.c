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
 * Written for TrustVisor by Ning Qu
 */

#include <types.h>
#include <error.h>
#include <multiboot.h>
#include <string.h>
#include <print.h>
#include <svm.h>
#include <sha1.h>
#include <processor.h>
#include <visor.h>
#include <paging.h>
#include <heap.h>
#include <io.h>
#include <pci.h>
#include <dev.h>
#include <scode.h>
#include <params.h>
#include <tpm_sw.h>
#include <tpm.h>
#include <arc4.h>  // for rand generator, by yanlinl at Jul 28, 2009
#include <random.h>
//#include <rsa.h>
/* whitelist of all approved sensitive code regions */
extern u32 scode_whitelist[];
/* bitmap of all physical page numer containing sensitive code */
extern u8 scode_pfn_bitmap[];
/* bitmap helps to maintain the physical pages of sensitive code
 * in one 2M physical page range
 */
extern u16 scode_pfn_bitmap_2M[];

extern u8 sealAesKey[16];
extern u8 sealHmacKey[20];

int scode_curr = -1;

whitelist_entry_t *whitelist;
u32 whitelist_size, whitelist_max, hashlist_size;
rsa_context g_rsa;

/* preloaded hash values for the scodes */
hashlist_entry_t hashlist[] = {
	//#include "hashlist.c"
};

u32 scode_verify(u32 pte_page, u32 size);
int scode_in_list(u64 gcr3, u32 gvaddr);

/* initialize all the scode related variables and buffers */
void init_scode(void)
{
	memset(scode_whitelist, 0, WHITELIST_SIZE << PAGE_SHIFT_4K); 
	whitelist = (whitelist_entry_t *)scode_whitelist;
	whitelist_size = 0;
	whitelist_max = (WHITELIST_SIZE << PAGE_SHIFT_4K) / sizeof(whitelist_entry_t);

	hashlist_size = sizeof(hashlist) / sizeof(hashlist_entry_t);

	memset(scode_pfn_bitmap, 0, MODPFN_SIZE << PAGE_SHIFT_4K);
	memset(scode_pfn_bitmap_2M, 0, PAGE_SIZE_4K);
	scode_curr = -1;
}

static inline u32 scode_set_prot(u32 pte_page, u32 size)
{
	u32 i; 
	u32 pfn;
	pt_t pte_pages = (pt_t)pte_page;
	int type =0; 

	for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
	{
		pfn = pte_pages[i] >> PAGE_SHIFT_4K;
		/* **********************************
		 * test page type
		 * type == 1 	SCODE(SENTRY)
		 * type == 2	STEXT
		 * type == 0	SDATA, SPARAM, SSTACK
		 * **********************************/
		if((pte_pages[i]) & 0x1)  {
			type = 1;
		} else if ((pte_pages[i]) & 0x4) {
			type = 2;
		} else {
			type = 0;
		}

		DEBUG printf("DEBUG: set_prot(pte %#x, size %#x): page No.%d, pfn %#x\n", pte_page, size, i+1, pfn);
		if (!test_page_scode_bitmap(pfn))
		{
			set_page_scode_bitmap(pfn);
			set_page_scode_bitmap_2M(pfn);

			set_page_dev_prot(pfn);
			nested_set_prot(pfn, type);
		}else
		{
			/* RELATED BIT IN BITMAP HAS BEEN SET   --ZONGWEI  DEC 13 2009 */
			DEBUG printf("DEBUG: exception detected\n");
			break;
		}
	}

	//DEBUG printf("DEBUG: set_prot pte %#x, size %#x, i %d\n", pte_page, size, i);
	/* exception detected above, need to recover the previous changes */
	if (i < (size >> PAGE_SHIFT_4K))
	{
		DEBUG printf("DEBUG: recover the protection\n");
		for (; i > 0; i --)
		{
			pfn = pte_pages[i - 1] >> PAGE_SHIFT_4K;

			clear_page_dev_prot(pfn);
			nested_clear_prot(pfn);

			clear_page_scode_bitmap(pfn);
			if (clear_page_scode_bitmap_2M(pfn) == 0)
				nested_promote(pfn);
		}
		return 1;
	}

	return 0;
}

static inline void scode_clear_prot(u32 pte_page, u32 size)
{
	u32 i; 
	u32 pfn;
	pt_t pte_pages = (pt_t)pte_page;

	for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
	{
		pfn = pte_pages[i] >> PAGE_SHIFT_4K;
		if (test_page_scode_bitmap(pfn))
		{
			DEBUG printf("DEBUG: clear_prot pte %#x, size %#x, pfn %#x\n", pte_page, size, pfn);
			clear_page_dev_prot(pfn);
			nested_clear_prot(pfn);

			clear_page_scode_bitmap(pfn);
			if (clear_page_scode_bitmap_2M(pfn) == 0)
				nested_promote(pfn);

		}
	}
}

void pm_parse_params_info(struct scode_params_info* pm_info, u64 cr3, u32 pm_addr)
{
	u32 i, num;
	u32 addr;
	addr = pm_addr;
	/* get parameter number */
	pm_info->params_num = get_32bit_aligned_value_from_guest(cr3, addr);
	addr += 4;

	/* param type and size */
	num = pm_info->params_num;
	DEBUG printf("scode.c DEBUG: pm_addr %#x, pm_parse num is %d\n", pm_addr, num);
	if (num > MAX_PARAMS_NUM) {
		FORCE_CRASH();
	}
	for (i = 0; i < num; i++)
	{
		pm_info->pm_str[i].type = get_32bit_aligned_value_from_guest(cr3, addr);
		DEBUG printf("scode.c DEBUG: pm_parse %d type is %d\n", i, pm_info->pm_str[i].type);
		addr += 4;
		pm_info->pm_str[i].size = get_32bit_aligned_value_from_guest(cr3, addr);
		DEBUG printf("scode.c DEBUG: pm_parse %d size is %d\n",i,pm_info->pm_str[i].size);

		addr += 4;
	}
}



/* parse scode sections info (scode registration input) */
int scode_parse_sectios_info(struct scode_sections_info * scode_info, u64 cr3, u32 ps_addr)
{
	int i;
	u32 addr = ps_addr;
	/* get parameter number */
	scode_info->section_num = get_32bit_aligned_value_from_guest(cr3, addr);
	DEBUG printf("DEBUG: scode_info addr %x, section num is %d\n", (int)(scode_info), scode_info->section_num);
	addr += 4;

	if( scode_info->section_num > MAX_SECTION_NUM )  {
		DEBUG printf("DEBUG: the num of scode sections exceeds limit!\n");
		return 1;
	}

	/* parse section type, start address and size */
	for (i = 0; i < scode_info->section_num; i++) {
		scode_info->ps_str[i].type = get_32bit_aligned_value_from_guest(cr3, addr);
		scode_info->ps_str[i].start_addr = get_32bit_aligned_value_from_guest(cr3, addr+4);
		scode_info->ps_str[i].page_num = get_32bit_aligned_value_from_guest(cr3, addr+8);
		DEBUG printf("DEBUG: section %d type %d addr %#x size %d\n",i+1, scode_info->ps_str[i].type,scode_info->ps_str[i].start_addr, scode_info->ps_str[i].page_num);
		addr += 12;
	}
	return 0;
}


/* register scode in whitelist */
u32 scode_register(u64 gcr3, u32 scode_info, u32 gssp, u32 scode_pm, u32 gventry) 
{

	u32 i, j;
	whitelist_entry_t whitelist_new;
	u32 ret;
	u32 inum;
	struct scode_sections_struct * ginfo; 

	DEBUG printf("\nDEBUG: ************************************\n");
	DEBUG printf("DEBUG: ********** scode register **********\n");
	DEBUG printf("DEBUG: ************************************\n");
	if (whitelist_size == whitelist_max)
	{
		/* what kind of crazy system are u using? more than 512 scodes? */
		printf("FATAL ERROR: too many registered scode, the limitation is %d\n", whitelist_max);
		return 1;
	}

	/* add sensitive code */
	DEBUG printf("DEBUG: add to whitelist, gcr3 %#llx, scode_info %#x, gssp %#x, gventry %#x\n", gcr3, scode_info, gssp, gventry);

	whitelist_new.gcr3 = gcr3;
	whitelist_new.grsp = (u32)-1;
	whitelist_new.gssp = gssp;

	/* set scode entry point */
	whitelist_new.entry_v = gventry;
	whitelist_new.entry_p = guest_pt_walker_internal(gcr3, gventry, NULL, NULL, NULL); 
	DEBUG printf("DEBUG: entry point vaddr is %#x, paddr is %#x\n", whitelist_new.entry_v, whitelist_new.entry_p);

	pm_parse_params_info(&(whitelist_new.params_info), gcr3 , scode_pm);
	whitelist_new.gpm_num = whitelist_new.params_info.params_num;
	DEBUG printf("DEBUG: parse param info at %#x, param num is %d!\n", scode_pm, whitelist_new.gpm_num);
	whitelist_new.gpmp = scode_pm; /* no actual use now */
	memset(whitelist_new.pcr, 0, TPM_PCR_SIZE*TPM_PCR_NUM); /* set pcr to zero, by yanlin at March 3, 2009*/

	/* Initialize the rand generator for sscb
	 * todo: (1) get random from hardware TPM
	 *       (2) arc4 setup 
	 * add by yanlinl at Jul 28, 2009
	 */
	DEBUG printf("DEBUG: initialize the rand generator\n");
	whitelist_new.refillNo = 0;
	DEBUG printf("DEBUG: get random from hardware TPM\n");
	arc4GetRandom(whitelist_new.randKey, STPM_RANDOM_BUFFER_SIZE);
	ret = STPM_RANDOM_BUFFER_SIZE;
	if(ret != STPM_RANDOM_BUFFER_SIZE)
	{
		printf("ERROR: get %d bytes random number from hardware TPM chip\n", ret);
	}

	/* FIXME: now each SSCB has exact same sTPM aeskey and hmackey
	 *        because we want to pass sealed data between SSCBs
     */
//	for (inum = 0; inum < 16; inum++)
//		whitelist_new.aeskey[inum] = random_byte();

//	for (inum = 0; inum < 20; inum++)
//		whitelist_new.hmackey[inum] = random_byte();

	for (inum = 0; inum < 16; inum++)
		whitelist_new.aeskey[inum] = (u8)(inum+1);

	for (inum = 0; inum < 20; inum++)
		whitelist_new.hmackey[inum] = (u8)(20-inum);

	DEBUG printf("DEBUG: setup arc4\n");

	/* initialization of rand generator end */

	/* ATTN: we should assign a ID for each registered sensitive code
	 * so we know what to verify each time
	 */
	whitelist_new.id = 0;

	/* save scode info struct into whitelist entry */ 
	if (scode_parse_sectios_info(&(whitelist_new.scode_info), gcr3, scode_info)) {
		printf("DEBUG: Registration Failed. Scode section info incorrect! \n");
		return 1;
	}

	/* register pages in each section */
	whitelist_new.scode_page = alloc_page();
	whitelist_new.scode_size = 0;
	for( i=0 ; i < (u32)(whitelist_new.scode_info.section_num) ; i++ )  {
		ginfo = &(whitelist_new.scode_info.ps_str[i]);
		if( whitelist_new.scode_size > (PAGE_SIZE_4K>>3) - ginfo->page_num )  {
			free_page(whitelist_new.scode_page);
			printf("DEBUG: Registration Failed. scode pages exceeds whitelist limit!\n"); 
			return 1;
		}
		if (guest_pt_copy(whitelist_new.scode_page+((whitelist_new.scode_size)<<3), gcr3, ginfo->start_addr, (ginfo->page_num)<<PAGE_SHIFT_4K, ginfo->type)) {
			free_page(whitelist_new.scode_page);
			printf("SECURITY: Registration Failed. Probably some page of sensitive code is not in memory yet\n");
			asm volatile("1: jmp 1b");
			return 1;
		}
		whitelist_new.scode_size += ginfo->page_num;
	}
	whitelist_new.scode_size = (whitelist_new.scode_size) << PAGE_SHIFT_4K;

	/* ************************************
	 * set up scode pages permission
	 * R 	-- 	read-only
	 * R/W	--	read, write
	 * NU	--	guest system cannot access
	 * U	--	guest system can access
	 *
	 * Section type		Permission
	 * SENTRY(SCODE) 	R NU
	 * STEXT			R U
	 * SDATA 			RW NU
	 * SPARAM			RW NU
	 * SSTACK			RW NU
	 * **************************************/
	if (scode_set_prot(whitelist_new.scode_page, whitelist_new.scode_size))
	{
		free_page(whitelist_new.scode_page);
		printf("SECURITY: Registration Failed. Probably some page has already been used by other sensitive code.\n");
		return 1;
	}

	/* sort whitelist entry by gcr3 */
	for (i = 0; (i < whitelist_size) && (gcr3 <= whitelist[i].gcr3); i ++);
	whitelist_size ++;
	for (j = whitelist_size; j > i; j --)
		memcpy(whitelist + j, whitelist + j - 1, sizeof(whitelist_entry_t));
	memcpy(whitelist + i, &whitelist_new, sizeof(whitelist_entry_t));

	/* hash the entire SSCB code, and then extend the hash value into uTPM PCR[0] */
	scode_curr = scode_in_list(whitelist_new.gcr3, (u32)whitelist_new.entry_v);
	if (scode_curr != -1)
	{
		if (scode_verify(whitelist[scode_curr].scode_page, whitelist[scode_curr].scode_size))
		{
			scode_clear_prot(whitelist[scode_curr].scode_page, whitelist[scode_curr].scode_size);
			free_page(whitelist[scode_curr].scode_page);
			printf("SECURITY: Registration Failed. sensitived code cannot be verified.\n");
			return 1;
		}
	}
	else
	{
		printf("SECURITY: Registration Failed. sensitive code cannot be located in the white list.");
		return 1;
	}

	scode_curr = -1;

	return 0; 
}

/* unregister scode in whitelist */
u32 scode_unregister(u64 gcr3, u32 gvaddr) 
{
	u32 i, j;
	DEBUG printf("\nDEBUG: ************************************\n");
	DEBUG printf("DEBUG: ********* scode unregister *********\n");
	DEBUG printf("DEBUG: ************************************\n");

	if (whitelist_size == 0)
	{
		/* what kind of crazy system are u using? more than 512 scodes? */
		printf("FATAL ERROR: no scode registered currently\n");
		return 1;
	}

	/* align the address and size */
	gvaddr = PAGE_ALIGN_4K(gvaddr);

	DEBUG printf("DEBUG: remove from whitelist gcr3 %#llx, gvaddr %#x\n", gcr3, gvaddr);

	for (i = 0; i < whitelist_size; i ++)
	{
		/* find scode with correct cr3 and entry point */
		if ((whitelist[i].gcr3 == gcr3) && (whitelist[i].entry_v == gvaddr))
			break;
	}

	if (i >= whitelist_size) 
	{
		DEBUG printf("DEBUG: gcr3 %#llx, gvaddr %#x\n", gcr3, gvaddr);
		printf("SECURITY: UnRegistration Failed. no matching sensitive code found\n");
		return 1;
	}

	/* if we find one to remove, we also need to clear the physcial page number
	 * vector 
	 */
	if (whitelist[i].scode_page)
	{
		scode_clear_prot(whitelist[i].scode_page, whitelist[i].scode_size);
		free_page(whitelist[i].scode_page);
		whitelist[i].scode_page = 0;
	}

	for (j = i; j < whitelist_size - 1; j ++)
		memcpy(whitelist + j, whitelist + j + 1, sizeof(whitelist_entry_t));

	whitelist_size --;

	return 0; 
}

u32 scode_verify(u32 pte_page, u32 size)
{
	u32 i; 
	u32 paddr;
	pt_t pte_pages = (pt_t)pte_page;
	sha1_context ctx;
	u8 sha1sum[SHA1_CHECKSUM_LEN];

	DEBUG printf("DEBUG: measure scode pte_page %#x, size %#x\n", pte_page, size);

	sha1_starts(&ctx);
	for (i = 0; i < (size >> PAGE_SHIFT_4K); i ++)
	{
		/* only measure SENTRY, STEXT, SDATA pages */
		paddr = PAGE_ALIGN_4K(pte_pages[i]);
		if((pte_pages[i] & 0x7)!=0)  {
			DEBUG printf("DEBUG: measure scode page %d paddr %#x\n", i+1, paddr);
			/* we assume one to one indentical mapping */
			sha1_update(&ctx, (u8 *)paddr, PAGE_SIZE_4K);
		} else {
			DEBUG printf("DEBUG: ignore scode page %d paddr %#x\n", i+1, paddr);
		}
	}
	sha1_finish(&ctx, sha1sum);

	DEBUG printf("DEBUG: SCODE measurement is:\n");
	DEBUG printf("DEBUG: ");
	for( i=0 ; i<SHA1_CHECKSUM_LEN ; i++ )  {
		DEBUG printf("%x ", sha1sum[i]);
	}
	DEBUG printf("\n");

	/* extend pcr */
	stpm_extend(sha1sum, 0);

	return 0;
}
#define EXPOSE_PAGE(x) expose_page(pte_page,x,scode_pfn_bitmap, &pte_count)
/* expose one page, helper function used by scode_expose_arch() */
void expose_page (u64 * page_list, u64 page, u8 * bitmap, u32 * count)
{
	u32 pfn = (u32)page >> PAGE_SHIFT_4K;
	if( !test_page_prot(pfn, bitmap) )  {
		page_list[(*count)]=page;
		*count = (*count)+1;
		/* set pfn bitmap so that we don't store duplicate page in page_list */
		set_page_prot(pfn, bitmap);
		/* set up DEV vector to prevent DMA attack */
		set_page_dev_prot(pfn);
		DEBUG printf("DEBUG: expose page %#llx \n", page);
		if( *count > (PAGE_SIZE_4K>>3)  )  {
			free_page((u32)page_list);
			printf("DEBUG: pte pages exceeds whitelist limit!\n"); 
			FORCE_CRASH();
		}
	}
}

/* find all PTE entry pages that is related to access scode and GDT */
void scode_expose_arch(void)
{
	u32 i;
	u32 j;
	u64 *pte_page;
	u32 pte_count = 0;
	u32 gpaddr = 0;
	struct scode_sections_struct * ginfo;
	u64 tmp_page[3];
	u32 tmp_count=0;
	pt_t sp = (pt_t)(whitelist[scode_curr].scode_page);
	u32 gcr3_flag=0;

	/* alloc memory for page table entry holder */
	whitelist[scode_curr].pte_page = alloc_page();
	pte_page = (u64 *)(whitelist[scode_curr].pte_page);

	/* get related page tables for scode */
	/* Here we walk guest page table, and find out all the pdp,pd,pt entry
	   that is necessary to translate gvaddr */
	DEBUG printf("DEBUG: expose SCODE related PTE pages\n");
	for( i=0 ; i < (u32)(whitelist[scode_curr].scode_info.section_num) ; i++ )  {
		ginfo = &(whitelist[scode_curr].scode_info.ps_str[i]);
		for( j=0 ; j<(u32)(ginfo->page_num); j++ )  {
			gpaddr = guest_pt_walker_internal(whitelist[scode_curr].gcr3, ginfo->start_addr+(j<<PAGE_SHIFT_4K), tmp_page, &tmp_page[1], &tmp_page[2]);

			/* check gvaddr to gpaddr mapping */
			if( gpaddr != (((u32)(*(sp+tmp_count+j)))&(~(0x7))))  {
				DEBUG printf("SECURITY: scode vaddr %x -> paddr %#llx mapping change has been DETECTED! gpaddr %x \n", ginfo->start_addr+(j<<PAGE_SHIFT_4K), *(sp+tmp_count+j), gpaddr);
				free_page(whitelist[scode_curr].pte_page);
				FORCE_CRASH();
			}

			/* write pdp, pd, pt entry into pte_page */
			if (linux_vmcb->cr4 & CR4_PAE) {
				/* PAE mode */
				if (gcr3_flag == 0) {
					gcr3_flag = 1;
					EXPOSE_PAGE(tmp_page[0]);
				}

				EXPOSE_PAGE(tmp_page[1]); 
				/* if _PAGE_PSE, page size is 2MB, no pd page 
				 * else, page size is 4KB, expose the pd page */
				if( (tmp_page[2] != (u64)(0xFFFFFFFF))) { 
					EXPOSE_PAGE(tmp_page[2]);
				}
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
	gpaddr = guest_pt_walker_internal(whitelist[scode_curr].gcr3, (u32)linux_vmcb->gdtr.base, NULL, &tmp_page[1], &tmp_page[2]);

	DEBUG printf("DEBUG: expose GDT related PTE pages\n");
	EXPOSE_PAGE(gpaddr);

	EXPOSE_PAGE(tmp_page[1]);
	if( (tmp_page[2] != (u64)(0xFFFFFFFF))) { 
		EXPOSE_PAGE(tmp_page[2]);
	}

	whitelist[scode_curr].pte_size = pte_count << PAGE_SHIFT_4K;
}

void scode_unexpose_arch(void)
{
	u32 i;
	u64 * page = (u64 *)(whitelist[scode_curr].pte_page);
	DEBUG printf("DEBUG: unexpose pte_page\n");
	/* clear page bitmap set in scode_expose_arch() */
	for (i=0; i<((whitelist[scode_curr].pte_size)>>PAGE_SHIFT_4K);i++) {
		clear_page_prot(((page[i])>>PAGE_SHIFT_4K),scode_pfn_bitmap);
		clear_page_dev_prot(((page[i])>>PAGE_SHIFT_4K));
	}

	/* free pte_page to save heap space,
	 * next expose will alloc a new pte_page */
	free_page(whitelist[scode_curr].pte_page);
	whitelist[scode_curr].pte_page = 0;
	whitelist[scode_curr].pte_size = 0;
}

void scode_marshall(void)
{
	u32 pm_addr, pm_addr_base, pm_value;  /*parameter stack base address*/
	u32 pm_num, pm_type, pm_size, pm_size_sum; /*save pm information*/
	u64 gcr3;
	u32 grsp;

	//struct scode_params_info pm_info; /*struct to save parameter information*/
	/* get guest address of scode parameter information*/
	//pm_info_addr = whitelist[scode_curr].gpmp; /*guest address for parameter information*/

	/*parse parameter information, saved in structure 'pm_info'*/
	gcr3 = (u64)linux_vmcb->cr3;
	//pm_parse_params_info(&pm_info, gcr3, pm_info_addr);

	//whitelist[scode_curr].gpm_num = pm_info.params_num;
	if(whitelist[scode_curr].gpm_num == 0)
	{
		DEBUG printf("DEBUG: params number is 0.Return!\n");
		return;
	}

	/* memory address for input parameter in sensitive code */
	pm_addr_base = PAGE_ALIGN_UP4K((u32)linux_vmcb->rsp - MAX_STACK_SIZE - MAX_INPUT_PARAMS_SIZE)+0x10;
	DEBUG printf("DEBUG: sensitive code input base address is %#x\n", pm_addr_base);

	/* address for parameters in guest stack */
	grsp = (u32)whitelist[scode_curr].grsp + 4; /*the stack pointer of parameters in guest stack*/

	/* save params number in input space*/
	pm_addr = pm_addr_base;
	put_32bit_aligned_value_to_guest(gcr3, (u32)pm_addr, whitelist[scode_curr].gpm_num);
	pm_addr += 4;
	pm_size_sum = 4; /*memory used in input pms section*/
	DEBUG printf("DEBUG: params number is %d\n", whitelist[scode_curr].gpm_num);

	if (whitelist[scode_curr].gpm_num > MAX_PARAMS_NUM)
	{
		printf("DEBUG: param num is too big! marshall params fail!\n");
		return;
	}

	/* begin to process the params*/
	for (pm_num = whitelist[scode_curr].gpm_num; pm_num > 0; pm_num--) /*the last parameter should be pushed in stack first*/
	{
		/* get param information*/
		pm_type = whitelist[scode_curr].params_info.pm_str[pm_num-1].type;
		pm_size = whitelist[scode_curr].params_info.pm_str[pm_num-1].size;

		/* get param value from guest stack */
		pm_value = pm_get_stack_param(gcr3, grsp, pm_num);

		pm_size_sum += 12;

		if (pm_size_sum > MAX_INPUT_PARAMS_SIZE)
		{
			printf("DEBUG: memory for input params is full! Marshall fail!\n");
			return;
		}

		/* save input params in input params memory for sensitive code */
		put_32bit_aligned_value_to_guest(gcr3, (u32)pm_addr, pm_type);
		pm_addr += 4;
		put_32bit_aligned_value_to_guest(gcr3, (u32)pm_addr, pm_size);
		pm_addr += 4;
		put_32bit_aligned_value_to_guest(gcr3, (u32)pm_addr, pm_value);
		pm_addr += 4;
		DEBUG printf("DEBUG: PM %d, type %d, size %d, value %#x\n", pm_num, pm_type, pm_size, pm_value);
		DEBUG printf("space left %#x bytes\n", (MAX_INPUT_PARAMS_SIZE - pm_size_sum));

		switch (pm_type)
		{
			case PM_TYPE_INTEGER: /*integer*/
				{        
					/* put the parameter value in sensitive code stack */
					linux_vmcb->rsp -= 4; 
					put_32bit_aligned_value_to_guest(gcr3, (u32)linux_vmcb->rsp, pm_value);
					DEBUG printf("DEBUG: param %d is integre, value %d\n",pm_num, pm_value);
					break;
				}
			case PM_TYPE_POINTER: /* pointer */
				{
					/*copy data from guest space to sensitive code*/
					pm_size_sum += 4*pm_size;
					if (pm_size_sum > MAX_INPUT_PARAMS_SIZE)
					{
						printf("DEBUG: No enough space to save input params data!marshall fail\n");
						return;
					}

					pm_copy_guest_to_guest(gcr3, pm_value, pm_addr, pm_size);

					/* put pointer address in sensitive code stack*/
					linux_vmcb->rsp -= 4;
					put_32bit_aligned_value_to_guest(gcr3, (u32)linux_vmcb->rsp, pm_addr);
					/*change pm address*/
					pm_addr += 4*pm_size;
					break;
				}
			default: /* other */
				printf("unknown parameter type. force crash\n");
				FORCE_CRASH();
		}

	}
}

void scode_unmarshall(void)
{
	u64 gcr3;
	u32 pm_addr_base, pm_addr;
	u32 i, pm_num, pm_type, pm_size, pm_value;
	u32 value;
	gcr3 = (u64)linux_vmcb->cr3;
	DEBUG printf("DEBUG: unmarshall\n");

	if (whitelist[scode_curr].gpm_num == 0)
	{
		DEBUG printf("DEBUG: unmarshall pm numbuer is 0. Return!\n");
		return;
	}

	/* memory address for input parameter in sensitive code */
	pm_addr_base = PAGE_ALIGN_UP4K((u32)whitelist[scode_curr].gssp - MAX_STACK_SIZE - MAX_INPUT_PARAMS_SIZE)+0x10;
	DEBUG printf("DEBUG: sensitive code input base address is %#x\n", pm_addr_base);

	/* get params number */
	pm_addr = pm_addr_base;
	pm_num = get_32bit_aligned_value_from_guest(gcr3, (u32)pm_addr);
	pm_addr += 4;
	DEBUG printf("DEBUG: params number is %d\n", pm_num);

	if (pm_num > MAX_PARAMS_NUM)
	{
		DEBUG printf("DEBUG: parameter number is incorrect\n");
		return;
	}
	/* begin to process the params*/
	for (i = 1; i <= pm_num; i++) /*the last parameter should be pushed in stack first*/
	{
		/* get param information*/
		pm_type =  get_32bit_aligned_value_from_guest(gcr3, (u32)pm_addr);
		pm_addr += 4;

		switch (pm_type)
		{
			case PM_TYPE_INTEGER: /*integer*/
				{
					/* put the parameter value in sensitive code stack */
					pm_addr += 8; /* skip now*/
					break;
				}
			case PM_TYPE_POINTER: /* pointer */
				{
					/*get size*/
					pm_size =  get_32bit_aligned_value_from_guest(gcr3, (u32)pm_addr);
					pm_addr += 4;

					/* get value -- pointer adddress in regular cod*/
					pm_value = get_32bit_aligned_value_from_guest(gcr3, (u32)pm_addr);
					pm_addr += 4;

					DEBUG printf("DEBUG: ummarshall pm %d, type %d, size %d, value %#x\n", i, pm_type, pm_size, pm_value);
					/*copy data from guest space to sensitive code*/
					pm_copy_guest_to_guest(gcr3, pm_addr, pm_value, pm_size);

					DEBUG
					{
						/* get the value of parameter*/
						value = get_32bit_aligned_value_from_guest(gcr3, (u32)pm_value);
						printf("DEBUG: the first 32 bit value of paramter is %#x\n", value);
					}
					/*change pm address*/
					pm_addr += 4*pm_size;
					break;
				}

			default: /* other */
				printf("unknown parameter %d type %d. force crash\n", i, pm_type);
				//FORCE_CRASH();
		} // end switch

	} //end for loop 
}

//todo: switch from regular code to sensitive code
void scode_switch_scode(void)
{
	u32 addr;
	DEBUG printf("DEBUG: ************************************\n");
	DEBUG printf("DEBUG: *********** switch r->s ************\n");
	DEBUG printf("DEBUG: ************************************\n");

	/* find all PTE pages related to access scode and GDT */
	scode_expose_arch();

	/* change NPT permission for all PTE pages and scode pages */
	nested_switch_scode(whitelist[scode_curr].scode_page, whitelist[scode_curr].scode_size,
			(u32)whitelist[scode_curr].pte_page, whitelist[scode_curr].pte_size);

	/* save the guest stack pointer and set new stack pointer to scode stack */
	DEBUG printf("DEBUG: saved guest regular stack %#x, switch to sensitive code stack %#x\n", (u32)linux_vmcb->rsp, whitelist[scode_curr].gssp);
	whitelist[scode_curr].grsp = (u32)linux_vmcb->rsp; 
	linux_vmcb->rsp = whitelist[scode_curr].gssp; 

	/* disable interrupts */
	linux_vmcb->rflags &= ~EFLAGS_IF;

	/* set the sensitive code to run in ring 3 */
	linux_vmcb->cpl = 3;

	/* input parameter marshalling */
	scode_marshall();

	/* write the return address to scode stack */
	addr = get_32bit_aligned_value_from_guest((u64)linux_vmcb->cr3, (u32)whitelist[scode_curr].grsp);
	linux_vmcb->rsp -= 4;
	put_32bit_aligned_value_to_guest((u64)linux_vmcb->cr3, (u32)(linux_vmcb->rsp), addr);

	/* write the return address in whitelist structure */
	whitelist[scode_curr].return_v = addr;

	DEBUG printf("DEBUG: return address is %#x\n", whitelist[scode_curr].return_v);
	DEBUG printf("DEBUG: host stack pointer is %#x\n",(u32)linux_vmcb->rsp);
	/*test the value in stack*/
	//stack_value = get_32bit_aligned_value_from_guest((u64)linux_vmcb->cr3, (u32)linux_vmcb->rsp);
	//DEBUG printf("DEBUG: the value in stack top is %#x\n", stack_value);
	/* extern pcr */
	/* copy the sensitve code from guest to host */
	//copy_from_guest(scode, (u64)linux_vmcb->cr3, (u32)whitelist[scode_curr].gvaddr, (u32)whitelist[scode_curr].size);
	/* get hash of code */
	//sha1_csum(scode, PAGE_SIZE_4K, hash);
	/* extend pcr */
	// stpm_extend(hash);

	/*add by yanlinl end*/
}

//todo: switch from sensitive code to regular code
void scode_switch_regular(void)
{
	DEBUG printf("DEBUG: ************************************\n");
	DEBUG printf("DEBUG: *********** switch s->r ************\n");
	DEBUG printf("DEBUG: ************************************\n");
	/* marshalling parameters back to regular code */
	scode_unmarshall();

	/* clear the NPT permission setting in switching into scode */
	nested_switch_regular(whitelist[scode_curr].scode_page, whitelist[scode_curr].scode_size,
			(u32)whitelist[scode_curr].pte_page, whitelist[scode_curr].pte_size);

	scode_unexpose_arch();

	DEBUG printf("DEBUG: switch from current stack %#x back to regular stack %#x\n", (u32)linux_vmcb->rsp, (u32)whitelist[scode_curr].grsp);
	linux_vmcb->rsp = whitelist[scode_curr].grsp;
	linux_vmcb->rsp += 4; 
	linux_vmcb->rflags |= EFLAGS_IF;
	whitelist[scode_curr].grsp = (u32)-1;
}

u32 scode_npf(u32 gpaddr, u64 errorcode, u64 gcr3)
{
	int index = -1;
	/* gvaddr here should be the guest physical address that caused the nested page fault  -- ZONGWEI JAN 2 2010 */
	DEBUG printf("DEBUG: nested page fault (rip %#x, gcr3 %#llx, gpaddr %#x errorcode %#llx\n", (u32)linux_vmcb->rip, gcr3, gpaddr, errorcode);

	if (!(errorcode & ((u64)PF_ERRORCODE_PRESENT))) {
		/* nested page not present */
		/* could be malicious apps or OS try to access memory range of trustvisor */
		printf("SECURITY: code trying to access trustvisor memory range has been DETECTED !!\n"); 
		return 1;
	}

	index = scode_in_list(gcr3, (u32)linux_vmcb->rip);
	if ((scode_curr == -1) && (index >= 0)) {
		/* regular code to sensitive code */
		if ((errorcode && ((u64)PF_ERRORCODE_INST))) {
			/* instruction read */
			/* context switch from regular code to sensitive code */
			scode_curr = index;
			/* check entry point */
			if ((whitelist[scode_curr].entry_v == (u32)linux_vmcb->rip) && (whitelist[scode_curr].entry_p == gpaddr)) { 
				scode_switch_scode();
			} else {
				printf("SECURITY: incorrect scode entry point has been DETECTED !!\n");
				return 1;
			}
		} else {
			printf("SECURITY: regular code trying to access senstive range has been DETECTED !!\n");
			return 1;
		}
	} else if ((scode_curr >=0) && (index < 0)) {
		/* sensitive code to regular code */
		if ((errorcode && ((u64)PF_ERRORCODE_INST)) || ((errorcode && ((u64)PF_ERRORCODE_TABLEWALK)) || (errorcode && ((u64)PF_ERRORCODE_FINALWALK)))) {
			/* instruction read or table walk */
			/* context switch from sensitive code to regular code */
			if (whitelist[scode_curr].return_v == (u32)linux_vmcb->rip) { 
				scode_switch_regular();
				scode_curr = -1;
			} else {
				printf("SECURITY: incorrect scode return point has been DETECTED !!\n");
				return 1;
			}
		} else { 
			/* data read or data write */
			printf("SECURITY: sensitive code trying to access regular range has been DETECTED !!\n");
			return 1;
		} 
	} else if ((scode_curr >=0) && (index >= 0)) {
		/* sensitive code to sensitive code */
		if (scode_curr == index) 
			printf("DEBUG: Sensitive code access itself?? Possible NPT miconfiguration. \n");
		else
			printf("SECURITY: sensitive code trying to access other sensitive code range has been DETECTED !!\n"); 
		return 1;	
	} else {
		/* regular code to regular code */
		printf("DEBUG: Regular code access regular code?? Possible NPT misconfiguration. \n"); 
		return 1;
	}
	return 0;
}

int scode_in_list(u64 gcr3, u32 gvaddr)
{
	u32 i, j;

	for (i = 0; i < whitelist_size; i ++)
	{
		if (gcr3 == whitelist[i].gcr3) {
			for( j=0 ; j<(u32)(whitelist[i].scode_info.section_num) ; j++ )  {
				if( (gvaddr >= whitelist[i].scode_info.ps_str[j].start_addr) &&
						(gvaddr < ((whitelist[i].scode_info.ps_str[j].start_addr)+((whitelist[i].scode_info.ps_str[j].page_num)<<PAGE_SHIFT_4K)))  )  {
#if 0
					gpaddr = guest_pt_walker(gcr3, gvaddr);
					DEBUG printf("DEBUG: gpaddr %#x, pfn %#x\n", gpaddr, gpaddr >> PAGE_SHIFT_4K); 
					if (test_page_scode_bitmap(gpaddr >> PAGE_SHIFT_4K))
						/* ATTN: if we don't protect the page table for sensitive code,
						 * we'd better use ID to further verify the physical page is 
						 * the one for this sensitive code
						 */
#endif
						DEBUG printf("DEBUG: find gvaddr in scode %d section %d !\n", i, j+1);
					return i;
				}
			}
		}
	}
	DEBUG printf("DEBUG: no matching scode found\n");
	return -1;
}

/* functions for software tpm, by yanlinl at March 4, 2009 */

u32 scode_pcrread(u64 gcr3, u32 gvaddr, u32 num)
{
	int i;
	int index;
	u8 pcr[TPM_PCR_SIZE];

	DEBUG printf("PCRREAD DEBUG: cr3 %#x, gvaddr %#x\n", (u32)gcr3, gvaddr);
	index = scode_in_list(gcr3, (u32)linux_vmcb->rip); 

	if ((index >= 0) && (scode_curr >= 0))
	{
		scode_curr = index;
		stpm_pcrread(pcr, num);
		DEBUG printf("PCRREAD %d DEBUG: pcr value\n", num);
		for ( i = 0; i < TPM_HASH_SIZE/4; i ++)
		{
			DEBUG printf("PCRREAD %d DEBUG: %#x\n", num, ((u32 *)pcr)[i]);
		}

		copy_to_guest(gcr3, gvaddr, pcr, TPM_PCR_SIZE);
	} else 
	{
		printf("PCR Read DEBUG ERROR: cr3 %#x, gvaddr %#x, index %#x\n", (u32)gcr3, gvaddr, index);
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
		printf("PCR extend ERROR: cr3 %#x, gvaddr %#x\n", (u32)gcr3, gvaddr);
		printf("PCR extend ERROR: data size is too large\n");
		return 1;
	}

	/* get scode_curr */
	DEBUG printf("PCR extend DEBUG: cr3 %#x, gvaddr %#x, len %d, pcr num %d\n", (u32)gcr3, gvaddr, len, num);
	index = scode_in_list(gcr3, (u32)linux_vmcb->rip);

	if ((index >= 0) && (scode_curr >= 0))
	{
		scode_curr = index;
	}
	else
	{
		printf("PCR extend ERROR: cr3 %#x, gvaddr %#x\n", (u32)gcr3, gvaddr);
		printf("PCR extend ERROR: scode_curr error\n");
		return 1;
	}

	/* get data from guest */
	copy_from_guest((unsigned char *)data, gcr3, gvaddr, len);
	DEBUG printf("DEBUG: copy data from guest");
	/* hash input data */
	sha1_csum((unsigned char*)data, len, hash);
	DEBUG printf("DEBUG: PCR %d EXTEND, hash done!!", num);
	/* extend pcr */
	stpm_extend(hash, num);
	DEBUG printf("PCR %d extend finish\n", num); 
	return 0;
}


u32 scode_seal(u64 gcr3, u32 input_addr, u32 input_len, u32 pcrAtRelease_addr, u32 output_addr, u32 output_len_addr)
{
	unsigned int i;
	int index;
	u8 indata[1024];  /* the largest input data length is one page size, 4k - 48 bytes, 48 bytes  is header of output */
	u8 output[1024];  /* the largest output data length is one page size, 4k bytes */
	u8 pcr[TPM_PCR_SIZE];
	u32 outlen;
	/* check input data length */
	if (input_len > (1024 - 48) )
	{
		printf("PCR Seal DEBUG: input data length is too large, lenth %#x\n", input_len);
		return 1;
	}

	/* get scode_curr */
	DEBUG printf("PCR Seal DEBUG: cr3 %#x, inputaddr %#x\n", (u32)gcr3, input_addr);
	index = scode_in_list(gcr3, (u32)linux_vmcb->rip); 

	if ((index >= 0) && (scode_curr >= 0))
	{
		scode_curr = index;
	}
	else
	{
		printf("PCR Seal ERROR: cr3 %#x, inputaddr %#x\n", (u32)gcr3, input_addr);
		return 1;
	}

	/* copy input data to host */
	copy_from_guest(indata, gcr3, input_addr, input_len);
	DEBUG printf("input len = %d!\n", input_len);
	for(i=0;i<input_len;i++) {
		DEBUG printf("%x ", indata[i]);
	}
	DEBUG printf("\n");


	/* copy pcr value at release to host */
	copy_from_guest(pcr, gcr3, pcrAtRelease_addr, TPM_PCR_SIZE);
	DEBUG printf("pcr:\n");
	for(i=0;i<TPM_PCR_SIZE;i++) {
		DEBUG printf("%x ", pcr[i]);
	}
	DEBUG printf("\n");


	/* seal */
	stpm_seal(pcr, indata, input_len, output, &outlen);
	DEBUG printf("sealed len = %d!\n", outlen);
	for(i=0;i<outlen;i++) {
		DEBUG printf("%x ", output[i]);
	}
	DEBUG printf("\n");

	/*copy output to guest */
	copy_to_guest(gcr3, output_addr, output, outlen);

	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(gcr3, output_len_addr, outlen);
	DEBUG printf("PCR seal finish\n");
	return 0;
}

u32 scode_unseal(u64 gcr3, u32 input_addr, u32 input_len, u32 output_addr, u32 output_len_addr)
{
	u8 indata[1024]; 
	u8 outdata[1024];
	u32 outlen;
	u32 ret;
	int index;

	/* check input data length */
	if (input_len > 1024)
	{
		printf("PCR usSeal ERROR: cr3 %#x, inputaddr %#x, input_len %d\n", (u32)gcr3, input_addr, input_len);
		printf("PCR usSeal ERROR: input data length is too large\n");
		return 1;
	}

	/* get scode_curr */
	DEBUG printf("PCR unSeal DEBUG: cr3 %#x, inputaddr %#x\n", (u32)gcr3, input_addr);
	index = scode_in_list(gcr3, (u32)linux_vmcb->rip);    

	if ((index >= 0) && (scode_curr >= 0))
	{
		scode_curr = index;
	}
	else
	{
		printf("PCR unSeal ERROR: cr3 %#x, inputaddr %#x\n", (u32)gcr3, input_addr);
		return 1;
	}

	/* copy input data from guest */
	copy_from_guest(indata, gcr3, input_addr, input_len);
	/* unseal */
	ret = stpm_unseal(indata, input_len, outdata, &outlen);

	if (ret)
	{
		printf("PCR Unseal fail\n");
		return 1;
	}

	/* copy output to guest */
	copy_to_guest(gcr3, output_addr, outdata, outlen);
	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(gcr3, output_len_addr, outlen);
	DEBUG printf("PCR unseal finish\n");
	return 0;
}

u32 scode_quote(u64 gcr3, u32 nonce_addr, u32 out_addr, u32 out_len_addr)
{
	u8 outdata[TPM_QUOTE_SIZE];
	u8 aikdata[TPM_RSA_KEY_LEN];
	u8 nonce[TPM_NONCE_SIZE];
	u32 outlen, ret;
	u32 i;
	int index;

	/* get scode_curr */
	DEBUG printf("PCR quote DEBUG: cr3 %#x, outaddr %#x\n", (u32)gcr3, out_addr);
	index = scode_in_list(gcr3, (u32)linux_vmcb->rip);

	if ((index >= 0) && (scode_curr >= 0))
	{
		scode_curr = index;
	}
	else
	{
		printf("DEBUG: cr3 %#x, out_addr %#x\n", (u32)gcr3, out_addr);
		return 1;
	}

	DEBUG printf("DEBUG: QUOTE begin\n");

	/* get external nonce from guest */
	copy_from_guest(nonce, gcr3, nonce_addr, TPM_NONCE_SIZE);

	for (i = 0 ; i < TPM_NONCE_SIZE/4; i++)
	{
		DEBUG printf("DEBUG: nonce %d is %#x\n", i, (u32)(((u32*)nonce)[i]));
	}
	/* save quote result in out*/
	ret = stpm_quote(nonce, outdata, &outlen);
	if (ret != 0)
	{
		printf("DEBUG: TPM quote fail\n");
		return 1;
	}

	DEBUG{
		for (i = 12; i < (12 + 64); i++)
			printf("DEBUG: Quote %d, %#x\n",i, *(((unsigned int*)outdata)+i));
	}
	DEBUG printf("DEBUG: quote finish, data len %d\n", outlen);
	/* copy output to guest */
	copy_to_guest(gcr3, out_addr, outdata, outlen);

	for (i = 0; i < TPM_RSA_KEY_LEN; i++)
		aikdata[i] = ((u8*)g_rsa.N.p)[i];

	copy_to_guest(gcr3, out_addr + outlen, aikdata, TPM_RSA_KEY_LEN);
	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(gcr3, out_len_addr, outlen);

	DEBUG printf("DEBUG: quote result has been copyed to guest\n");

	return 0;
}

u32 scode_rand(u64 gcr3, u32 buffer_addr, u32 numbytes_requested, u32 numbytes_addr)
{
	u32 ret;
	int index;
	u8 buffer[STPM_RANDOM_BUFFER_SIZE + STPM_RANDOM_BUFFER_SIZE]; // buffer to save the random data
	u32 numbytes;

	/* get scode_curr */
	DEBUG printf("PCR rand DEBUG: cr3 %#x, buffaddr %#x, numbytes %d\n", (u32)gcr3, buffer_addr, numbytes_requested);
	index = scode_in_list(gcr3, (u32)linux_vmcb->rip);

	if ((index >= 0) && (scode_curr >= 0))
	{
		scode_curr = index;
	}
	else
	{
		printf("GEN RANDOM ERROR: cr3 %#x, buff_addr %#x\n", (u32)gcr3, buffer_addr);
		return 1;
	}

	// get the byte number requested
	numbytes = numbytes_requested;
	ret = stpm_rand(buffer, numbytes);
	if (ret != numbytes)
	{
		printf("DEBUG: utmp generate randon %d bytes, requested %d bytes\n", ret, numbytes);
	}
	numbytes = ret;

	DEBUG printf("DEBUG: copy random data to guest\n");
	/* copy random data to guest */
	copy_to_guest(gcr3, buffer_addr, buffer, numbytes);
	DEBUG printf("DEBUG: copy random data length to guest, %d bytes\n", numbytes);
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

   DEBUG printf("GetPubKey DEBUG: cr3 %#x, gvaddr %#x\n", (u32)gcr3, gvaddr);
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
   DEBUG printf("GetPubKey DEBUG ERROR: cr3 %#x, gvaddr %#x, index %#x\n", (u32)gcr3, gvaddr, index);
   return 1;
   }

   return 0;
   }
   */

