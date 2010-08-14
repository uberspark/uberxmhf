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
 */

#ifndef __MODULE_H_
#define __MODULE_H_

#include "rsa.h" // for global rsa key
#include "arc4.h"  // for arc4_context in whitelist_entry, by yanlinl at Jul 28, 2009
#include "tpm_sw.h"
#include "params.h"

#ifndef STPM_RANDOM_BUFFER_SIZE
#define STPM_RANDOM_BUFFER_SIZE 128
#endif

/* definde for scode sections info */

#define MAX_SECTION_NUM 10  /* max sections that are allowed in scode registration */

typedef int SECTION_TYPE;  /* section type, different section types have different page permission */
#define  SECTION_TYPE_SCODE 1
#define  SECTION_TYPE_SDATA 2
#define  SECTION_TYPE_PARAM 3
#define  SECTION_TYPE_STACK 4
#define  SECTION_TYPE_STEXT 5

/* from params.h */
#define MAX_STACK_SIZE 0x1000       /* 2k */         
#define MAX_INPUT_PARAMS_SIZE 0x1000 /* 1k */      
#define MAX_OUTPUT_PARAMS_SIZE 10    

#define MAX_PARAMS_NUM 10

/* parameter type */
#define PM_TYPE_INTEGER 1 /* integre */
#define PM_TYPE_POINTER 2 /* pointer */


struct scode_params_struct{
  u32 type;  /* 1: integer ;  2:pointer*/
  u32 size;
};

struct scode_params_info{
  u32 params_num;
  struct scode_params_struct pm_str[MAX_PARAMS_NUM];
};

void pm_parse_params_info(struct scode_params_info* pm_info, u64 cr3, u32 pm_addr);



struct scode_sections_struct{
	SECTION_TYPE type;  
	unsigned int start_addr;
	int page_num;
};

struct scode_sections_info{
	int section_num;
	struct scode_sections_struct ps_str[MAX_SECTION_NUM];
};

typedef struct whitelist_entry{
	u64 gcr3; 
	u32 id;
	u32 grsp;		/* guest reguar stack */
	u32 gssp;		/* guest senstive code stack */
	u32 entry_v; /* entry point virutal address */
	u32 entry_p; /* entry point physical address */
	u32 return_v; /* return point virtual address */

	u32 gpmp;             /* guest parameter infomation address, add by yanlinl*/
	u32 gpm_num;
	u8  pcr[TPM_PCR_SIZE*TPM_PCR_NUM];          /* pcr for sensitive code, by yanlin at March 3, 2009*/
	u64 refillNo;         /* counter number for rand generator, initialized to 0 when sscb registered, by yanlinl at Jul 28, 2009*/
	u8  randKey[2*STPM_RANDOM_BUFFER_SIZE];/* utmp rand generator key, initialized by TPM when sscb registered, by yanlinl at Jul 28, 2009*/
	u8  aeskey[32];
	u8 hmackey[40];
	arc4_context arc4_ctx;/* acr4 context for rand generator, by yanlinl at Jul 28, 2009*/


	struct scode_sections_info scode_info; /* scode_info struct for registration function inpu */
	struct scode_params_info params_info; /* param info struct */
	u32 scode_page; /* holder for scode pages */
	u32 scode_size; /* scode size */

	u32 pte_page;  /* holder for guest page table entry to access scode and GDT */
	u32 pte_size;	/* total size of all PTE pages */

	/* FIXME: delte these after fixing all scode functions */
//	u32 gvaddr;
//	u32 size;
//	u64 tmp_pte_page[7];
//	u32 tmp_pte_size;
} __attribute__ ((packed)) whitelist_entry_t;


typedef struct hashlist_entry{
	u8 checksum[SHA1_CHECKSUM_LEN];
} __attribute__ ((packed)) hashlist_entry_t;

extern whitelist_entry_t *whitelist;
extern u8 scode_pfn_bitmap[];
extern u16 scode_pfn_bitmap_2M[];
extern rsa_context g_rsa;

/* helper function */
static inline u32 set_page_scode_bitmap_2M(u32 pfn)
{
	u32 index;

	index = pfn >> (PAGE_SHIFT_2M - PAGE_SHIFT_4K);
	if (scode_pfn_bitmap_2M[index] < PAE_PTRS_PER_PDT)
		scode_pfn_bitmap_2M[index] ++;
	else
	{
		printf("FATAL ERROR: exceed the limitation of 2M page\n");
		FORCE_CRASH();
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
		FORCE_CRASH();
	}

	return scode_pfn_bitmap_2M[index];
}

static inline u32 test_page_scode_bitmap_2M(u32 pfn)
{
	u32 index;

	index = pfn >> (PAGE_SHIFT_2M - PAGE_SHIFT_4K);

	return scode_pfn_bitmap_2M[index];
}

/* set scode remapping protection for a page, pfn is the page frame number */
#define set_page_scode_bitmap(pfn)	set_page_prot(pfn, scode_pfn_bitmap)
/* clear scode remapping protection for a page, pfn is the page frame number */
#define clear_page_scode_bitmap(pfn)	clear_page_prot(pfn, scode_pfn_bitmap)
/* test scode remapping protection enabled for a page, pfn is the page frame number */
#define test_page_scode_bitmap(pfn)	test_page_prot(pfn, scode_pfn_bitmap)

void init_scode(void) __attribute__ ((section ("_init_text")));
int scode_parse_sectios_info(struct scode_sections_info * scode_info, u64 cr3, u32 ps_addr);
u32 scode_register(u64 gcr3, u32 scode_info, u32 scode_sp, u32 scode_pm, u32 gventry);
u32 scode_unregister(u64 gcr3, u32 gvaddr);
u32 scode_npf(u32 gvaddr, u64 errorcode, u64 gcr3);

u32 scode_pcrread(u64 gcr3, u32 gvaddr, u32 num);
u32 scode_pcrextend(u64 gcr3, u32 gvaddr, u32 len, u32 num);
u32 scode_seal(u64 gcr3, u32 input_addr, u32 input_len, u32 pcrhash_addr, u32 output_addr, u32 output_len_addr);
u32 scode_unseal(u64 gcr3, u32 input_addr, u32 input_len, u32 output_addr, u32 output_len_addr);
u32 scode_quote(u64 gcr3, u32 nonce_addr, u32 out_addr, u32 out_len_addr);
u32 scode_rand(u64 gcr3, u32 buffer_addr, u32 numbytes_requested, u32 numbytes_addr);
//u32 scode_getpubkey(u64 gcr3, u32 gvaddr);
#endif /* __MODULE_H_ */
