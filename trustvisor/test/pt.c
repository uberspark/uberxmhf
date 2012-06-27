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

#include "unity.h"

#define __PRINT_H_ /* avoid indirectly including our print.h, which conflicts with libc stdio.h */
#include <xmhf.h>

/* run time parameter block. we'll mock this up as needed */
RPB __rpb;
RPB *rpb = &__rpb;

/* global CPU structs */
VCPU g_vcpubuffers[0];

#define BR64_GET(x64, name) BR64_GET_HL(x64, name##_HI, name##_LO)
#define BR64_SET(x64, name, val) BR64_SET_HL(x64, name##_HI, name##_LO, val)

/* do-nothing mock */
void emhf_hwpgtbl_flushall(VCPU *vcpu)
{
}

static u64 get_addr(u64 entry, u32 hi, u32 lo)
{
	return BR64_GET_HL(entry, hi, lo) << lo;
}
static u64 set_addr(u64 entry, u32 hi, u32 lo, u64 val)
{
	ASSERT((BR64_GET_HL(val, hi, lo) << lo) == val);
	return BR64_SET_HL(entry, hi, lo, val >> lo);
}

typedef u64 ept_pml4e_t;
typedef u64 ept_pdpte_t;
typedef u64 ept_pde_t;
typedef u64 ept_pte_t;

typedef u64 gpaddr_t;
typedef u64 hpaddr_t;

#define EPT_PML4_SIZE 512
#define EPT_PDPT_SIZE 512
#define EPT_PD_SIZE 512
#define EPT_PT_SIZE 512

/* max bits used in physical devices. processor-dependent. */
#define M 47

/* PML4E bit fields */
#define EPT_PML4E_IGN0_HI 63
#define EPT_PML4E_IGN0_LO 52
#define EPT_PML4E_RSVD0_HI 51
#define EPT_PML4E_RSVD0_LO M
#define EPT_PML4E_PDPT_HI (M-1)
#define EPT_PML4E_PDPT_LO 12
#define EPT_PML4E_IGN1_HI 11
#define EPT_PML4E_IGN1_LO 8
#define EPT_PML4E_RSVD2_HI 7
#define EPT_PML4E_RSVD2_LO 3
#define EPT_PML4E_X_HI 2
#define EPT_PML4E_X_LO 2
#define EPT_PML4E_W_HI 1
#define EPT_PML4E_W_LO 1
#define EPT_PML4E_R_HI 0
#define EPT_PML4E_R_LO 0
#define EPT_PML4E_NP_HI 2 /* not-present */
#define EPT_PML4E_NP_LO 0


/* PDPTE bit fields */
#define EPT_PDPTE_IGN0_HI 63
#define EPT_PDPTE_IGN0_LO 52
#define EPT_PDPTE_RSVD0_HI 51
#define EPT_PDPTE_RSVD0_LO M
/****** when ISPAGE==0 ********************/
  #define EPT_PDPTE_PD_HI (M-1)
  #define EPT_PDPTE_PD_LO 12
/******* when ISPAGE==1********************/
  #define EPT_PDPTE_PAGE_HI (M-1)
  #define EPT_PDPTE_PAGE_LO 30
  #define EPT_PDPTE_RSVD1_HI 29
  #define EPT_PDPTE_RSVD1_LO 12
/******************************************/
#define EPT_PDPTE_IGN1_HI 11
#define EPT_PDPTE_IGN1_LO 8
#define EPT_PDPTE_ISPAGE_HI 7
#define EPT_PDPTE_ISPAGE_LO 7
/****** when ISPAGE==0 ********************/
  #define EPT_PDPTE_RSVD2_HI 6
  #define EPT_PDPTE_RSVD2_LO 3
/****** when ISPAGE==1 ********************/
  #define EPT_PDPTE_IPAT_HI 6
  #define EPT_PDPTE_IPAT_LO 6
  #define EPT_PDPTE_EPTMT_HI 5
  #define EPT_PDPTE_EPTMT_LO 3
/******************************************/
#define EPT_PDPTE_X_HI 2
#define EPT_PDPTE_X_LO 2
#define EPT_PDPTE_W_HI 1
#define EPT_PDPTE_W_LO 1
#define EPT_PDPTE_R_HI 0
#define EPT_PDPTE_R_LO 0
#define EPT_PDPTE_NP_HI 2 /* not-present */
#define EPT_PDPTE_NP_LO 0
#define EPT_PDPTE_PROT_HI 2
#define EPT_PDPTE_PROT_LO 0


/* PDE bit fields */
#define EPT_PDE_IGN0_HI 63
#define EPT_PDE_IGN0_LO 52
#define EPT_PDE_RSVD0_HI 51
#define EPT_PDE_RSVD0_LO M
/****** when ISPAGE==0 ********************/
  #define EPT_PDE_PT_HI (M-1)
  #define EPT_PDE_PT_LO 12
/******* when ISPAGE==1********************/
  #define EPT_PDE_PAGE_HI (M-1)
  #define EPT_PDE_PAGE_LO 21
  #define EPT_PDE_RSVD1_HI 20
  #define EPT_PDE_RSVD1_LO 12
/******************************************/
#define EPT_PDE_IGN1_HI 11
#define EPT_PDE_IGN1_LO 8
#define EPT_PDE_ISPAGE_HI 7
#define EPT_PDE_ISPAGE_LO 7
/****** when ISPAGE==0 ********************/
  #define EPT_PDE_RSVD2_HI 6
  #define EPT_PDE_RSVD2_LO 3
/****** when ISPAGE==1 ********************/
  #define EPT_PDE_IPAT_HI 6
  #define EPT_PDE_IPAT_LO 6
  #define EPT_PDE_EPTMT_HI 5
  #define EPT_PDE_EPTMT_LO 3
/******************************************/
#define EPT_PDE_X_HI 2
#define EPT_PDE_X_LO 2
#define EPT_PDE_W_HI 1
#define EPT_PDE_W_LO 1
#define EPT_PDE_R_HI 0
#define EPT_PDE_R_LO 0
#define EPT_PDE_NP_HI 2 /* not-present */
#define EPT_PDE_NP_LO 0
#define EPT_PDE_PROT_HI 2
#define EPT_PDE_PROT_LO 0

static hpaddr_t ept_pde_pt_get(ept_pde_t ept_pde)
{
	return get_addr(ept_pde, EPT_PDE_PT_HI, EPT_PDE_PT_LO);
}
static ept_pde_t ept_pde_pt_set(ept_pde_t ept_pde, hpaddr_t ept_pt)
{
	return set_addr(ept_pde, EPT_PDE_PT_HI, EPT_PDE_PT_LO, ept_pt);
}

/* PTE bit fields */
#define EPT_PTE_IGN0_HI 63
#define EPT_PTE_IGN0_LO 52
#define EPT_PTE_RSVD0_HI 51
#define EPT_PTE_RSVD0_LO M
#define EPT_PTE_PAGE_HI (M-1)
#define EPT_PTE_PAGE_LO 12
#define EPT_PTE_IGN1_HI 11
#define EPT_PTE_IGN1_LO 7
#define EPT_PTE_IPAT_HI 6
#define EPT_PTE_IPAT_LO 6
#define EPT_PTE_EPTMT_HI 5
#define EPT_PTE_EPTMT_LO 3
#define EPT_PTE_X_HI 2
#define EPT_PTE_X_LO 2
#define EPT_PTE_W_HI 1
#define EPT_PTE_W_LO 1
#define EPT_PTE_R_HI 0
#define EPT_PTE_R_LO 0
#define EPT_PTE_NP_HI 2 /* not-present */
#define EPT_PTE_NP_LO 0
#define EPT_PTE_PROT_HI 2
#define EPT_PTE_PROT_LO 0

/* guest physical address */

#define EPT_GPA_PML4_I_HI 47
#define EPT_GPA_PML4_I_LO 39
#define EPT_GPA_PDPT_I_HI 38
#define EPT_GPA_PDPT_I_LO 30
#define EPT_GPA_PD_I_HI 29
#define EPT_GPA_PD_I_LO 21
#define EPT_GPA_PT_I_HI 20
#define EPT_GPA_PT_I_LO 12
#define EPT_GPA_OFFSET_HI 11
#define EPT_GPA_OFFSET_LO 0

static u32 gpaddr_list;
static u32 gpaddr_count;
static u64 ept_pdpt[EPT_PDPT_SIZE];

static void ept_pdpte_init(ept_pdpte_t *ept_pdpte)
{
	*ept_pdpte = 0;
}

static void ept_pdpt_init(ept_pdpte_t *ept_pdpt)
{
	int i;
	for(i=0; i<EPT_PDPT_SIZE; i++) {
		ept_pdpt[i] = 0;
	}
}

static ept_pdpte_t* ept_pd_construct(void)
{
	ept_pdpte_t *rv;
	if (posix_memalign(&rv, PAGE_SIZE_4K, EPT_PD_SIZE*sizeof(ept_pde_t)))
		return NULL;
	else
		return rv;
}

/* intermediate levels that weren't present are given rwx */
static void ept_pdpt_insert(ept_pdpte_t* ept_pdpt, gpaddr_t gpaddr)
{
	ept_pde_t *ept_pd;
	ept_pdpte_t *ept_pdpte;
	ept_pdpte = &ept_pdpt[BR64_GET(gpaddr, EPT_GPA_PDPT_I)];

	/* if not present, create pd. (maintaining np == unallocated for the
		 test harness) */
	if (BR64_GET(*ept_pdpte, EPT_PDPTE_NP)) {
		ept_pd = ept_pd_construct();
		/* BR64_SET(*ept_pdpte */
	}
}

void setUp(void)
{
	gpaddr_list = 0;
	gpaddr_count = 0;
	/* initialize page tables */
}

void tearDown(void)
{
}

void test_MASKRANGE64_all(void)
{
	/* TEST_ASSERT_EQUAL_HEX64(1ll, 1ll); */
	TEST_ASSERT_EQUAL_HEX64(0xffffffffffffffffull, MASKRANGE64(63, 0));
	TEST_ASSERT_EQUAL_HEX64(0x7fffffffffffffffull, MASKRANGE64(62, 0));
	TEST_ASSERT_EQUAL_HEX64(0x3ull, MASKRANGE64(1, 0));
	TEST_ASSERT_EQUAL_HEX64(0x1ull, MASKRANGE64(0, 0));

	/* ept_pdpte_t p; */
	/* ept_pdpte_init(&p); */
	/* p = BR64_SET(p, EPT_PDPTE_X, 1); */
	/* printf("p : %0.16llx\n", p); */
	/* printf("63,0 : %0.16llx\n",  */
	/* printf("63,0 : %0.16llx\n", MASKRANGE64(63, 62)); */
	/* printf("7,0  : %0.16llx\n", MASKRANGE64(7, 0)); */
	/* printf("63,56: %0.16llx\n", MASKRANGE64(63, 56)); */
	/* printf("55,48: %0.16llx\n", MASKRANGE64(55, 48)); */
	/*vmx_nested_make_pt_accessible(gpaddr_list, gpaddr_count, npdp, true);*/
}

/* if pde is not-present, sets it to rwx, and sets unregistered pt's below it to not-present */
/* XXX why not set all pt's below it to not-present? */
/* XXX what about if pdpte is not-present? */


/* if is_pal, sets pte permissions to pte's pal permissions */

/* if not is_pal, sets pte permissions to rw */
/* XXX why not just r? */
