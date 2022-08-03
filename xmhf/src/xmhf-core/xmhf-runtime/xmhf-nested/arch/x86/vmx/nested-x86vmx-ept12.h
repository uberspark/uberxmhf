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

// nested-x86vmx-ept12.h
// Handle EPT in the guest
// author: Eric Li (xiaoyili@andrew.cmu.edu)

#ifndef _NESTED_X86VMX_EPT12_H_
#define _NESTED_X86VMX_EPT12_H_

#include "nested-x86vmx-vmcs12.h"
#include "nested-x86vmx-lru.h"

/* Maximum number of active EPTs per CPU */
#define VMX_NESTED_MAX_ACTIVE_EPT 4

/* Maximum number of active VPIDs per CPU */
#define VMX_NESTED_MAX_ACTIVE_VPID 4

/* Format of EPT12 context information */
typedef struct {
	/* Context of EPT12 */
	hptw_ctx_t ctx;
	/* Context of EPT01 */
	guestmem_hptw_ctx_pair_t ctx01;
} ept12_ctx_t;

/* Format of EPT02 context information */
typedef struct {
	/* Context */
	hptw_ctx_t ctx;
	/* List of pages to be allocated by ctx, limit = EPT02_PAGE_POOL_SIZE */
	 u8(*page_pool)[PAGE_SIZE_4K];
	/* Whether the corresponding page in page_pool is allocated */
	u8 *page_alloc;
} ept02_ctx_t;

typedef u32 ept02_cache_index_t;

/* Guest physical address of EPT12 (4K aligned) */
typedef gpa_t ept02_cache_key_t;

typedef struct {
	/* EPT02 context (for allocating pages) */
	ept02_ctx_t ept02_ctx;
	/* EPT12 context (for accessing guest EPT) */
	ept12_ctx_t ept12_ctx;
} ept02_cache_value_t;

LRU_NEW_SET(ept02_cache_set_t, ept02_cache_line_t, VMX_NESTED_MAX_ACTIVE_EPT,
			ept02_cache_index_t, ept02_cache_key_t, ept02_cache_value_t);

typedef u16 vpid02_cache_index_t;
typedef u16 vpid02_cache_key_t;
typedef u16 vpid02_cache_value_t;

LRU_NEW_SET(vpid02_cache_set_t, vpid02_cache_line_t, VMX_NESTED_MAX_ACTIVE_VPID,
			vpid02_cache_index_t, vpid02_cache_key_t, vpid02_cache_value_t);

void xmhf_nested_arch_x86vmx_ept_init(VCPU * vcpu);
void xmhf_nested_arch_x86vmx_vpid_init(VCPU * vcpu);
bool xmhf_nested_arch_x86vmx_check_ept_lower_bits(u64 eptp12,
												  gpa_t * ept_pml4t);
void xmhf_nested_arch_x86vmx_invept_single_context(VCPU * vcpu, gpa_t ept12);
/* xmhf_nested_arch_x86vmx_invept_global() is defined in xmhf-nested.h */
bool xmhf_nested_arch_x86vmx_invvpid_indiv_addr(VCPU * vcpu, u16 vpid12,
												u64 address);
void xmhf_nested_arch_x86vmx_invvpid_single_ctx(VCPU * vcpu, u16 vpid12);
void xmhf_nested_arch_x86vmx_invvpid_all_ctx(VCPU * vcpu);
void xmhf_nested_arch_x86vmx_invvpid_single_ctx_global(VCPU * vcpu, u16 vpid12);
spa_t xmhf_nested_arch_x86vmx_get_ept02(VCPU * vcpu, gpa_t ept12,
										bool *cache_hit,
										ept02_cache_line_t ** cache_line);
u16 xmhf_nested_arch_x86vmx_get_vpid02(VCPU * vcpu, u16 vpid12,
									   bool *cache_hit);
int xmhf_nested_arch_x86vmx_handle_ept02_exit(VCPU * vcpu,
											  ept02_cache_line_t * cache_line,
											  u64 guest2_paddr,
											  ulong_t qualification);
void xmhf_nested_arch_x86vmx_hardcode_ept(VCPU * vcpu,
										  ept02_cache_line_t * cache_line,
										  u64 guest2_paddr);

#endif							/* _NESTED_X86VMX_EPT12_H_ */
