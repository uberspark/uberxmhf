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

// nested-x86vmx-ept12.c
// Handle EPT in the guest
// author: Eric Li (xiaoyili@andrew.cmu.edu)
#include <xmhf.h>
#include "nested-x86vmx-ept12.h"

static u8 ept02_page_pool[MAX_VCPU_ENTRIES][VMX_NESTED_MAX_ACTIVE_VMCS]
	[EPT02_PAGE_POOL_SIZE][PAGE_SIZE_4K]
	__attribute__((section(".bss.palign_data")));

static u8 ept02_page_alloc[MAX_VCPU_ENTRIES][VMX_NESTED_MAX_ACTIVE_VMCS]
	[EPT02_PAGE_POOL_SIZE];

static void *ept02_gzp(void *vctx, size_t alignment, size_t sz)
{
	ept02_ctx_t *ept02_ctx = (ept02_ctx_t *) vctx;
	u32 i;
	HALT_ON_ERRORCOND(alignment == PAGE_SIZE_4K);
	HALT_ON_ERRORCOND(sz == PAGE_SIZE_4K);
	for (i = 0; i < EPT02_PAGE_POOL_SIZE; i++) {
		if (!ept02_ctx->page_alloc[i]) {
			void *page = ept02_ctx->page_pool[i];
			ept02_ctx->page_alloc[i] = 1;
			memset(page, 0, PAGE_SIZE_4K);
			return page;
		}
	}
	return NULL;
}

static hpt_pa_t ept02_ptr2pa(void *vctx, void *ptr)
{
	(void)vctx;
	return hva2spa(ptr);
}

static void *ept02_pa2ptr(void *vctx, hpt_pa_t spa, size_t sz,
						  hpt_prot_t access_type, hptw_cpl_t cpl,
						  size_t *avail_sz)
{
	(void)vctx;
	(void)access_type;
	(void)cpl;
	*avail_sz = sz;
	return spa2hva(spa);
}

/*
 * Initialize the ept02_ctx_t structure in ept02_ctx.
 * The current CPU and VMCS12 is vcpu and vmcs12_info.
 */
void xmhf_nested_arch_x86vmx_ept02_init(VCPU * vcpu,
										vmcs12_info_t * vmcs12_info,
										ept02_ctx_t * ept02_ctx)
{
	ept02_ctx->page_pool = ept02_page_pool[vcpu->idx][vmcs12_info->index];
	ept02_ctx->page_alloc = ept02_page_alloc[vcpu->idx][vmcs12_info->index];
	ept02_ctx->ctx.gzp = ept02_gzp;
	ept02_ctx->ctx.pa2ptr = ept02_pa2ptr;
	ept02_ctx->ctx.ptr2pa = ept02_ptr2pa;
	ept02_ctx->ctx.root_pa =
		hva2spa(ept02_gzp(&ept02_ctx->ctx, PAGE_SIZE_4K, PAGE_SIZE_4K));
	ept02_ctx->ctx.t = HPT_TYPE_EPT;
}

/*
 * Get pointer to EPT02 for current VMCS12. Will fill EPT02 as EPT violation
 * happens.
 */
spa_t xmhf_nested_arch_x86vmx_get_ept02(VCPU * vcpu,
										vmcs12_info_t * vmcs12_info)
{
	spa_t addr = (uintptr_t) vmcs12_info->ept02_ctx.page_pool[0];
	(void)vcpu;
	return addr | 0x1e;			// TODO: remove magic number
}

/*
 * Handles an EPT exit received by L0 when running L2. There are 3 cases.
 * 1. L2 accesses legitimate memory, but L0 has not processed the EPT entry in
 *    L1 yet. In this case this function returns 1. XMHF should add EPT entry
 *    to EPT02 and continue running L2.
 * 2. L2 accesses memory not in EPT12. In this case this function returns 2.
 *    XMHF should forward EPT violation to L1.
 * 3. L2 accesses memory not valid in EPT01 (L1 sets up EPT that accesses
 *    illegal memory). In this case this function returns 3. XMHF should halt
 *    for security.
 */
int xmhf_nested_arch_x86vmx_handle_ept02_exit(VCPU * vcpu,
											  vmcs12_info_t * vmcs12_info)
{
	guestmem_hptw_ctx_pair_t ctx_pair;
	guestmem_init(vcpu, &ctx_pair);
	HALT_ON_ERRORCOND(0 && "TODO frontier");
	(void)vmcs12_info;
	return 3;
}
