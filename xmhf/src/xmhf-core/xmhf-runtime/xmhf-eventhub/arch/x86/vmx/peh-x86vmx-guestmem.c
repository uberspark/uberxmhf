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

// peh-x86vmx-guestmem.c
// Function for accessing guest memeory
// author: Eric Li (xiaoyili@andrew.cmu.edu)
#include <xmhf.h>

static hpt_pa_t guestmem_host_ctx_ptr2pa(void *vctx, void *ptr)
{
	(void)vctx;
	return hva2spa(ptr);
}

static void* guestmem_host_ctx_pa2ptr(void *vctx, hpt_pa_t spa, size_t sz, hpt_prot_t access_type, hptw_cpl_t cpl, size_t *avail_sz)
{
	(void)vctx;
	(void)access_type;
	(void)cpl;
	*avail_sz = sz;
	return spa2hva(spa);
}

static hpt_pa_t guestmem_guest_ctx_ptr2pa(void __attribute__((unused)) *ctx, void *ptr)
{
	return hva2gpa(ptr);
}

static void* guestmem_guest_ctx_pa2ptr(void *vctx, hpt_pa_t gpa, size_t sz, hpt_prot_t access_type, hptw_cpl_t cpl, size_t *avail_sz)
{
	guestmem_hptw_ctx_pair_t *ctx_pair = vctx;

	return hptw_checked_access_va(&ctx_pair->host_ctx,
									access_type,
									cpl,
									gpa,
									sz,
									avail_sz);
}

static void* guestmem_ctx_unimplemented(void *vctx, size_t alignment, size_t sz)
{
	(void)vctx;
	(void)alignment;
	(void)sz;
	HALT_ON_ERRORCOND(0 && "Not implemented");
	return NULL;
}

/*
 * Initialize guestmem_hptw_ctx_pair_t
 *
 * For each interception, before accessing guest memory, guestmem_init() needs
 * to be called to update guestmem_hptw_ctx_pair_t.
 */
void guestmem_init(VCPU *vcpu, guestmem_hptw_ctx_pair_t *ctx_pair)
{
	hpt_type_t guest_t = hpt_emhf_get_guest_hpt_type(vcpu);
	ctx_pair->guest_ctx.ptr2pa = guestmem_guest_ctx_ptr2pa;
	ctx_pair->guest_ctx.pa2ptr = guestmem_guest_ctx_pa2ptr;
	ctx_pair->guest_ctx.gzp = guestmem_ctx_unimplemented;
	ctx_pair->guest_ctx.root_pa =
		hpt_cr3_get_address(guest_t, vcpu->vmcs.guest_CR3);
	ctx_pair->guest_ctx.t = guest_t;
	ctx_pair->host_ctx.ptr2pa = guestmem_host_ctx_ptr2pa;
	ctx_pair->host_ctx.pa2ptr = guestmem_host_ctx_pa2ptr;
	ctx_pair->host_ctx.gzp = guestmem_ctx_unimplemented;
	ctx_pair->host_ctx.root_pa =
		hpt_eptp_get_address(HPT_TYPE_EPT, vcpu->vmcs.control_EPT_pointer);
	ctx_pair->host_ctx.t = HPT_TYPE_EPT;
}

/* Copy from dst (guest virtual address) to src (hypervisor address) */
void guestmem_copy_g2h(guestmem_hptw_ctx_pair_t *ctx_pair, hptw_cpl_t cpl,
						void *dst, hpt_va_t src, size_t len)
{
	hptw_ctx_t *ctx = &ctx_pair->guest_ctx;
	int result = hptw_checked_copy_from_va(ctx, cpl, dst, src, len);
	HALT_ON_ERRORCOND(result == 0);
}

