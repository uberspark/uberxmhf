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
#include <hpt_emhf.h>

/*
 * This library provides functions for the hypervisor to access guest memory
 * space:
 * * guestmem_init: initialize structures, call whenever CR3 / EPTP changes
 * * guestmem_copy_gv2h: copy from guest virtual to hypervisor
 * * guestmem_copy_gp2h: copy from guest physical to hypervisor
 * * guestmem_copy_h2gv: copy from hypervisor to guest virtual
 * * guestmem_copy_h2gp: copy from hypervisor to guest physical
 * * guestmem_gpa2spa_page: translate gpa to spa for a whole page
 * * guestmem_gpa2spa_size: translate gpa to spa for some custom size
 * * guestmem_desegment: convert logical address to linear address
 *
 * Accessing EPT in hypervisor code may create race conditions. Currently the
 * following functions use memprot_x86vmx_eptlock_read_lock() and
 * memprot_x86vmx_eptlock_read_unlock() to avoid the race condition:
 * * guestmem_copy_gv2h: copy from guest virtual to hypervisor
 * * guestmem_copy_gp2h: copy from guest physical to hypervisor
 * * guestmem_copy_h2gv: copy from hypervisor to guest virtual
 * * guestmem_copy_h2gp: copy from hypervisor to guest physical
 *
 * Currently the following functions have NOT implemented the locking logic
 * (their use callers have other ways to prevent this race condition):
 * * guestmem_gpa2spa_page: translate gpa to spa for a whole page
 * * guestmem_gpa2spa_size: translate gpa to spa for some custom size
 *
 * See memp-x86vmx-eptlock.c for details about the race condition.
 */

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
	ctx_pair->vcpu = vcpu;
}

/*
 * Copy from dst (guest virtual address) to src (hypervisor address).
 * This function uses memprot_x86vmx_eptlock_read_lock() to prevent race
 * condition.
 */
void guestmem_copy_gv2h(guestmem_hptw_ctx_pair_t *ctx_pair, hptw_cpl_t cpl,
						void *dst, hpt_va_t src, size_t len)
{
	hptw_ctx_t *ctx = &ctx_pair->guest_ctx;
	memprot_x86vmx_eptlock_read_lock(ctx_pair->vcpu);
	HALT_ON_ERRORCOND(hptw_checked_copy_from_va(ctx, cpl, dst, src, len) == 0);
	memprot_x86vmx_eptlock_read_unlock(ctx_pair->vcpu);
}

/*
 * Copy from dst (guest physical address) to src (hypervisor address).
 * This function uses memprot_x86vmx_eptlock_read_lock() to prevent race
 * condition.
 */
void guestmem_copy_gp2h(guestmem_hptw_ctx_pair_t *ctx_pair, hptw_cpl_t cpl,
						void *dst, hpt_va_t src, size_t len)
{
	hptw_ctx_t *ctx = &ctx_pair->host_ctx;
	memprot_x86vmx_eptlock_read_lock(ctx_pair->vcpu);
	HALT_ON_ERRORCOND(hptw_checked_copy_from_va(ctx, cpl, dst, src, len) == 0);
	memprot_x86vmx_eptlock_read_unlock(ctx_pair->vcpu);
}

/*
 * Copy from dst (hypervisor address) to src (guest virtual address).
 * This function uses memprot_x86vmx_eptlock_read_lock() to prevent race
 * condition.
 */
void guestmem_copy_h2gv(guestmem_hptw_ctx_pair_t *ctx_pair, hptw_cpl_t cpl,
						hpt_va_t dst, void *src, size_t len)
{
	hptw_ctx_t *ctx = &ctx_pair->guest_ctx;
	memprot_x86vmx_eptlock_read_lock(ctx_pair->vcpu);
	HALT_ON_ERRORCOND(hptw_checked_copy_to_va(ctx, cpl, dst, src, len) == 0);
	memprot_x86vmx_eptlock_read_unlock(ctx_pair->vcpu);
}

/*
 * Copy from dst (hypervisor address) to src (guest physical address).
 * This function uses memprot_x86vmx_eptlock_read_lock() to prevent race
 * condition.
 */
void guestmem_copy_h2gp(guestmem_hptw_ctx_pair_t *ctx_pair, hptw_cpl_t cpl,
						hpt_va_t dst, void *src, size_t len)
{
	hptw_ctx_t *ctx = &ctx_pair->host_ctx;
	memprot_x86vmx_eptlock_read_lock(ctx_pair->vcpu);
	HALT_ON_ERRORCOND(hptw_checked_copy_to_va(ctx, cpl, dst, src, len) == 0);
	memprot_x86vmx_eptlock_read_unlock(ctx_pair->vcpu);
}

/*
 * Test whether guest_addr (4K page aligned) is valid guest physical memory
 * page. If so, return corresponding host physical memory page. Else, halt.
 *
 * This function does NOT use memprot_x86vmx_eptlock_read_lock() to prevent
 * race condition.
 */
spa_t guestmem_gpa2spa_page(guestmem_hptw_ctx_pair_t *ctx_pair,
							gpa_t guest_addr)
{
	void *ans;
	size_t avail_size;
	HALT_ON_ERRORCOND(PA_PAGE_ALIGNED_4K(guest_addr));
	ans = hptw_checked_access_va(&ctx_pair->host_ctx,
								HPT_PROTS_R,
								0,
								guest_addr,
								PAGE_SIZE_4K,
								&avail_size);
	/*
	 * If this fails, likely the memory crosses page boundary. But haven't we
	 * just checked that guest_addr is page aligned?
	 */
	HALT_ON_ERRORCOND(avail_size == PAGE_SIZE_4K);
	return hva2spa(ans);
}

/*
 * Test whether guest_addr is valid continuous guest physical memory of size
 * len in host physical memory. If so, return corresponding host physical
 * memory page. Else, halt.
 *
 * This function does NOT use memprot_x86vmx_eptlock_read_lock() to prevent
 * race condition.
 */
spa_t guestmem_gpa2spa_size(guestmem_hptw_ctx_pair_t *ctx_pair,
							gpa_t guest_addr, size_t len)
{
	void *ans = NULL;
	size_t scanned = 0;
	bool ans_assigned = false;
	while (scanned < len) {
		gpa_t ptr_gpa = guest_addr + scanned;
		size_t cur_scan;
		void *ptr;
		ptr = hptw_checked_access_va(&ctx_pair->host_ctx,
									HPT_PROTS_R,
									0,
									ptr_gpa,
									len - scanned,
									&cur_scan);
		if (scanned == 0) {
			/* First time assigning to ans */
			ans = ptr;
			ans_assigned = true;
		} else {
			/* Check that ptr and ans indicate continuous memory */
			HALT_ON_ERRORCOND(ans + scanned == ptr);
		}
		HALT_ON_ERRORCOND(cur_scan > 0);
		scanned += cur_scan;
	}
	HALT_ON_ERRORCOND(ans_assigned);
	return hva2spa(ans);
}

/*
 * Given a segment index, translate logical address to linear address.
 * seg: index of segment used by hardware.
 * addr: logical address as input, modified to linear address as output.
 * size: size of access.
 * mode: access mode (read / write / execute). Use HPT_PROT_*_MASK macros.
 * cpl: permission of access.
 *
 * Note: currently XMHF halts when guest makes an invalid access. Ideally XMHF
 * should inject corresponding exceptions like #GP(0).
 */
gva_t guestmem_desegment(VCPU * vcpu, cpu_segment_t seg, gva_t addr,
						 size_t size, hpt_prot_t mode, hptw_cpl_t cpl)
{
	/* Get segment fields from VMCS */
	ulong_t base;
	u32 access_rights;
	u32 limit;
	bool g64 = VCPU_g64(vcpu);
	switch (seg) {
	case CPU_SEG_ES:
		base = vcpu->vmcs.guest_ES_base;
		access_rights = vcpu->vmcs.guest_ES_access_rights;
		limit = vcpu->vmcs.guest_ES_limit;
		break;
	case CPU_SEG_CS:
		base = vcpu->vmcs.guest_CS_base;
		access_rights = vcpu->vmcs.guest_CS_access_rights;
		limit = vcpu->vmcs.guest_CS_limit;
		break;
	case CPU_SEG_SS:
		base = vcpu->vmcs.guest_SS_base;
		access_rights = vcpu->vmcs.guest_SS_access_rights;
		limit = vcpu->vmcs.guest_SS_limit;
		break;
	case CPU_SEG_DS:
		base = vcpu->vmcs.guest_DS_base;
		access_rights = vcpu->vmcs.guest_DS_access_rights;
		limit = vcpu->vmcs.guest_DS_limit;
		break;
	case CPU_SEG_FS:
		base = vcpu->vmcs.guest_FS_base;
		access_rights = vcpu->vmcs.guest_FS_access_rights;
		limit = vcpu->vmcs.guest_FS_limit;
		break;
	case CPU_SEG_GS:
		base = vcpu->vmcs.guest_GS_base;
		access_rights = vcpu->vmcs.guest_GS_access_rights;
		limit = vcpu->vmcs.guest_GS_limit;
		break;
	default:
		HALT_ON_ERRORCOND(0 && "Unexpected segment");
	}
	/*
	 * For 32-bit guest, check segment limit.
	 * For 64-bit guest, no limit check is performed (can even wrap around).
	 */
	if (!g64) {
		gva_t addr_max;
		HALT_ON_ERRORCOND(addr <= UINT_MAX);
		if (addr > UINT_MAX - size) {
			HALT_ON_ERRORCOND(0 && "Invalid access: logical address overflow");
		}
		addr_max = addr + size;
		if (addr_max >= limit) {
			HALT_ON_ERRORCOND(0 && "Invalid access: segment limit exceed");
		}
		if (base > UINT_MAX - addr_max) {
			HALT_ON_ERRORCOND(0 && "Not implemented: linear address overflow");
		}
	}
	/* Check access rights. Skip checking if amd64 SS/DS/ES/FS/GS. */
	if (seg == 1 || !g64) {
		/* Check Segment type */
		{
			hpt_prot_t supported_modes = HPT_PROTS_NONE;
			if ((access_rights & (1U << 3)) == 0) {
				/* type = 0 - 7, always has read */
				supported_modes |= HPT_PROT_READ_MASK;
				if (access_rights & (1U << 1)) {
					/* type = 2/3/6/7, has write */
					supported_modes |= HPT_PROT_WRITE_MASK;
				}
				if (access_rights & (1U << 2)) {
					/* type = 4 - 7, expand-down data segment not implemented */
					HALT_ON_ERRORCOND(0 && "Not implemented: expand-down");
				}
			} else {
				/* type = 8 - 15, always has execute */
				supported_modes |= HPT_PROT_EXEC_MASK;
				if (access_rights & (1U << 1)) {
					/* type = 10/11/14/15, has read */
					supported_modes |= HPT_PROT_READ_MASK;
				}
			}
			if ((supported_modes & mode) != mode) {
				HALT_ON_ERRORCOND(0 && "Invalid access: segment type");
			}
		}
		/* Check S - Descriptor type (0 = system; 1 = code or data) */
		HALT_ON_ERRORCOND((access_rights & (1U << 4)));
		/* Check DPL - Descriptor privilege level */
		{
			u32 dpl = (access_rights >> 5) & 0x3;
			if (dpl < (u32) cpl) {
				HALT_ON_ERRORCOND(0 && "Invalid access: DPL");
			}
		}
		/* Check P - Segment present */
		HALT_ON_ERRORCOND((access_rights & (1U << 7)));
	}
	return addr + base;
}
