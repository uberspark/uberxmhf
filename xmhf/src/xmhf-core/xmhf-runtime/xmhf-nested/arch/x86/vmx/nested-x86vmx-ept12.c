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
#include "nested-x86vmx-handler1.h"
#include "nested-x86vmx-vmcs12.h"

/*
 * Number of pages in page_pool in ept02_ctx_t.
 * This value is configured using --with-vmx-nested-ept02-page-pool-size.
 */
#define EPT02_PAGE_POOL_SIZE (__VMX_NESTED_EPT02_PAGE_POOL_SIZE__)

/*
 * For each CPU, information about all EPT12 -> EPT02 it caches.
 *
 * This variable can be asynchronously invalidated when another CPU's EPT01
 * changes. So use xmhf_nested_arch_x86vmx_block_ept02_flush() to protect it
 * when accessing.
 */
static ept02_cache_set_t ept02_cache[MAX_VCPU_ENTRIES];

/* Page pool for ept02_cache */
static u8 ept02_page_pool[MAX_VCPU_ENTRIES][VMX_NESTED_MAX_ACTIVE_EPT]
	[EPT02_PAGE_POOL_SIZE][PAGE_SIZE_4K]
	__attribute__((aligned(PAGE_SIZE_4K)));

/* Page allocation flags for ept02_cache */
static u8 ept02_page_alloc[MAX_VCPU_ENTRIES][VMX_NESTED_MAX_ACTIVE_EPT]
	[EPT02_PAGE_POOL_SIZE];

/* For each CPU, information about all VPID12 -> VPID02 it caches */
static vpid02_cache_set_t vpid02_cache[MAX_VCPU_ENTRIES];

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

static void *ept12_gzp(void *vctx, size_t alignment, size_t sz)
{
	(void)vctx;
	(void)alignment;
	(void)sz;
	HALT_ON_ERRORCOND(0 && "EPT12 should not call gzp()");
	return NULL;
}

static hpt_pa_t ept12_ptr2pa(void *vctx, void *ptr)
{
	(void)vctx;
	return hva2spa(ptr);
}

static void *ept12_pa2ptr(void *vctx, hpt_pa_t spa, size_t sz,
						  hpt_prot_t access_type, hptw_cpl_t cpl,
						  size_t *avail_sz)
{
	ept12_ctx_t *ctx = vctx;
	return hptw_checked_access_va(&ctx->ctx01.host_ctx,
								  access_type, cpl, spa, sz, avail_sz);
}

/*
 * Initialize the ept02_ctx_t structure in pointed to by ept02_ctx.
 * The current CPU is vcpu. The index of ept02_ctx in the CPU is index.
 */
static void ept02_ctx_init(VCPU * vcpu, u32 index, ept02_ctx_t * ept02_ctx)
{
	ept02_ctx->page_pool = ept02_page_pool[vcpu->idx][index];
	ept02_ctx->page_alloc = ept02_page_alloc[vcpu->idx][index];
	ept02_ctx->ctx.gzp = ept02_gzp;
	ept02_ctx->ctx.pa2ptr = ept02_pa2ptr;
	ept02_ctx->ctx.ptr2pa = ept02_ptr2pa;
	/* root_pa will be assigned to by ept02_ctx_reset() later */
	ept02_ctx->ctx.root_pa = 0;
	ept02_ctx->ctx.t = HPT_TYPE_EPT;
}

static void ept12_ctx_init(VCPU * vcpu, ept12_ctx_t * ept12_ctx)
{
	ept12_ctx->ctx.ptr2pa = ept12_ptr2pa;
	ept12_ctx->ctx.pa2ptr = ept12_pa2ptr;
	ept12_ctx->ctx.gzp = ept12_gzp;
	/* root_pa will be assigned to by ept12_ctx_update() later */
	ept12_ctx->ctx.root_pa = 0;
	ept12_ctx->ctx.t = HPT_TYPE_EPT;
	guestmem_init(vcpu, &ept12_ctx->ctx01);
}

/*
 * Handle EPT02 reset (e.g. due to EPT TLB flush).
 * Most fields in ept02_ctx_t do not change, so this function only updates the
 * fields that change. This function also flushes L0's EPT TLB.
 */
static void ept02_ctx_reset(ept02_ctx_t * ept02_ctx)
{
	u32 i;
	spa_t root_pa;
	for (i = 0; i < EPT02_PAGE_POOL_SIZE; i++) {
		ept02_ctx->page_alloc[i] = 0;
	}
	root_pa = hva2spa(ept02_gzp(&ept02_ctx->ctx, PAGE_SIZE_4K, PAGE_SIZE_4K));
	ept02_ctx->ctx.root_pa = root_pa;
	HALT_ON_ERRORCOND(__vmx_invept(VMX_INVEPT_SINGLECONTEXT,
								   root_pa | 0x1eULL));
}

/*
 * Most fields in ept12_ctx_t do not change. This function only updates the
 * fields that change. The fields are EPT12 (in argument) and EPT01 (from
 * vcpu).
 */
static void ept12_ctx_update(VCPU * vcpu, ept12_ctx_t * ept12_ctx, gpa_t ept12)
{
	ept12_ctx->ctx01.host_ctx.root_pa =
		hpt_eptp_get_address(HPT_TYPE_EPT, vcpu->vmcs.control_EPT_pointer);
	ept12_ctx->ctx.root_pa = ept12;
}

void xmhf_nested_arch_x86vmx_ept_init(VCPU * vcpu)
{
	ept02_cache_index_t index;
	ept02_cache_line_t *line;
	LRU_SET_INIT(&ept02_cache[vcpu->id]);
	LRU_FOREACH(index, line, &ept02_cache[vcpu->id]) {
		ept02_ctx_init(vcpu, index, &line->value.ept02_ctx);
		ept12_ctx_init(vcpu, &line->value.ept12_ctx);
	}
}

void xmhf_nested_arch_x86vmx_vpid_init(VCPU * vcpu)
{
	vpid02_cache_index_t index;
	vpid02_cache_line_t *line;
	LRU_SET_INIT(&vpid02_cache[vcpu->id]);
	LRU_FOREACH(index, line, &vpid02_cache[vcpu->id]) {
		/*
		 * VPID 0 is reserved by hardware, VPID 1 is for L1 guest. Ideally we
		 * map VPID01 = 1 - 65535 to VPID02 = 2 - 65535. However, here we only
		 * use VPID02 = 2 - (2 + VMX_NESTED_MAX_ACTIVE_VPID).
		 */
		HALT_ON_ERRORCOND(index + 2 > 0);
		line->value = index + 2;
	}
}

/*
 * Return whether bits 0 - 11 of eptp12 are legal for VMENTRY
 * When return true, ept_pml4t is the address of PML4T (page aligned)
 */
bool xmhf_nested_arch_x86vmx_check_ept_lower_bits(u64 eptp12, gpa_t * ept_pml4t)
{
	struct {
		union {
			struct {
				u8 mem_type:3;
				u8 walk_length:3;
				u8 access_dirty:1;
				u8 access_right_sup_shadow_stack:1;
				u8 reserved_11_8:4;
				u64 ept_pml4t:52;
			};
			u64 raw;
		};
	} guest_eptp;
	guest_eptp.raw = eptp12;
	if (guest_eptp.mem_type != HPT_PMT_WB) {
		return false;
	}
	if (guest_eptp.walk_length != 3) {
		return false;
	}
	/* Setting this bit to 1 is not supported yet. */
	if (guest_eptp.access_dirty) {
		return false;
	}
	/* Setting this bit to 1 is not supported yet. */
	if (guest_eptp.access_right_sup_shadow_stack) {
		return false;
	}
	if (guest_eptp.reserved_11_8) {
		return false;
	}
	*ept_pml4t = guest_eptp.ept_pml4t << PAGE_SHIFT_4K;
	return true;
}

/*
 * Invalidate ept12.
 *
 * Since this function accesses ept02_cache, callers of this function need to
 * call xmhf_nested_arch_x86vmx_block_ept02_flush() to prevent race conditions.
 */
void xmhf_nested_arch_x86vmx_invept_single_context(VCPU * vcpu, gpa_t ept12)
{
	ept02_cache_line_t *line;
	if (LRU_SET_INVALIDATE(&ept02_cache[vcpu->id], ept12, line)) {
		/*
		 * INVEPT will be executed in ept02_ctx_reset() when this EPT02 is used
		 * the next time.
		 */
	}
}

/*
 * Invalidate all EPTs
 *
 * Since this function accesses ept02_cache, callers of this function need to
 * call xmhf_nested_arch_x86vmx_block_ept02_flush() to prevent race conditions.
 */
void xmhf_nested_arch_x86vmx_invept_global(VCPU * vcpu)
{
	LRU_SET_INVALIDATE_ALL(&ept02_cache[vcpu->id]);
	/*
	 * INVEPT will be executed in ept02_ctx_reset() when the EPT02 is used the
	 * next time.
	 */
}

/*
 * Invalidate one address for one VPID. Return whether successful.
 * This function may fail by returning false when address is not canonical.
 */
bool xmhf_nested_arch_x86vmx_invvpid_indiv_addr(VCPU * vcpu, u16 vpid12,
												u64 address)
{
	vpid02_cache_line_t *line;
	ulong_t addr = address;

	/* Check whether the address is canonical */
	{
		u64 linaddrmask;
#ifdef __AMD64__
		u32 eax, ebx, ecx, edx;
		/* Check whether CPUID 0x80000008 is supported */
		cpuid(0x80000000U, &eax, &ebx, &ecx, &edx);
		HALT_ON_ERRORCOND(eax >= 0x80000008U);
		/* Compute paddrmask from CPUID.80000008H:EAX[15:8] (max lin addr) */
		cpuid(0x80000008U, &eax, &ebx, &ecx, &edx);
		eax >>= 8;
		eax &= 0xFFU;
		HALT_ON_ERRORCOND(eax >= 32 && eax < 64);
		linaddrmask = (1ULL << eax) - 0x1ULL;
#elif defined(__I386__)
		linaddrmask = (1ULL << 32) - 0x1ULL;
#else							/* !defined(__I386__) && !defined(__AMD64__) */
#error "Unsupported Arch"
#endif							/* !defined(__I386__) && !defined(__AMD64__) */
		if (address & ~linaddrmask) {
			return false;
		}
	}

	if (LRU_SET_FIND_IMMUTABLE(&vpid02_cache[vcpu->id], vpid12, line)) {
		u16 vpid02 = line->value;
		HALT_ON_ERRORCOND(__vmx_invvpid
						  (VMX_INVVPID_INDIVIDUALADDRESS, vpid02, addr));
	}
	return true;
}

/* Invalidate one VPID */
void xmhf_nested_arch_x86vmx_invvpid_single_ctx(VCPU * vcpu, u16 vpid12)
{
	vpid02_cache_line_t *line;
	if (LRU_SET_INVALIDATE(&vpid02_cache[vcpu->id], vpid12, line)) {
		/*
		 * INVVPID will be executed in xmhf_nested_arch_x86vmx_get_vpid02()
		 * when this VPID02 is used the next time.
		 */
	}
}

/* Invalidate all VPIDs */
void xmhf_nested_arch_x86vmx_invvpid_all_ctx(VCPU * vcpu)
{
	LRU_SET_INVALIDATE_ALL(&vpid02_cache[vcpu->id]);
	/*
	 * INVVPID will be executed in xmhf_nested_arch_x86vmx_get_vpid02() when
	 * the VPID02 is used the next time.
	 */
}

/* Invalidate one VPID except global transitions */
void xmhf_nested_arch_x86vmx_invvpid_single_ctx_global(VCPU * vcpu, u16 vpid12)
{
	vpid02_cache_line_t *line;
	if (LRU_SET_FIND_IMMUTABLE(&vpid02_cache[vcpu->id], vpid12, line)) {
		u16 vpid02 = line->value;
		HALT_ON_ERRORCOND(__vmx_invvpid
						  (VMX_INVVPID_SINGLECONTEXTGLOBAL, vpid02, 0));
	}
}

/*
 * Get pointer to EPT02 for current VMCS12. Will fill EPT02 as EPT violation
 * happens.
 *
 * Since this function accesses ept02_cache, callers of this function need to
 * call xmhf_nested_arch_x86vmx_block_ept02_flush() to prevent race conditions.
 */
spa_t xmhf_nested_arch_x86vmx_get_ept02(VCPU * vcpu, gpa_t ept12,
										bool *cache_hit,
										ept02_cache_line_t ** cache_line)
{
	bool hit;
	spa_t addr;
	ept02_cache_index_t index;
	ept02_cache_line_t *line = LRU_SET_FIND_EVICT(&ept02_cache[vcpu->id],
												  ept12, index, hit);
	(void)index;
	if (!hit) {
		ept02_ctx_reset(&line->value.ept02_ctx);
		ept12_ctx_update(vcpu, &line->value.ept12_ctx, ept12);
#ifdef __DEBUG_QEMU__
		/*
		 * Workaround a KVM bug:
		 * https://bugzilla.kernel.org/show_bug.cgi?id=216234
		 *
		 * Prevent EPT violations on REP INS instructions. Here we hardcode
		 * some known physical addresses to prevent EPT violations.
		 */
		{
			extern bool is_in_kvm;
			if (is_in_kvm) {
				u64 i;
				for (i = 0x68000ULL; i < 0x80000ULL; i += PA_PAGE_SIZE_4K) {
					xmhf_nested_arch_x86vmx_hardcode_ept(vcpu, line, i);
				}
			}
		}
#endif							/* !__DEBUG_QEMU__ */
#ifdef __DEBUG_EVENT_LOGGER__
		xmhf_dbg_log_event(vcpu, 1, XMHF_DBG_EVENTLOG_ept02_miss, &ept12);
#endif							/* __DEBUG_EVENT_LOGGER__ */
		if (0) {
			printf("CPU(0x%02x): EPT cache miss 0x%08llx\n", vcpu->id, ept12);
		}
	}
	*cache_hit = hit;
	*cache_line = line;
	addr = line->value.ept02_ctx.ctx.root_pa;
	return addr | 0x1e;			// TODO: remove magic number
}

/* Get value of a VPID02 for current VPID12 */
u16 xmhf_nested_arch_x86vmx_get_vpid02(VCPU * vcpu, u16 vpid12, bool *cache_hit)
{
	bool hit;
	vpid02_cache_index_t index;
	vpid02_cache_line_t *line = LRU_SET_FIND_EVICT(&vpid02_cache[vcpu->id],
												   vpid12, index, hit);
	(void)index;
	if (!hit) {
		HALT_ON_ERRORCOND(__vmx_invvpid
						  (VMX_INVVPID_SINGLECONTEXT, line->value, 0));
	}
	*cache_hit = hit;
	return vpid12;
}

/*
 * Handle an EPT exit received by L0 when running L2. There are 4 cases,
 * represented by 4 different return values.
 * * VMX_NESTED_EPT02_CACHEMISS: L2 accesses legitimate memory, but L0 has not
 *   processed the EPT entry in L1 yet. XMHF should add EPT entry to EPT02 and
 *   continue running L2.
 * * VMX_NESTED_EPT12_VIOLATION: L2 accesses memory not in EPT12. XMHF should
 *   forward EPT violation to L1.
 * * VMX_NESTED_EPT01_VIOLATION: L2 accesses memory not valid in EPT01 (L1 sets
 *   up EPT that accesses illegal memory). XMHF should halt for security.
 * * VMX_NESTED_EPT12_MISCONFIG: The EPT12 for L2's memory access is
 *   misconfigured. XMHF should return EPT misconfiguration exit to L1.
 */
int xmhf_nested_arch_x86vmx_handle_ept02_exit(VCPU * vcpu,
											  ept02_cache_line_t * cache_line,
											  u64 guest2_paddr,
											  ulong_t qualification)
{
	ept12_ctx_t *ept12_ctx;
	ept02_ctx_t *ept02_ctx;
	gpa_t guest1_paddr;
	spa_t xmhf_paddr;
	hpt_pmeo_t pmeo12;
	hpt_pmeo_t pmeo01;
	hpt_pmeo_t pmeo02;
	hpt_prot_t access_type;

	HALT_ON_ERRORCOND(cache_line->valid);
	ept12_ctx = &cache_line->value.ept12_ctx;
	ept02_ctx = &cache_line->value.ept02_ctx;
	access_type = 0;
	if (qualification & (1UL << 0)) {
		access_type |= HPT_PROT_READ_MASK;
	}
	if (qualification & (1UL << 1)) {
		access_type |= HPT_PROT_WRITE_MASK;
	}
	if (qualification & (1UL << 2)) {
		access_type |= HPT_PROT_EXEC_MASK;
	}
	HALT_ON_ERRORCOND(access_type);

	/* Get the entry in EPT12 and the L1 paddr that is to be accessed */
	if (hptw_checked_get_pmeo(&pmeo12, &ept12_ctx->ctx, access_type, 0,
							  guest2_paddr) != 0) {
		return VMX_NESTED_EPT12_VIOLATION;
	}
	guest1_paddr = hpt_pmeo_va_to_pa(&pmeo12, guest2_paddr);

	/*
	 * Check for EPT misconfiguration. TODO: only R=0 && W=1 is checked here,
	 * but there are other cases to be checked. See SDM.
	 */
	if (!(pmeo12.pme & HPT_PROT_READ_MASK)) {
		if (pmeo12.pme & HPT_PROT_WRITE_MASK) {
			return VMX_NESTED_EPT12_MISCONFIG;
		} else {
			/* It must be R=0 && X=1, which is misconfig if not supported */
			HALT_ON_ERRORCOND(0 && "Likely unimplemented EPT misconfig");
		}
	}

	/* Get the entry in EPT01 for the L1 paddr */
	if (hptw_checked_get_pmeo(&pmeo01, &ept12_ctx->ctx01.host_ctx, access_type,
							  0, guest1_paddr) != 0) {
		return VMX_NESTED_EPT01_VIOLATION;
	}
	xmhf_paddr = hpt_pmeo_va_to_pa(&pmeo01, guest1_paddr);

	/* Construct page map entry for EPT02 */
	pmeo02.pme = 0;
	pmeo02.t = HPT_TYPE_EPT;
	pmeo02.lvl = pmeo12.lvl < pmeo01.lvl ? pmeo12.lvl : pmeo01.lvl;
	hpt_pmeo_set_page(&pmeo02, true);
	hpt_pmeo_set_address(&pmeo02, xmhf_paddr);
	{
		hpt_prot_t prot01 = hpt_pmeo_getprot(&pmeo01);
		hpt_prot_t prot12 = hpt_pmeo_getprot(&pmeo12);
		hpt_pmeo_setprot(&pmeo02, prot01 & prot12);
	}
	{
		/*
		 * MTRRs do not affect guest memory type, so EPT02's memory type is
		 * determined only by EPT12. EPT01 has nothing to do with EPT02's
		 * memory type.
		 */
		hpt_pmeo_setcache(&pmeo02, hpt_pmeo_getcache(&pmeo12));
	}
	{
		bool user01 = hpt_pmeo_getuser(&pmeo01);
		bool user12 = hpt_pmeo_getuser(&pmeo12);
		hpt_pmeo_setuser(&pmeo02, user01 && user12);
	}

	/* Put page map entry into EPT02 */
	if (hptw_insert_pmeo_alloc(&ept02_ctx->ctx, &pmeo02, guest2_paddr)) {
		{
			gpa_t ept12 = ept12_ctx->ctx.root_pa;
#ifdef __DEBUG_EVENT_LOGGER__
			xmhf_dbg_log_event(vcpu, 1, XMHF_DBG_EVENTLOG_ept02_full, &ept12);
#endif							/* __DEBUG_EVENT_LOGGER__ */
			if (0) {
				printf("CPU(0x%02x): EPT02 full 0x%08llx\n", vcpu->id, ept12);
			}
		}
		ept02_ctx_reset(ept02_ctx);
		HALT_ON_ERRORCOND(hptw_insert_pmeo_alloc(&ept02_ctx->ctx, &pmeo02,
												 guest2_paddr) == 0);
	}
	if (0) {
		printf("CPU(0x%02x): EPT: L2=0x%08llx L1=0x%08llx L0=0x%08llx\n",
			   vcpu->id, guest2_paddr, guest1_paddr, xmhf_paddr);
	}
	return VMX_NESTED_EPT02_CACHEMISS;
}

/*
 * This function is what xmhf_nested_arch_x86vmx_flush_ept02() does when no
 * blocking occurs.
 */
static void xmhf_nested_arch_x86vmx_flush_ept02_effect(VCPU * vcpu)
{
	LRU_SET_INVALIDATE_ALL(&ept02_cache[vcpu->id]);
	xmhf_nested_arch_x86vmx_clear_all_vmcs12_ept02(vcpu);

	/*
	 * If L2 (nested guest) is running, the VMCS02 fields that depend on EPT01
	 * need to be recomputed (e.g. fields with flag FIELD_PROP_GPADDR).
	 *
	 * If the guest is using EPT02, the flushing above would make
	 * vmcs12_info->guest_ept_cache_line invalid. We need to create new EPT02
	 * to make it valid. This also applies to the EPT pointer in VMCS02.
	 */
	if (vcpu->vmx_nested_operation_mode == NESTED_VMX_MODE_NONROOT) {
		vmcs12_info_t *vmcs12_info;
		vmcs12_info = xmhf_nested_arch_x86vmx_find_current_vmcs12(vcpu);
		/* Re-compute VMCS fields that depend on EPT01 */
		xmhf_nested_arch_x86vmx_rewalk_ept01(vcpu, vmcs12_info);
	}
}

/*
 * Invalidate all EPT02 on the current CPU (e.g. due to change in EPT01).
 * This function is designed to be called in NMI handlers. Its effect will be
 * delayed until call to xmhf_nested_arch_x86vmx_unblock_ept02_flush() if
 * xmhf_nested_arch_x86vmx_block_ept02_flush() has been called.
 */
void xmhf_nested_arch_x86vmx_flush_ept02(VCPU * vcpu)
{
	if (vcpu->vmx_nested_ept02_flush_disable) {
		vcpu->vmx_nested_ept02_flush_visited = true;
	} else {
		xmhf_nested_arch_x86vmx_flush_ept02_effect(vcpu);
	}
}

/* Block the effect of xmhf_nested_arch_x86vmx_flush_ept02() */
void xmhf_nested_arch_x86vmx_block_ept02_flush(VCPU * vcpu)
{
	HALT_ON_ERRORCOND(!vcpu->vmx_nested_ept02_flush_disable);
	vcpu->vmx_nested_ept02_flush_disable = true;
}

/* Unblock the effect of xmhf_nested_arch_x86vmx_flush_ept02() */
void xmhf_nested_arch_x86vmx_unblock_ept02_flush(VCPU * vcpu)
{
	HALT_ON_ERRORCOND(vcpu->vmx_nested_ept02_flush_disable);
	vcpu->vmx_nested_ept02_flush_disable = false;
	while (vcpu->vmx_nested_ept02_flush_visited) {
		vcpu->vmx_nested_ept02_flush_visited = false;
		vcpu->vmx_nested_ept02_flush_disable = true;
		xmhf_nested_arch_x86vmx_flush_ept02_effect(vcpu);
		vcpu->vmx_nested_ept02_flush_disable = false;
	}
}

#ifdef __DEBUG_QEMU__
void xmhf_nested_arch_x86vmx_hardcode_ept(VCPU * vcpu,
										  ept02_cache_line_t * cache_line,
										  u64 guest2_paddr)
{
	switch (xmhf_nested_arch_x86vmx_handle_ept02_exit(vcpu, cache_line,
													  guest2_paddr,
													  HPT_PROTS_RW)) {
	case VMX_NESTED_EPT02_CACHEMISS:
		/* Everything is well */
		break;
	case VMX_NESTED_EPT01_VIOLATION:
		HALT_ON_ERRORCOND(0 && "Guest EPT will access illegal memory");
		break;
	case VMX_NESTED_EPT12_VIOLATION:
		/*
		 * Guest hypervisor has not set up EPT for guest2_paddr. This should
		 * result in an EPT violation in the future. However, if KVM
		 * is buggy, we may not be able to workaround easily.
		 */
		printf("CPU(0x%02x): Warning: 0x%016llx not in guest EPT\n", vcpu->id,
			   guest2_paddr);
		break;
	case VMX_NESTED_EPT12_MISCONFIG:
		/*
		 * Guest hypervisor will encounter EPT misconfiguration. For now ignore
		 * the error.
		 */
		printf("CPU(0x%02x): Warning: 0x%016llx misconfigured guest EPT\n",
			   vcpu->id, guest2_paddr);
		break;
	default:
		HALT_ON_ERRORCOND(0 && "Unknown status");
		break;
	}
}
#endif							/* !__DEBUG_QEMU__ */
