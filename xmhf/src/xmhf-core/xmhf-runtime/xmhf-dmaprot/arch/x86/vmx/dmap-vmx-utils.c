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

// author: Miao Yu

#include <xmhf.h>
#include "dmap-vmx-internal.h"
#include "../../../iommu-pt.h"

extern void *vtd_cet; // cet holds all its structures in the memory linearly
extern struct dmap_vmx_cap g_vtd_cap_sagaw_mgaw_nd;

//! Return the spaddr of the VT-d page root
extern spa_t xmhf_dmaprot_arch_x86_vmx_get_eap_vtd_pt_root(void);

//------------------------------------------------------------------------------
// [TODO] Move util functions to a better place
void __iommu_flush_cpu_cache(VTD_DRHD* drhd, void *addr, int size)
{
    VTD_ECAP_REG ecap;
    _vtd_reg(drhd, VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&ecap.value);

	if (!vtd_ecap_c(drhd))
		xmhf_cpu_flush_cache_range(addr, size);
}


//! Invalidate the IOMMU PageTable corresponding to <pt_info>
void iommu_vmx_invalidate_pt(IOMMU_PT_INFO *pt_info)
{
	(void)pt_info;
	// [TODO] We should invalidate this page table only later
	xmhf_dmaprot_invalidate_cache();
}

/*static bool _iommu_destroy_1GB_pts(IOMMU_PT_INFO* pt_info, uint64_t pt_1GB_pte)
{

}

static void _iommu_map_1GB_page(IOMMU_PT_INFO* pt_info, void* upper_level_pts, gpa_t gpa, spa_t spa, uint32_t flags)
{
	uint32_t pt_1GB_index = 0;
	uint64_t old_1GB_pte = 0;

	pt_1GB_index = PAE_get_pdptindex(gpa);
	old_1GB_pte = ((uint64_t*)upper_level_pts)[pt_1GB_index];

	if(old_1GB_pte)
	{
		// We have set a PTE at this slot before, so we need to free the old
		// page structures first.

		// Step 1.

	}

	// Now we can safely assign the new PTE.
	((uint64_t*)upper_level_pts)[pt_1GB_index] = (spa & PAGE_MASK_1G) | (uint64_t)flags
				| (uint64_t)VTD_SUPERPAGE | (uint64_t) VTD_PRESENT;

	return true;
}

bool iommu_vmx_map(IOMMU_PT_INFO* pt_info, gpa_t start_gpa, spa_t start_spa, uint32_t num_pages, uint32_t flags)
{
	uint32_t remained_pages = num_pages;

	// Step 1. Allocate root page table if not exist
	if(!pt_info->pt_root)
	{
		pt_info->pt_root = xmhf_mm_alloc_page_with_record(pt_info->used_mem, 1);
		if(!pt_info->pt_root)
			return false;
	}

	// Step 2. Try mapping 1GB page frame


	return true;
}

bool iommu_vmx_map_batch(IOMMU_PT_INFO* pt_info, gpa_t start_gpa, spa_t* spas, uint32_t num_pages, uint32_t flags)
{

	// Step 1. Allocate root page table if not exist
	if(!pt_info->pt_root)
	{
		pt_info->pt_root = xmhf_mm_alloc_page_with_record(pt_info->used_mem, 1);
		if(!pt_info->pt_root)
			return false;
	}

	return true;
}*/

static void *__vtd_get_l1pt(IOMMU_PT_INFO *pt_info)
{
	// Step 1. Allocate root page table if not exist
	if (!pt_info->pt_root)
	{
		pt_info->pt_root = xmhf_mm_alloc_page_with_record(pt_info->used_mem, 1);
		if (!pt_info->pt_root)
			printf("[VTD-ERROR] No memory to allocate IOMMU top-level page struct!\n");
	}
	return pt_info->pt_root;
}

static void *__vtd_get_nextlvl_pt(IOMMU_PT_INFO *pt_info, void *pt_base, uint32_t pt_idx)
{
	uint64_t *p_pte = &((uint64_t *)pt_base)[pt_idx];
	void *nextlvl_pt = NULL;

	if (!*p_pte)
	{
		nextlvl_pt = xmhf_mm_alloc_page_with_record(pt_info->used_mem, 1);
		if (!nextlvl_pt)
		{
			printf("[VTD-ERROR] No memory to allocate next level IOMMU page struct!\n");
			return NULL;
		}

		*p_pte = (hva2spa(nextlvl_pt) & ADDR64_PAGE_MASK_4K) | ((uint64_t)VTD_READ | (uint64_t)VTD_WRITE | (uint64_t)VTD_EXECUTE);
		// xmhf_cpu_flush_cache_range(p_pte, sizeof(*p_pte));
	}

	return spa2hva(*p_pte & ADDR64_PAGE_MASK_4K);
}

bool iommu_vmx_map(IOMMU_PT_INFO *pt_info, gpa_t gpa, spa_t spa, uint32_t flags)
{
	void *pml4 = NULL, *pdp = NULL, *pd = NULL, *pt = NULL;
	uint32_t pml4_idx, pdp_idx, pd_idx, pt_idx = 0;

	pml4_idx = PAE_get_pml4tindex(gpa);
	pdp_idx = PAE_get_pdptindex(gpa);
	pd_idx = PAE_get_pdtindex(gpa);
	pt_idx = PAE_get_ptindex(gpa);

	if (g_vtd_cap_sagaw_mgaw_nd.sagaw & 0x4)
	{
		// Preferred to use 4-level PT
		// Step 1. Get PML4
		pml4 = __vtd_get_l1pt(pt_info);
		if (!pml4)
			return false;

		// Step 2. Get PDP
		pdp = __vtd_get_nextlvl_pt(pt_info, pml4, pml4_idx);
		if (!pdp)
			return false;
	}
	else if (g_vtd_cap_sagaw_mgaw_nd.sagaw & 0x2)
	{
		// Step 1. Get PDP
		pdp = __vtd_get_l1pt(pt_info);
		if (!pdp)
			return false;
	}
	else
	{
		// Unsupported IOMMU
		return false;
	}

	// Step 3. Get PD
	pd = __vtd_get_nextlvl_pt(pt_info, pdp, pdp_idx);
	if (!pd)
		return false;

	// Step 4. Get PT
	pt = __vtd_get_nextlvl_pt(pt_info, pd, pd_idx);
	if (!pt)
		return false;

	// Step 5. Map spa
	if (flags == DMA_ALLOW_ACCESS)
	{
		uint64_t* ptr = &((uint64_t *)pt)[pt_idx];
		*ptr = (spa & ADDR64_PAGE_MASK_4K) | ((uint64_t)VTD_READ | (uint64_t)VTD_WRITE | (uint64_t)VTD_EXECUTE);
		// xmhf_cpu_flush_cache_range(ptr, sizeof(*ptr));
	}
	else if (flags == DMA_DENY_ACCESS)
	{
		uint64_t* ptr = &((uint64_t *)pt)[pt_idx];
		*ptr = (spa & ADDR64_PAGE_MASK_4K) & (uint64_t)0xfffffffe; // remove the present bit
		// xmhf_cpu_flush_cache_range(ptr, sizeof(*ptr));
	}

	return true;
}

static bool __x86vmx_bind_cet(DEVICEDESC *device, iommu_pt_t pt_id, spa_t iommu_pt_root)
{
	uint64_t *value;

	// Update the CET
	value = (uint64_t *)((hva_t)vtd_cet + (device->bus * PAGE_SIZE_4K) +
						 (device->dev * PCI_FUNCTION_MAX + device->func) * 16);

	if (g_vtd_cap_sagaw_mgaw_nd.sagaw & 0x4)
	{
		// Preferred to use 4-level PT
		*(value + 1) = (uint64_t)0x0000000000000002ULL | (((uint64_t)pt_id & 0xFFFFULL) << 8); // domain:<pt_id>, aw=48 bits, 4 level pt
	}
	else if (g_vtd_cap_sagaw_mgaw_nd.sagaw & 0x2)
	{
		// If no 4-level PT, then try 3-level PT
		*(value + 1) = (uint64_t)0x0000000000000001ULL | (((uint64_t)pt_id & 0xFFFFULL) << 8); // domain:<pt_id>, aw=39 bits, 3 level pt
	}
	else
	{
		// Unsupported IOMMU
		return false;
	}

	*value = iommu_pt_root;
	*value |= 0x1ULL; // present, enable fault recording/processing, multilevel pt translation

	// xmhf_cpu_flush_cache_range(value, 16); // 128-bits
	return true;
}

bool iommu_vmx_bind_device(IOMMU_PT_INFO *pt_info, DEVICEDESC *device)
{
	return __x86vmx_bind_cet(device, pt_info->iommu_pt_id, hva2spa(pt_info->pt_root));
}

//! Bind the untrusted OS's default IOMMU PT to a device
bool iommu_vmx_unbind_device(DEVICEDESC *device)
{
	spa_t vtd_pt_root = xmhf_dmaprot_arch_x86_vmx_get_eap_vtd_pt_root();

	if (vtd_pt_root == INVALID_SPADDR)
		return false;

	return __x86vmx_bind_cet(device, UNTRUSTED_OS_IOMMU_PT_ID, vtd_pt_root);
}