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

// EMHF DMA protection component implementation for x86 VMX
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include "dmap-vmx-internal.h"
#include "dmap-vmx-quirks.h"

void *vtd_cet = NULL; // cet holds all its structures in the memory linearly

//==============================================================================
// local (static) variables and function definitions
//==============================================================================

// DMA Remapping Hardware Unit Definitions
static VTD_DRHD vtd_drhd[VTD_MAX_DRHD];
static u32 vtd_num_drhd = 0; // total number of DMAR h/w units

// VT-d 3-level/4-level DMA protection page table data structure addresses
static spa_t l_vtd_pml4t_paddr = 0;
static hva_t l_vtd_pml4t_vaddr = 0;
static spa_t l_vtd_pdpt_paddr = 0;
static hva_t l_vtd_pdpt_vaddr = 0;
static spa_t l_vtd_pdts_paddr = 0;
static hva_t l_vtd_pdts_vaddr = 0;
static spa_t l_vtd_pts_paddr = 0;
static hva_t l_vtd_pts_vaddr = 0;

//------------------------------------------------------------------------------
// setup VT-d DMA protection page tables
static bool _vtd_setuppagetables(spa_t vtd_pml4t_paddr, hva_t vtd_pml4t_vaddr,
                                 spa_t vtd_pdpt_paddr, hva_t vtd_pdpt_vaddr,
                                 spa_t vtd_pdts_paddr, hva_t vtd_pdts_vaddr,
                                 spa_t vtd_pts_paddr, hva_t vtd_pts_vaddr,
                                 spa_t machine_low_spa, spa_t machine_high_spa)
{
    spa_t pml4tphysaddr, pdptphysaddr, pdtphysaddr, ptphysaddr;
    u32 i, j, k;
    pml4t_t pml4t;
    pdpt_t pdpt;
    pdt_t pdt;
    pt_t pt;
    uintptr_t physaddr = 0;
    spa_t m_low_spa = PA_PAGE_ALIGN_1G(machine_low_spa);
    spa_t m_high_spa = PA_PAGE_ALIGN_UP_1G(machine_high_spa);
    u32 num_1G_entries = (m_high_spa - (u64)m_low_spa) >> PAGE_SHIFT_1G;

    pml4tphysaddr = vtd_pml4t_paddr;
    pdptphysaddr = vtd_pdpt_paddr;
    pdtphysaddr = vtd_pdts_paddr;
    ptphysaddr = vtd_pts_paddr;

    // ensure PDPT, PDTs and PTs are all page-aligned
    HALT_ON_ERRORCOND(PA_PAGE_ALIGNED_4K(pml4tphysaddr) && PA_PAGE_ALIGNED_4K(pdptphysaddr) && 
        PA_PAGE_ALIGNED_4K(pdtphysaddr) && PA_PAGE_ALIGNED_4K(ptphysaddr));

    // initialize our local variables
    l_vtd_pml4t_paddr = vtd_pml4t_paddr;
    l_vtd_pml4t_vaddr = vtd_pml4t_vaddr;
    l_vtd_pdpt_paddr = vtd_pdpt_paddr;
    l_vtd_pdpt_vaddr = vtd_pdpt_vaddr;
    l_vtd_pdts_paddr = vtd_pdts_paddr;
    l_vtd_pdts_vaddr = vtd_pdts_vaddr;
    l_vtd_pts_paddr = vtd_pts_paddr;
    l_vtd_pts_vaddr = vtd_pts_vaddr;

    // setup pml4t
    // The VT-d page table created here is a partial one. If 4-level PT is used, then there is only one PML4 entry instead
    // of 512 entries. This is sufficient because the lower 3-level PT covers 0 - 512GB physical memory space
    pml4t = (pml4t_t)vtd_pml4t_vaddr;
    pml4t[0] = (u64)(pdptphysaddr + (0 * PAGE_SIZE_4K));
    pml4t[0] |= ((u64)VTD_READ | (u64)VTD_WRITE | (u64)VTD_EXECUTE);

    // setup pdpt, pdt and pt
    // initially set the entire spaddr space [m_low_spa, m_high_spa) as DMA read/write capable
    pdpt = (pdpt_t)vtd_pdpt_vaddr;

    for (i = 0; i < num_1G_entries; i++) // DMAPROT_VMX_P4L_NPDT
    {
        pdpt[i] = (u64)(pdtphysaddr + (i * PAGE_SIZE_4K));
        pdpt[i] |= ((u64)VTD_READ | (u64)VTD_WRITE | (u64)VTD_EXECUTE);

        pdt = (pdt_t)(vtd_pdts_vaddr + (i * PAGE_SIZE_4K));
        for (j = 0; j < PAE_PTRS_PER_PDT; j++)
        {
            pdt[j] = (u64)(ptphysaddr + (i * PAGE_SIZE_4K * PAE_PTRS_PER_PDT) + (j * PAGE_SIZE_4K));
            pdt[j] |= ((u64)VTD_READ | (u64)VTD_WRITE | (u64)VTD_EXECUTE);

            pt = (pt_t)(vtd_pts_vaddr + (i * PAGE_SIZE_4K * PAE_PTRS_PER_PDT) + (j * PAGE_SIZE_4K));
            for (k = 0; k < PAE_PTRS_PER_PT; k++)
            {
                pt[k] = (u64)physaddr;
                pt[k] |= ((u64)VTD_READ | (u64)VTD_WRITE | (u64)VTD_EXECUTE);
                physaddr += PAGE_SIZE_4K;
            }
        }
    }

    return true;
}

//------------------------------------------------------------------------------
// set VT-d RET and CET tables
// we have 1 root entry table (RET) of 4kb, each root entry (RE) is 128-bits
// which gives us 256 entries in the RET, each corresponding to a PCI bus num.
//(0-255)
// each RE points to a context entry table (CET) of 4kb, each context entry (CE)
// is 128-bits which gives us 256 entries in the CET, accounting for 32 devices
// with 8 functions each as per the PCI spec.
// each CE points to a PDPT type paging structure.
// in our implementation, every CE will point to a single PDPT type paging
// structure for the whole system
static bool _vtd_setupRETCET(struct dmap_vmx_cap *vtd_cap,
                             spa_t vtd_pml4t_paddr, spa_t vtd_pdpt_paddr,
                             spa_t vtd_ret_paddr, hva_t vtd_ret_vaddr,
                             spa_t vtd_cet_paddr, hva_t vtd_cet_vaddr)
{
    spa_t retphysaddr, cetphysaddr;
    u32 i, j;
    u64 *value;

    // Sanity checks
    if (!vtd_cap)
        return false;

    retphysaddr = vtd_ret_paddr;
    (void)retphysaddr;
    cetphysaddr = vtd_cet_paddr;

    // sanity check that pdpt base address is page-aligned
    HALT_ON_ERRORCOND(PA_PAGE_ALIGNED_4K(vtd_pml4t_paddr) && PA_PAGE_ALIGNED_4K(vtd_pdpt_paddr));

    // initialize RET
    for (i = 0; i < PCI_BUS_MAX; i++)
    {
        value = (u64 *)(vtd_ret_vaddr + (i * 16));
        *(value + 1) = (u64)0x0ULL;
        *value = (u64)(cetphysaddr + (i * PAGE_SIZE_4K));

        // sanity check that CET is page aligned
        HALT_ON_ERRORCOND(!(*value & 0x0000000000000FFFULL));

        // set it to present
        *value |= 0x1ULL;
    }

    // initialize CET
    for (i = 0; i < PCI_BUS_MAX; i++)
    {
        for (j = 0; j < (PCI_DEVICE_MAX * PCI_FUNCTION_MAX); j++)
        {
            value = (u64 *)(vtd_cet_vaddr + (i * PAGE_SIZE_4K) + (j * 16));

            if (vtd_cap->sagaw & 0x4)
            {
                // Preferred to use 4-level PT
                *(value + 1) = (u64)0x0000000000000102ULL; // domain:1, aw=48 bits, 4 level pt
                *value = vtd_pml4t_paddr;
            }
            else if (vtd_cap->sagaw & 0x2)
            {
                // If no 4-level PT, then try 3-level PT
                *(value + 1) = (u64)0x0000000000000101ULL; // domain:1, aw=39 bits, 3 level pt
                *value = vtd_pdpt_paddr;
            }
            else
            {
                // Unsupported IOMMU
                return false;
            }

            *value |= 0x1ULL; // present, enable fault recording/processing, multilevel pt translation
        }
    }

    return true;
}

// initialize VMX EAP a.k.a VT-d
// returns 1 if all went well, else 0
// if input parameter bootstrap is 1 then we perform minimal translation
// structure initialization, else we do the full DMA translation structure
// initialization at a page-granularity
static u32 vmx_eap_initialize(
    spa_t vtd_pml4t_paddr, hva_t vtd_pml4t_vaddr,
    spa_t vtd_pdpt_paddr, hva_t vtd_pdpt_vaddr,
    spa_t vtd_pdts_paddr, hva_t vtd_pdts_vaddr,
    spa_t vtd_pts_paddr, hva_t vtd_pts_vaddr,
    spa_t vtd_ret_paddr, hva_t vtd_ret_vaddr,
    spa_t vtd_cet_paddr, hva_t vtd_cet_vaddr)
{
    ACPI_RSDP rsdp;
    ACPI_RSDT rsdt;
    u32 num_rsdtentries;
    uintptr_t rsdtentries[ACPI_MAX_RSDT_ENTRIES];
    uintptr_t status;
    bool status2 = false;
    VTD_DMAR dmar;
    u32 i, dmarfound;
    spa_t dmaraddrphys, remappingstructuresaddrphys;
    spa_t rsdt_xsdt_spaddr = INVALID_SPADDR;
    hva_t rsdt_xsdt_vaddr = INVALID_VADDR;

#ifndef __XMHF_VERIFICATION__
    // zero out rsdp and rsdt structures
    memset(&rsdp, 0, sizeof(ACPI_RSDP));
    memset(&rsdt, 0, sizeof(ACPI_RSDT));
    memset(&g_vtd_cap_sagaw_mgaw_nd, 0, sizeof(struct dmap_vmx_cap));

    // get ACPI RSDP
    //  [TODO] Unify the name of <xmhf_baseplatform_arch_x86_acpi_getRSDP> and <xmhf_baseplatform_arch_x86_acpi_getRSDP>, and then remove the following #ifdef
    status = xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp);
    HALT_ON_ERRORCOND(status != 0); // we need a valid RSDP to proceed
    printf("%s: RSDP at %lx\n", __FUNCTION__, status);

    // [Superymk] Use RSDT if it is ACPI v1, or use XSDT addr if it is ACPI v2
    if (rsdp.revision == 0) // ACPI v1
    {
        printf("%s: ACPI v1\n", __FUNCTION__);
        rsdt_xsdt_spaddr = rsdp.rsdtaddress;
    }
    else if (rsdp.revision == 0x2) // ACPI v2
    {
        printf("%s: ACPI v2\n", __FUNCTION__);
        rsdt_xsdt_spaddr = (spa_t)rsdp.xsdtaddress;
    }
    else // Unrecognized ACPI version
    {
        printf("%s: ACPI unsupported version!\n", __FUNCTION__);
        return 0;
    }

    // grab ACPI RSDT
    // Note: in i386, <rsdt_xsdt_spaddr> should be in lower 4GB. So the conversion to vaddr is fine.
    rsdt_xsdt_vaddr = (hva_t)rsdt_xsdt_spaddr;

    xmhf_baseplatform_arch_flat_copy((u8 *)&rsdt, (u8 *)rsdt_xsdt_vaddr, sizeof(ACPI_RSDT));
    printf("%s: RSDT at %lx, len=%u bytes, hdrlen=%u bytes\n",
           __FUNCTION__, rsdt_xsdt_vaddr, rsdt.length, sizeof(ACPI_RSDT));

    // get the RSDT entry list
    num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT)) / sizeof(u32);
    HALT_ON_ERRORCOND(num_rsdtentries < ACPI_MAX_RSDT_ENTRIES);
    xmhf_baseplatform_arch_flat_copy((u8 *)&rsdtentries, (u8 *)(rsdt_xsdt_vaddr + sizeof(ACPI_RSDT)),
                                     sizeof(rsdtentries[0]) * num_rsdtentries);
    printf("%s: RSDT entry list at %lx, len=%u\n", __FUNCTION__,
           (rsdt_xsdt_vaddr + sizeof(ACPI_RSDT)), num_rsdtentries);

    // find the VT-d DMAR table in the list (if any)
    for (i = 0; i < num_rsdtentries; i++)
    {
        xmhf_baseplatform_arch_flat_copy((u8 *)&dmar, (u8 *)rsdtentries[i], sizeof(VTD_DMAR));
        if (dmar.signature == VTD_DMAR_SIGNATURE)
        {
            dmarfound = 1;
            break;
        }
    }

    // if no DMAR table, bail out
    if (!dmarfound)
        return 0;

    dmaraddrphys = rsdtentries[i]; // DMAR table physical memory address;
    printf("%s: DMAR at %llx\n", __FUNCTION__, dmaraddrphys);

    i = 0;
    remappingstructuresaddrphys = dmaraddrphys + sizeof(VTD_DMAR);
    printf("%s: remapping structures at %llx\n", __FUNCTION__, remappingstructuresaddrphys);

    while (i < (dmar.length - sizeof(VTD_DMAR)))
    {
        u16 type, length;
        hva_t remappingstructures_vaddr = (hva_t)remappingstructuresaddrphys;

        xmhf_baseplatform_arch_flat_copy((u8 *)&type, (u8 *)(remappingstructures_vaddr + i), sizeof(u16));
        xmhf_baseplatform_arch_flat_copy((u8 *)&length, (u8 *)(remappingstructures_vaddr + i + sizeof(u16)), sizeof(u16));

        switch (type)
        {
        case 0: // DRHD
            printf("DRHD at %lx, len=%u bytes\n", (remappingstructures_vaddr + i), length);
            HALT_ON_ERRORCOND(vtd_num_drhd < VTD_MAX_DRHD);
            xmhf_baseplatform_arch_flat_copy((u8 *)&vtd_drhd[vtd_num_drhd], (u8 *)(remappingstructures_vaddr + i), length);
            vtd_num_drhd++;
            i += (u32)length;
            break;

        default: // unknown type, we skip this
            i += (u32)length;
            break;
        }
    }

    printf("%s: total DRHDs detected= %u units\n", __FUNCTION__, vtd_num_drhd);

    // be a little verbose about what we found
    printf("%s: DMAR Devices:\n", __FUNCTION__);
    FOREACH_S(i, vtd_num_drhd, VTD_MAX_DRHD, 0, 1)
    {
        VTD_CAP_REG cap;
        VTD_ECAP_REG ecap;
        printf("	Device %u on PCI seg %04x; base=0x%016llx\n", i,
               vtd_drhd[i].pcisegment, vtd_drhd[i].regbaseaddr);
        _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);
        printf("		cap=0x%016llx\n", (u64)cap.value);
        _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&ecap.value);
        printf("		ecap=0x%016llx\n", (u64)ecap.value);
    }

    // Verify VT-d capabilities
    status2 = _vtd_verify_cap(vtd_drhd, vtd_num_drhd, &g_vtd_cap_sagaw_mgaw_nd);
    if (!status2)
    {
        printf("%s: verify VT-d units' capabilities error! Halting!\n", __FUNCTION__);
        HALT();
    }

    // initialize VT-d page tables (not done if we are bootstrapping)
    {
        spa_t machine_low_spa = INVALID_SPADDR;
        spa_t machine_high_spa = INVALID_SPADDR;
        u64 phy_space_size = 0;

        // Get the base and limit used system physical address from the E820 map
        status2 = xmhf_get_machine_paddr_range(&machine_low_spa, &machine_high_spa);
        if (!status2)
        {
            printf("%s: Get system physical address range error! Halting!\n", __FUNCTION__);
            HALT();
        }

        // Check: The base and limit of the physical address space must <= DMAPROT_PHY_ADDR_SPACE_SIZE
        phy_space_size = machine_high_spa - machine_low_spa;
        if(phy_space_size > DMAPROT_PHY_ADDR_SPACE_SIZE)
        {
            printf("%s: Too large system physical address! Found space size:%llX. Halting!\n", __FUNCTION__, phy_space_size);
            HALT();
        }

        status2 = _vtd_setuppagetables(vtd_pml4t_paddr, vtd_pml4t_vaddr, vtd_pdpt_paddr, vtd_pdpt_vaddr,
                                       vtd_pdts_paddr, vtd_pdts_vaddr, vtd_pts_paddr, vtd_pts_vaddr, machine_low_spa, machine_high_spa);
        if (!status2)
        {
            printf("%s: setup VT-d page tables (pdpt=%llx, pdts=%llx, pts=%llx) error! Halting!\n", __FUNCTION__, vtd_pdpt_paddr, vtd_pdts_paddr, vtd_pts_paddr);
            HALT();
        }

        printf("%s: setup VT-d page tables (pdpt=%llx, pdts=%llx, pts=%llx).\n", __FUNCTION__, vtd_pdpt_paddr, vtd_pdts_paddr, vtd_pts_paddr);
    }

    // initialize VT-d RET and CET
    {
        status2 = _vtd_setupRETCET(&g_vtd_cap_sagaw_mgaw_nd, vtd_pml4t_paddr, vtd_pdpt_paddr, vtd_ret_paddr, vtd_ret_vaddr, vtd_cet_paddr, vtd_cet_vaddr);
        if (!status2)
        {
            printf("%s: setup VT-d RET (%llx) and CET (%llx) error! Halting!\n", __FUNCTION__, vtd_ret_paddr, vtd_cet_paddr);
            HALT();
        }

        printf("%s: setup VT-d RET (%llx) and CET (%llx).\n", __FUNCTION__, vtd_ret_paddr, vtd_cet_paddr);
    }

#endif //__XMHF_VERIFICATION__

    // zap VT-d presence in ACPI table...
    // TODO: we need to be a little elegant here. eventually need to setup
    // EPT/NPTs such that the DMAR pages are unmapped for the guest
    xmhf_baseplatform_arch_flat_writeu32(dmaraddrphys, 0UL);

    // Flush CPU cache
    wbinvd();

    // success
    printf("%s: success, leaving...\n", __FUNCTION__);

    return 1;
}

////////////////////////////////////////////////////////////////////////
// Within DMAP component

//! Return the spaddr of the VT-d page root
//! [NOTE] This function is used by dmap module only, and hence is not exported.
spa_t xmhf_dmaprot_arch_x86_vmx_get_eap_vtd_pt_root(void)
{
    spa_t result = INVALID_SPADDR;

    if (g_vtd_cap_sagaw_mgaw_nd.sagaw & 0x4)
    {
        // 4-level PT
        result = l_vtd_pml4t_paddr;
    }
    else if (g_vtd_cap_sagaw_mgaw_nd.sagaw & 0x2)
    {
        // VT-d uses 3-level PT
        result = l_vtd_pdpt_paddr;
    }
    else
    {
        // Unsupported IOMMU
        result = INVALID_SPADDR;
    }

    return result;
}




////////////////////////////////////////////////////////////////////////
// GLOBALS

u32 xmhf_dmaprot_arch_x86_vmx_enable(spa_t protectedbuffer_paddr,
                                         hva_t protectedbuffer_vaddr, size_t protectedbuffer_size)
{
    u32 i = 0;
    // Vt-d bootstrap has minimal DMA translation setup and protects entire
    // system memory. Relax this by instantiating a complete DMA translation
    // structure at a page granularity and protecting only the SL and Runtime
    uintptr_t vmx_eap_vtd_pml4t_paddr;
    uintptr_t vmx_eap_vtd_pdpt_paddr;
    uintptr_t vmx_eap_vtd_pdts_paddr;
    uintptr_t vmx_eap_vtd_pts_paddr;
    uintptr_t vmx_eap_vtd_ret_paddr;

    (void)protectedbuffer_vaddr;
    HALT_ON_ERRORCOND(protectedbuffer_size >= SIZE_G_RNTM_DMAPROT_BUFFER);

    // The VT-d page table created here is a partial one. If 4-level PT is used, then there is only one PML4 entry instead
    // of 512 entries. This is sufficient because the lower 3-level PT covers 0 - 512GB physical memory space
    vmx_eap_vtd_pml4t_paddr = protectedbuffer_paddr;
    vmx_eap_vtd_pdpt_paddr = vmx_eap_vtd_pml4t_paddr + PAGE_SIZE_4K;
    vmx_eap_vtd_pdts_paddr = vmx_eap_vtd_pdpt_paddr + PAGE_SIZE_4K;
    vmx_eap_vtd_pts_paddr = vmx_eap_vtd_pdts_paddr + (PAGE_SIZE_4K * DMAPROT_VMX_P4L_NPDT);
    vmx_eap_vtd_ret_paddr = vmx_eap_vtd_pts_paddr + (PAGE_SIZE_4K * DMAPROT_VMX_P4L_NPDT * PAE_PTRS_PER_PDT);

    
#ifndef __XMHF_VERIFICATION__
    // initialize all DRHD units
    FOREACH_S(i, vtd_num_drhd, VTD_MAX_DRHD, 0, 1)
    {
        printf("%s: initializing DRHD unit %u...\n", __FUNCTION__, i);
        _vtd_drhd_initialize_runtime(&vtd_drhd[i], vmx_eap_vtd_ret_paddr);
    }
#else
    printf("%s: initializing DRHD unit %u...\n", __FUNCTION__, i);
    _vtd_drhd_initialize_runtime(&vtd_drhd[0], vmx_eap_vtd_ret_paddr);
#endif

    // Clear VT-d caches
    xmhf_dmaprot_arch_x86_vmx_invalidate_cache();

    // Print and clean fault registers
	xmhf_dmaprot_arch_x86_vmx_print_and_clear_fault_registers();

    // success
    printf("%s: success, leaving...\n", __FUNCTION__);

    return 1;
}

//"normal" DMA protection initialization to setup required
// structures for DMA protection
// return 1 on success 0 on failure
u32 xmhf_dmaprot_arch_x86_vmx_initialize(spa_t protectedbuffer_paddr,
                                         hva_t protectedbuffer_vaddr, size_t protectedbuffer_size)
{
    // Vt-d bootstrap has minimal DMA translation setup and protects entire
    // system memory. Relax this by instantiating a complete DMA translation
    // structure at a page granularity and protecting only the SL and Runtime
    uintptr_t vmx_eap_vtd_pml4t_paddr, vmx_eap_vtd_pml4t_vaddr;
    uintptr_t vmx_eap_vtd_pdpt_paddr, vmx_eap_vtd_pdpt_vaddr;
    uintptr_t vmx_eap_vtd_pdts_paddr, vmx_eap_vtd_pdts_vaddr;
    uintptr_t vmx_eap_vtd_pts_paddr, vmx_eap_vtd_pts_vaddr;
    uintptr_t vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr;
    uintptr_t vmx_eap_vtd_cet_paddr, vmx_eap_vtd_cet_vaddr;

    HALT_ON_ERRORCOND(protectedbuffer_size >= SIZE_G_RNTM_DMAPROT_BUFFER);

    // The VT-d page table created here is a partial one. If 4-level PT is used, then there is only one PML4 entry instead
    // of 512 entries. This is sufficient because the lower 3-level PT covers 0 - 512GB physical memory space
    vmx_eap_vtd_pml4t_paddr = protectedbuffer_paddr;
    vmx_eap_vtd_pml4t_vaddr = protectedbuffer_vaddr;
    vmx_eap_vtd_pdpt_paddr = vmx_eap_vtd_pml4t_paddr + PAGE_SIZE_4K;
    vmx_eap_vtd_pdpt_vaddr = vmx_eap_vtd_pml4t_vaddr + PAGE_SIZE_4K;
    vmx_eap_vtd_pdts_paddr = vmx_eap_vtd_pdpt_paddr + PAGE_SIZE_4K;
    vmx_eap_vtd_pdts_vaddr = vmx_eap_vtd_pdpt_vaddr + PAGE_SIZE_4K;
    vmx_eap_vtd_pts_paddr = vmx_eap_vtd_pdts_paddr + (PAGE_SIZE_4K * DMAPROT_VMX_P4L_NPDT);
    vmx_eap_vtd_pts_vaddr = vmx_eap_vtd_pdts_vaddr + (PAGE_SIZE_4K * DMAPROT_VMX_P4L_NPDT);
    vmx_eap_vtd_ret_paddr = vmx_eap_vtd_pts_paddr + (PAGE_SIZE_4K * DMAPROT_VMX_P4L_NPDT * PAE_PTRS_PER_PDT);
    vmx_eap_vtd_ret_vaddr = vmx_eap_vtd_pts_vaddr + (PAGE_SIZE_4K * DMAPROT_VMX_P4L_NPDT * PAE_PTRS_PER_PDT);
    vmx_eap_vtd_cet_paddr = vmx_eap_vtd_ret_paddr + PAGE_SIZE_4K;
    vmx_eap_vtd_cet_vaddr = vmx_eap_vtd_ret_vaddr + PAGE_SIZE_4K;

    // [Superymk] [TODO] ugly hack...
    vtd_cet = (void *)vmx_eap_vtd_cet_vaddr;
    return vmx_eap_initialize(vmx_eap_vtd_pml4t_paddr, vmx_eap_vtd_pml4t_vaddr, vmx_eap_vtd_pdpt_paddr, vmx_eap_vtd_pdpt_vaddr, vmx_eap_vtd_pdts_paddr, vmx_eap_vtd_pdts_vaddr,
                              vmx_eap_vtd_pts_paddr, vmx_eap_vtd_pts_vaddr, vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr, vmx_eap_vtd_cet_paddr, vmx_eap_vtd_cet_vaddr);
}

// DMA protect a given region of memory
void xmhf_dmaprot_arch_x86_vmx_protect(spa_t start_paddr, size_t size)
{
    pt_t pt;
    spa_t cur_spaddr, end_paddr;
    u32 pdptindex, pdtindex, ptindex;

    // compute page aligned end
    end_paddr = PA_PAGE_ALIGN_UP_4K(start_paddr + size);
    start_paddr = PA_PAGE_ALIGN_4K(start_paddr);

    // sanity check
    HALT_ON_ERRORCOND((l_vtd_pdpt_paddr != 0) && (l_vtd_pdpt_vaddr != 0));
    HALT_ON_ERRORCOND((l_vtd_pdts_paddr != 0) && (l_vtd_pdts_vaddr != 0));
    HALT_ON_ERRORCOND((l_vtd_pts_paddr != 0) && (l_vtd_pts_vaddr != 0));

#ifndef __XMHF_VERIFICATION__
    for (cur_spaddr = start_paddr; cur_spaddr < end_paddr; cur_spaddr += PAGE_SIZE_4K)
    {
        // compute pdpt, pdt and pt indices
        pdptindex = PAE_get_pdptindex(cur_spaddr);
        pdtindex = PAE_get_pdtindex(cur_spaddr);
        ptindex = PAE_get_ptindex(cur_spaddr);

        // get the page-table for this physical page
        pt = (pt_t)(l_vtd_pts_vaddr + (pdptindex * PAGE_SIZE_4K * PAE_PTRS_PER_PDT) + (pdtindex * PAGE_SIZE_4K));

        // protect the physical page
        // pt[ptindex] &= 0xFFFFFFFFFFFFFFFCULL;
        pt[ptindex] &= (~((u64)VTD_READ | (u64)VTD_WRITE) | (u64)VTD_EXECUTE);
    }
#endif
}

// DMA unprotect a given region of memory
void xmhf_dmaprot_arch_x86_vmx_unprotect(spa_t start_paddr, size_t size)
{
    pt_t pt;
    spa_t cur_spaddr, end_paddr;
    u32 pdptindex, pdtindex, ptindex;

    // compute page aligned end
    end_paddr = PA_PAGE_ALIGN_UP_4K(start_paddr + size);
    start_paddr = PA_PAGE_ALIGN_4K(start_paddr);

    // sanity check
    HALT_ON_ERRORCOND((l_vtd_pdpt_paddr != 0) && (l_vtd_pdpt_vaddr != 0));
    HALT_ON_ERRORCOND((l_vtd_pdts_paddr != 0) && (l_vtd_pdts_vaddr != 0));
    HALT_ON_ERRORCOND((l_vtd_pts_paddr != 0) && (l_vtd_pts_vaddr != 0));

#ifndef __XMHF_VERIFICATION__
    for (cur_spaddr = start_paddr; cur_spaddr < end_paddr; cur_spaddr += PAGE_SIZE_4K)
    {
        // compute pdpt, pdt and pt indices
        pdptindex = PAE_get_pdptindex(cur_spaddr);
        pdtindex = PAE_get_pdtindex(cur_spaddr);
        ptindex = PAE_get_ptindex(cur_spaddr);

        // get the page-table for this physical page
        pt = (pt_t)(l_vtd_pts_vaddr + (pdptindex * PAGE_SIZE_4K * PAE_PTRS_PER_PDT) + (pdtindex * PAGE_SIZE_4K));

        // protect the physical page
        // pt[ptindex] &= 0xFFFFFFFFFFFFFFFCULL;
        pt[ptindex] |= ((u64)VTD_READ | (u64)VTD_WRITE | (u64)VTD_EXECUTE);
    }
#endif
}

// flush the caches
void xmhf_dmaprot_arch_x86_vmx_invalidate_cache(void)
{
    u32 i = 0;

#ifndef __XMHF_VERIFICATION__
    // initialize all DRHD units
    FOREACH_S(i, vtd_num_drhd, VTD_MAX_DRHD, 0, 1)
    {
        _vtd_invalidate_caches_single_iommu(&vtd_drhd[i], &vtd_drhd[0]);
    }
#else
    _vtd_invalidate_caches_single_iommu(&vtd_drhd[0], &vtd_drhd[0]);
#endif
}




/********* Support hypapps to control igfx's IOMMU *********/
#ifdef __XMHF_ALLOW_HYPAPP_DISABLE_IGFX_IOMMU__
//! \brief Enable the IOMMU servicing the integrated GPU only. Other IOMMUs are not modified.
//!
//! @return Return true on success
bool xmhf_dmaprot_arch_x86_vmx_enable_igfx_iommu(void)
{
    return _vtd_enable_igfx_drhd(vtd_drhd, vtd_num_drhd);
}

//! \brief Disable the IOMMU servicing the integrated GPU only. Other IOMMUs are not modified.
//!
//! @return Return true on success
bool xmhf_dmaprot_arch_x86_vmx_disable_igfx_iommu(void)
{
    return _vtd_disable_igfx_drhd(vtd_drhd, vtd_num_drhd);
}
#endif // __XMHF_ALLOW_HYPAPP_DISABLE_IGFX_IOMMU__




/********* Debug functions *********/
void xmhf_dmaprot_arch_x86_vmx_print_and_clear_fault_registers(void)
{
    u32 i = 0;

    FOREACH_S(i, vtd_num_drhd, VTD_MAX_DRHD, 0, 1)
    {
        printf("DRHD[%u]:\n", i);
        _vtd_print_and_clear_fault_registers(&vtd_drhd[i]);
    }
}

void xmhf_dmaprot_arch_x86_vmx_restart_dma_iommu(void)
{
    u32 i = 0;

    FOREACH_S(i, vtd_num_drhd, VTD_MAX_DRHD, 0, 1)
    {
        _vtd_restart_dma_iommu(&vtd_drhd[i]);
    }
}

void xmhf_dmaprot_arch_x86_vmx_disable_dma_iommu(void)
{
    u32 i = 0;

    FOREACH_S(i, vtd_num_drhd, VTD_MAX_DRHD, 0, 1)
    {
        _vtd_disable_dma_iommu(&vtd_drhd[i]);
    }
}

void xmhf_dmaprot_arch_x86_vmx_print_tes(char* s)
{
    u32 i = 0;

    FOREACH_S(i, vtd_num_drhd, VTD_MAX_DRHD, 0, 1)
    {
        VTD_GSTS_REG gsts;
        _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value); 
        printf("%s gsts.bits.tes:%u\n", s, gsts.bits.tes);
    }
}