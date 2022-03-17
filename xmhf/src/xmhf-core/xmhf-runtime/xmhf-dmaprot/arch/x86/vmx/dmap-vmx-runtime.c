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

void *vtd_cet = NULL; // cet holds all its structures in the memory linearly

// maximum number of RSDT entries we support
#define ACPI_MAX_RSDT_ENTRIES (256)

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
static bool _vtd_setuppagetables(struct dmap_vmx_cap *vtd_cap,
                                 spa_t vtd_pml4t_paddr, hva_t vtd_pml4t_vaddr,
                                 spa_t vtd_pdpt_paddr, hva_t vtd_pdpt_vaddr,
                                 spa_t vtd_pdts_paddr, hva_t vtd_pdts_vaddr,
                                 spa_t vtd_pts_paddr, hva_t vtd_pts_vaddr,
                                 spa_t machine_low_spa, u64 machine_high_spa)
{
    spa_t pml4tphysaddr, pdptphysaddr, pdtphysaddr, ptphysaddr;
    u32 i, j, k;
    pml4t_t pml4t;
    pdpt_t pdpt;
    pdt_t pdt;
    pt_t pt;
    uintptr_t physaddr = 0;
    spa_t m_low_spa = PAGE_ALIGN_1G(machine_low_spa);
    u64 m_high_spa = PAGE_ALIGN_UP1G(machine_high_spa);
    u32 num_1G_entries = (m_high_spa - (u64)m_low_spa) >> PAGE_SHIFT_1G;

    // Sanity checks
    if (!vtd_cap)
        return false;

    pml4tphysaddr = vtd_pml4t_paddr;
    pdptphysaddr = vtd_pdpt_paddr;
    pdtphysaddr = vtd_pdts_paddr;
    ptphysaddr = vtd_pts_paddr;

    // ensure PDPT, PDTs and PTs are all page-aligned
    HALT_ON_ERRORCOND(!(pml4tphysaddr & 0x00000FFFUL) && !(pdptphysaddr & 0x00000FFFUL) && !(pdtphysaddr & 0x00000FFFUL) && !((ptphysaddr & 0x00000FFFUL)));

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
    pml4t[0] |= ((u64)VTD_READ | (u64)VTD_WRITE);

    // setup pdpt, pdt and pt
    // initially set the entire spaddr space [m_low_spa, m_high_spa) as DMA read/write capable
    pdpt = (pdpt_t)vtd_pdpt_vaddr;
    for (i = 0; i < num_1G_entries; i++) // DMAPROT_VMX_P4L_NPDT
    {
        pdpt[i] = (u64)(pdtphysaddr + (i * PAGE_SIZE_4K));
        pdpt[i] |= ((u64)VTD_READ | (u64)VTD_WRITE);

        pdt = (pdt_t)(vtd_pdts_vaddr + (i * PAGE_SIZE_4K));
        for (j = 0; j < PAE_PTRS_PER_PDT; j++)
        {
            pdt[j] = (u64)(ptphysaddr + (i * PAGE_SIZE_4K * 512) + (j * PAGE_SIZE_4K));
            pdt[j] |= ((u64)VTD_READ | (u64)VTD_WRITE);

            pt = (pt_t)(vtd_pts_vaddr + (i * PAGE_SIZE_4K * 512) + (j * PAGE_SIZE_4K));
            for (k = 0; k < PAE_PTRS_PER_PT; k++)
            {
                pt[k] = (u64)physaddr;
                pt[k] |= ((u64)VTD_READ | (u64)VTD_WRITE);
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
                             uintptr_t vtd_pml4t_paddr, uintptr_t vtd_pdpt_paddr,
                             uintptr_t vtd_ret_paddr, uintptr_t vtd_ret_vaddr,
                             uintptr_t vtd_cet_paddr, uintptr_t vtd_cet_vaddr)
{
    uintptr_t retphysaddr, cetphysaddr;
    u32 i, j;
    u64 *value;

    // Sanity checks
    if (!vtd_cap)
        return false;

    retphysaddr = vtd_ret_paddr;
    (void)retphysaddr;
    cetphysaddr = vtd_cet_paddr;

    // sanity check that pdpt base address is page-aligned
    HALT_ON_ERRORCOND(!(vtd_pdpt_paddr & 0x00000FFFUL));

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
        for (j = 0; j < PCI_BUS_MAX; j++)
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
    memset(&g_vtd_cap, 0, sizeof(struct dmap_vmx_cap));

    // get ACPI RSDP
    //  [TODO] Unify the name of <xmhf_baseplatform_arch_x86_acpi_getRSDP> and <xmhf_baseplatform_arch_x86_acpi_getRSDP>, and then remove the following #ifdef
    status = xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp);
    HALT_ON_ERRORCOND(status != 0); // we need a valid RSDP to proceed
    printf("\n%s: RSDP at %08x", __FUNCTION__, status);

    // [Superymk] Use RSDT if it is ACPI v1, or use XSDT addr if it is ACPI v2
    if (rsdp.revision == 0) // ACPI v1
    {
        printf("\n%s: ACPI v1", __FUNCTION__);
        rsdt_xsdt_spaddr = rsdp.rsdtaddress;
    }
    else if (rsdp.revision == 0x2) // ACPI v2
    {
        printf("\n%s: ACPI v2", __FUNCTION__);
        rsdt_xsdt_spaddr = (spa_t)rsdp.xsdtaddress;
    }
    else // Unrecognized ACPI version
    {
        printf("\n%s: ACPI unsupported version!", __FUNCTION__);
        return 0;
    }

    // grab ACPI RSDT
    // Note: in i386, <rsdt_xsdt_spaddr> should be in lower 4GB. So the conversion to vaddr is fine.
    rsdt_xsdt_vaddr = (hva_t)rsdt_xsdt_spaddr;

    xmhf_baseplatform_arch_flat_copy((u8 *)&rsdt, (u8 *)rsdt_xsdt_vaddr, sizeof(ACPI_RSDT));
    printf("\n%s: RSDT at %08x, len=%u bytes, hdrlen=%u bytes",
           __FUNCTION__, rsdt_xsdt_vaddr, rsdt.length, sizeof(ACPI_RSDT));

    // get the RSDT entry list
    num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT)) / sizeof(u32);
    HALT_ON_ERRORCOND(num_rsdtentries < ACPI_MAX_RSDT_ENTRIES);
    xmhf_baseplatform_arch_flat_copy((u8 *)&rsdtentries, (u8 *)(rsdt_xsdt_vaddr + sizeof(ACPI_RSDT)),
                                     sizeof(rsdtentries[0]) * num_rsdtentries);
    printf("\n%s: RSDT entry list at %08x, len=%u", __FUNCTION__,
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
    printf("\n%s: DMAR at %08x", __FUNCTION__, dmaraddrphys);

    i = 0;
    remappingstructuresaddrphys = dmaraddrphys + sizeof(VTD_DMAR);
    printf("\n%s: remapping structures at %08x", __FUNCTION__, remappingstructuresaddrphys);

    while (i < (dmar.length - sizeof(VTD_DMAR)))
    {
        u16 type, length;
        hva_t remappingstructures_vaddr = (hva_t)remappingstructuresaddrphys;

        xmhf_baseplatform_arch_flat_copy((u8 *)&type, (u8 *)(remappingstructures_vaddr + i), sizeof(u16));
        xmhf_baseplatform_arch_flat_copy((u8 *)&length, (u8 *)(remappingstructures_vaddr + i + sizeof(u16)), sizeof(u16));

        switch (type)
        {
        case 0: // DRHD
            printf("\nDRHD at %08x, len=%u bytes", (u32)(remappingstructures_vaddr + i), length);
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

    printf("\n%s: total DRHDs detected= %u units", __FUNCTION__, vtd_num_drhd);

    // be a little verbose about what we found
    printf("\n%s: DMAR Devices:", __FUNCTION__);
    for (i = 0; i < vtd_num_drhd; i++)
    {
        VTD_CAP_REG cap;
        VTD_ECAP_REG ecap;
        printf("\n	Device %u on PCI seg %04x; base=0x%016llx", i,
               vtd_drhd[i].pcisegment, vtd_drhd[i].regbaseaddr);
        _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);
        printf("\n		cap=0x%016llx", (u64)cap.value);
        _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&ecap.value);
        printf("\n		ecap=0x%016llx", (u64)ecap.value);
    }

    // Verify VT-d capabilities
    status2 = _vtd_verify_cap(vtd_drhd, vtd_num_drhd, &g_vtd_cap);
    if (!status2)
    {
        printf("\n%s: verify VT-d units' capabilities error! Halting!", __FUNCTION__);
        HALT();
    }

    // initialize VT-d page tables (not done if we are bootstrapping)
    {
        spa_t machine_low_spa = INVALID_SPADDR;
        u64 machine_high_spa = INVALID_SPADDR;
        u64 phy_space_size = 0;

        // Get the base and limit used system physical address from the E820 map
        status2 = xmhf_baseplatform_x86_e820_paddr_range(&machine_low_spa, &machine_high_spa);
        if (!status2)
        {
            printf("\n%s: Get system physical address range error! Halting!", __FUNCTION__);
            HALT();
        }
        machine_low_spa = PAGE_ALIGN_4K(machine_low_spa);
        machine_high_spa = PAGE_ALIGN_UP4K(machine_high_spa);

        // Check: The base and limit of the physical address space must <= DMAPROT_PHY_ADDR_SPACE_SIZE
        phy_space_size = machine_high_spa - machine_low_spa;
        if(phy_space_size > DMAPROT_PHY_ADDR_SPACE_SIZE)
        {
            printf("\n%s: Too large system physical address! Found space size:%llX. Halting!", __FUNCTION__, phy_space_size);
            HALT();
        }

        status2 = _vtd_setuppagetables(&g_vtd_cap, vtd_pml4t_paddr, vtd_pml4t_vaddr, vtd_pdpt_paddr, vtd_pdpt_vaddr,
                                       vtd_pdts_paddr, vtd_pdts_vaddr, vtd_pts_paddr, vtd_pts_vaddr, machine_low_spa, machine_high_spa);
        if (!status2)
        {
            printf("\n%s: setup VT-d page tables (pdpt=%08x, pdts=%08x, pts=%08x) error! Halting!", __FUNCTION__, vtd_pdpt_paddr, vtd_pdts_paddr, vtd_pts_paddr);
            HALT();
        }

        printf("\n%s: setup VT-d page tables (pdpt=%08x, pdts=%08x, pts=%08x).", __FUNCTION__, vtd_pdpt_paddr, vtd_pdts_paddr, vtd_pts_paddr);
    }

    // initialize VT-d RET and CET
    {
        status2 = _vtd_setupRETCET(&g_vtd_cap, vtd_pml4t_paddr, vtd_pdpt_paddr, vtd_ret_paddr, vtd_ret_vaddr, vtd_cet_paddr, vtd_cet_vaddr);
        if (!status2)
        {
            printf("\n%s: setup VT-d RET (%08x) and CET (%08x) error! Halting!", __FUNCTION__, vtd_ret_paddr, vtd_cet_paddr);
            HALT();
        }

        printf("\n%s: setup VT-d RET (%08x) and CET (%08x).", __FUNCTION__, vtd_ret_paddr, vtd_cet_paddr);
    }

#endif //__XMHF_VERIFICATION__

#ifndef __XMHF_VERIFICATION__
    // initialize all DRHD units
    for (i = 0; i < vtd_num_drhd; i++)
    {
        printf("\n%s: initializing DRHD unit %u...", __FUNCTION__, i);
        _vtd_drhd_initialize(&vtd_drhd[i], vtd_ret_paddr);
    }
#else
    printf("\n%s: initializing DRHD unit %u...", __FUNCTION__, i);
    _vtd_drhd_initialize(&vtd_drhd[0], vtd_ret_paddr);
#endif

    // zap VT-d presence in ACPI table...
    // TODO: we need to be a little elegant here. eventually need to setup
    // EPT/NPTs such that the DMAR pages are unmapped for the guest
    xmhf_baseplatform_arch_flat_writeu32(dmaraddrphys, 0UL);

    // success
    printf("\n%s: success, leaving...", __FUNCTION__);

    return 1;
}

//------------------------------------------------------------------------------
// vt-d invalidate cachess note: we do global invalidation currently
static void _vtd_invalidatecaches(void)
{
    u32 i;
    VTD_CCMD_REG ccmd;
    VTD_IOTLB_REG iotlb;

#ifdef __XMHF_VERIFICATION__
    for (i = 0; i < 1; i++)
    {
#else
    for (i = 0; i < vtd_num_drhd; i++)
    {
#endif
        // 1. invalidate CET cache

#ifndef __XMHF_VERIFICATION__
        // wait for context cache invalidation request to send
        do
        {
            _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_CCMD_REG_OFF, (void *)&ccmd.value);
        } while (ccmd.bits.icc);
#else
        _vtd_reg(&vtd_drhd[0], VTD_REG_READ, VTD_CCMD_REG_OFF, (void *)&ccmd.value);
#endif

        // initialize CCMD to perform a global invalidation
        ccmd.value = 0;
        ccmd.bits.cirg = 1; // global invalidation
        ccmd.bits.icc = 1;  // invalidate context cache

        // perform the invalidation
        _vtd_reg(&vtd_drhd[i], VTD_REG_WRITE, VTD_CCMD_REG_OFF, (void *)&ccmd.value);

#ifndef __XMHF_VERIFICATION__
        // wait for context cache invalidation completion status
        do
        {
            _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_CCMD_REG_OFF, (void *)&ccmd.value);
        } while (ccmd.bits.icc);
#else
        _vtd_reg(&vtd_drhd[0], VTD_REG_READ, VTD_CCMD_REG_OFF, (void *)&ccmd.value);
#endif

        // if all went well CCMD CAIG = CCMD CIRG (i.e., actual = requested invalidation granularity)
        if (ccmd.bits.caig != 0x1)
        {
            printf("\n	Invalidatation of CET failed. Halting! (%u)", ccmd.bits.caig);
            HALT();
        }

        // 2. invalidate IOTLB
        // initialize IOTLB to perform a global invalidation
        iotlb.value = 0;
        iotlb.bits.iirg = 1; // global invalidation
        iotlb.bits.ivt = 1;  // invalidate

        // perform the invalidation
        _vtd_reg(&vtd_drhd[i], VTD_REG_WRITE, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);

#ifndef __XMHF_VERIFICATION__
        // wait for the invalidation to complete
        do
        {
            _vtd_reg(&vtd_drhd[i], VTD_REG_READ, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);
        } while (iotlb.bits.ivt);
#else
        _vtd_reg(&vtd_drhd[0], VTD_REG_READ, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);
#endif

        // if all went well IOTLB IAIG = IOTLB IIRG (i.e., actual = requested invalidation granularity)
        if (iotlb.bits.iaig != 0x1)
        {
            printf("\n	Invalidation of IOTLB failed. Halting! (%u)", iotlb.bits.iaig);
            HALT();
        }
    }
}

////////////////////////////////////////////////////////////////////////
// GLOBALS

#define PAE_get_pdptindex(x) ((x) >> 30)
#define PAE_get_pdtindex(x) (((x) << 2) >> 23)
#define PAE_get_ptindex(x) (((x) << 11) >> 23)
#define PAE_get_pdtaddress(x) ((u32)((u64)(x) & (u64)0x3FFFFFFFFFFFF000ULL))
#define PAE_get_ptaddress(x) ((u32)((u64)(x) & (u64)0x3FFFFFFFFFFFF000ULL))

#if !defined(__DMAP__)
void vmx_eap_zap(void)
{
    ACPI_RSDP rsdp;
    ACPI_RSDT rsdt;
    u32 num_rsdtentries;
    uintptr_t rsdtentries[ACPI_MAX_RSDT_ENTRIES];
    uintptr_t status;
    VTD_DMAR dmar;
    u32 i, dmarfound;
    spa_t dmaraddrphys, remappingstructuresaddrphys;
    spa_t rsdt_xsdt_spaddr = INVALID_SPADDR;
    hva_t rsdt_xsdt_vaddr = INVALID_VADDR;

    // zero out rsdp and rsdt structures
    memset(&rsdp, 0, sizeof(ACPI_RSDP));
    memset(&rsdt, 0, sizeof(ACPI_RSDT));

    // get ACPI RSDP
    // [TODO] Unify the name of <xmhf_baseplatform_arch_x86_acpi_getRSDP> and <xmhf_baseplatform_arch_x86_acpi_getRSDP>, and then remove the following #ifdef
    status = xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp);
    HALT_ON_ERRORCOND(status != 0); // we need a valid RSDP to proceed
    printf("\n%s: RSDP at %08x", __FUNCTION__, status);

    // [Superymk] Use RSDT if it is ACPI v1, or use XSDT addr if it is ACPI v2
    if (rsdp.revision == 0) // ACPI v1
    {
        printf("\n%s: ACPI v1", __FUNCTION__);
        rsdt_xsdt_spaddr = rsdp.rsdtaddress;
    }
    else if (rsdp.revision == 0x2) // ACPI v2
    {
        printf("\n%s: ACPI v2", __FUNCTION__);
        rsdt_xsdt_spaddr = (spa_t)rsdp.xsdtaddress;
    }
    else // Unrecognized ACPI version
    {
        printf("\n%s: ACPI unsupported version!", __FUNCTION__);
        return;
    }

    // grab ACPI RSDT
    // Note: in i386, <rsdt_xsdt_spaddr> should be in lower 4GB. So the conversion to vaddr is fine.
    rsdt_xsdt_vaddr = (hva_t)rsdt_xsdt_spaddr;

    xmhf_baseplatform_arch_flat_copy((u8 *)&rsdt, (u8 *)rsdt_xsdt_vaddr, sizeof(ACPI_RSDT));
    printf("\n%s: RSDT at %08x, len=%u bytes, hdrlen=%u bytes",
           __FUNCTION__, rsdt_xsdt_vaddr, rsdt.length, sizeof(ACPI_RSDT));

    // get the RSDT entry list
    num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT)) / sizeof(u32);
    HALT_ON_ERRORCOND(num_rsdtentries < ACPI_MAX_RSDT_ENTRIES);
    xmhf_baseplatform_arch_flat_copy((u8 *)&rsdtentries, (u8 *)(rsdt_xsdt_vaddr + sizeof(ACPI_RSDT)),
                                     sizeof(u32) * num_rsdtentries);
    printf("\n%s: RSDT entry list at %08x, len=%u", __FUNCTION__,
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
        return;

    dmaraddrphys = rsdtentries[i]; // DMAR table physical memory address;
    printf("\n%s: DMAR at %08x", __FUNCTION__, dmaraddrphys);

    i = 0;
    remappingstructuresaddrphys = dmaraddrphys + sizeof(VTD_DMAR);
    printf("\n%s: remapping structures at %08x", __FUNCTION__, remappingstructuresaddrphys);

    // zap VT-d presence in ACPI table...
    // TODO: we need to be a little elegant here. eventually need to setup
    // EPT/NPTs such that the DMAR pages are unmapped for the guest
    xmhf_baseplatform_arch_flat_writeu32(dmaraddrphys, 0UL);

    // success
    printf("\n%s: success, leaving...", __FUNCTION__);
}
#endif //__DMAP__

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
    vmx_eap_vtd_pdpt_paddr = protectedbuffer_paddr + PAGE_SIZE_4K;
    vmx_eap_vtd_pdpt_vaddr = protectedbuffer_vaddr + PAGE_SIZE_4K;
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
    end_paddr = PAGE_ALIGN_4K(start_paddr + size);
    start_paddr = PAGE_ALIGN_4K(start_paddr);

    // sanity check
    HALT_ON_ERRORCOND((l_vtd_pdpt_paddr != 0) && (l_vtd_pdpt_vaddr != 0));
    HALT_ON_ERRORCOND((l_vtd_pdts_paddr != 0) && (l_vtd_pdts_vaddr != 0));
    HALT_ON_ERRORCOND((l_vtd_pts_paddr != 0) && (l_vtd_pts_vaddr != 0));

#ifndef __XMHF_VERIFICATION__
    for (cur_spaddr = start_paddr; cur_spaddr <= end_paddr; cur_spaddr += PAGE_SIZE_4K)
    {

        // compute pdpt, pdt and pt indices
        pdptindex = PAE_get_pdptindex(cur_spaddr);
        pdtindex = PAE_get_pdtindex(cur_spaddr);
        ptindex = PAE_get_ptindex(cur_spaddr);

        // get the page-table for this physical page
        pt = (pt_t)(l_vtd_pts_vaddr + (pdptindex * PAGE_SIZE_4K * PAE_PTRS_PER_PDT) + (pdtindex * PAGE_SIZE_4K));

        // protect the physical page
        // pt[ptindex] &= 0xFFFFFFFFFFFFFFFCULL;
        pt[ptindex] &= ~((u64)VTD_READ | (u64)VTD_WRITE);
    }
#endif

    // flush the caches
    _vtd_invalidatecaches();
}

// DMA unprotect a given region of memory
void xmhf_dmaprot_arch_x86_vmx_unprotect(spa_t start_paddr, size_t size)
{
    pt_t pt;
    spa_t cur_spaddr, end_paddr;
    u32 pdptindex, pdtindex, ptindex;

    // compute page aligned end
    end_paddr = PAGE_ALIGN_4K(start_paddr + size);
    start_paddr = PAGE_ALIGN_4K(start_paddr);

    // sanity check
    HALT_ON_ERRORCOND((l_vtd_pdpt_paddr != 0) && (l_vtd_pdpt_vaddr != 0));
    HALT_ON_ERRORCOND((l_vtd_pdts_paddr != 0) && (l_vtd_pdts_vaddr != 0));
    HALT_ON_ERRORCOND((l_vtd_pts_paddr != 0) && (l_vtd_pts_vaddr != 0));

#ifndef __XMHF_VERIFICATION__
    for (cur_spaddr = start_paddr; cur_spaddr <= end_paddr; cur_spaddr += PAGE_SIZE_4K)
    {
        // compute pdpt, pdt and pt indices
        pdptindex = PAE_get_pdptindex(cur_spaddr);
        pdtindex = PAE_get_pdtindex(cur_spaddr);
        ptindex = PAE_get_ptindex(cur_spaddr);

        // get the page-table for this physical page
        pt = (pt_t)(l_vtd_pts_vaddr + (pdptindex * PAGE_SIZE_4K * PAE_PTRS_PER_PDT) + (pdtindex * PAGE_SIZE_4K));

        // protect the physical page
        // pt[ptindex] &= 0xFFFFFFFFFFFFFFFCULL;
        pt[ptindex] |= ((u64)VTD_READ | (u64)VTD_WRITE);
    }
#endif
}

// flush the caches
void xmhf_dmaprot_arch_x86_vmx_invalidate_cache(void)
{
    _vtd_invalidatecaches();
}
