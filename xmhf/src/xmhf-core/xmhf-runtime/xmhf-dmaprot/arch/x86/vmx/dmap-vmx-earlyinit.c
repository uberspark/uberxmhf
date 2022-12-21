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

// XMHF must separate earlyinit from runtime, because secure loader links different files from the runtime.

#include <xmhf.h>
#include "dmap-vmx-internal.h"

//==============================================================================
// local (static) variables and function definitions
//==============================================================================

// DMA Remapping Hardware Unit Definitions
static VTD_DRHD vtd_drhd[VTD_MAX_DRHD];
static u32 vtd_num_drhd = 0; // total number of DMAR h/w units

//------------------------------------------------------------------------------
// set VT-d RET and CET tables for VT-d bootstrapping
// we have 1 root entry table (RET) of 4kb, each root entry (RE) is 128-bits
// which gives us 256 entries in the RET, each corresponding to a PCI bus num.
//(0-255)
// each RE points to a context entry table (CET) of 4kb, each context entry (CE)
// is 128-bits which gives us 256 entries in the CET, accounting for 32 devices
// with 8 functions each as per the PCI spec.
// each CE points to a PDPT type paging structure.
// we ensure that every entry in the RET is 0 which means that the DRHD will
// not allow any DMA requests for PCI bus 0-255 (Sec 3.3.2, IVTD Spec. v1.2)
// we zero out the CET just for sanity
static void _vtd_setupRETCET_bootstrap(spa_t vtd_ret_paddr, hva_t vtd_ret_vaddr)
{
    // sanity check that RET and CET are page-aligned
    HALT_ON_ERRORCOND(PA_PAGE_ALIGNED_4K(vtd_ret_paddr));

    // zero out RET, effectively preventing DMA reads and writes in the system
    memset((void *)vtd_ret_vaddr, 0, PAGE_SIZE_4K);
}

// initialize VMX EAP a.k.a VT-d
// returns 1 if all went well, else 0
// if input parameter bootstrap is 1 then we perform minimal translation
// structure initialization, else we do the full DMA translation structure
// initialization at a page-granularity
static u32 vmx_eap_initialize_early(
    spa_t vtd_pml4t_paddr, hva_t vtd_pml4t_vaddr,
    spa_t vtd_pdpt_paddr, hva_t vtd_pdpt_vaddr,
    spa_t vtd_pdts_paddr, hva_t vtd_pdts_vaddr,
    spa_t vtd_pts_paddr, hva_t vtd_pts_vaddr,
    spa_t vtd_ret_paddr, hva_t vtd_ret_vaddr)
{
    bool status2 = false;
    VTD_DMAR dmar;
    u32 i;
    spa_t dmaraddrphys, remappingstructuresaddrphys;

    (void)vtd_pml4t_paddr;(void)vtd_pml4t_vaddr;(void)vtd_pdpt_paddr;(void)vtd_pdpt_vaddr;
    (void)vtd_pdts_paddr;(void)vtd_pdts_vaddr;(void)vtd_pts_paddr;(void)vtd_pts_vaddr;

#ifndef __XMHF_VERIFICATION__
    // zero out rsdp and rsdt structures
    memset(&g_vtd_cap_sagaw_mgaw_nd, 0, sizeof(struct dmap_vmx_cap));

    dmaraddrphys = vmx_find_dmar_paddr(&dmar);

    i = 0;
    remappingstructuresaddrphys = dmaraddrphys + sizeof(VTD_DMAR);
    printf("%s: remapping structures at %08x\n", __FUNCTION__, remappingstructuresaddrphys);

    while (i < (dmar.length - sizeof(VTD_DMAR)))
    {
        u16 type, length;
        hva_t remappingstructures_vaddr = (hva_t)remappingstructuresaddrphys;

        xmhf_baseplatform_arch_flat_copy((u8 *)&type, (u8 *)(remappingstructures_vaddr + i), sizeof(u16));
        xmhf_baseplatform_arch_flat_copy((u8 *)&length, (u8 *)(remappingstructures_vaddr + i + sizeof(u16)), sizeof(u16));

        switch (type)
        {
        case 0: // DRHD
            printf("DRHD at %08x, len=%u bytes\n", (u32)(remappingstructures_vaddr + i), length);
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
    for (i = 0; i < vtd_num_drhd; i++)
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

    // initialize VT-d RET and CET using empty RET and CET, so no DMA is allowed
    _vtd_setupRETCET_bootstrap(vtd_ret_paddr, vtd_ret_vaddr);
    printf("%s: setup VT-d RET (0x%llX) for bootstrap.\n", __FUNCTION__, vtd_ret_paddr);

    // Flush CPU cache
    wbinvd();

#endif //__XMHF_VERIFICATION__

#ifndef __XMHF_VERIFICATION__
    // initialize all DRHD units
    for (i = 0; i < vtd_num_drhd; i++)
    {
        printf("%s: initializing DRHD unit %u...\n", __FUNCTION__, i);
        _vtd_drhd_initialize_earlyinit(&vtd_drhd[i], vtd_ret_paddr);
    }
#else
    printf("%s: initializing DRHD unit %u...\n", __FUNCTION__, i);
    _vtd_drhd_initialize_earlyinit(&vtd_drhd[0], vtd_ret_paddr);
#endif

    // success
    printf("%s: success, leaving...\n", __FUNCTION__);

    return 1;
}

////////////////////////////////////////////////////////////////////////
// GLOBALS

//"early" DMA protection initialization to setup minimal
// structures to protect a range of physical memory
// return 1 on success 0 on failure
u32 xmhf_dmaprot_arch_x86_vmx_earlyinitialize(sla_t protectedbuffer_paddr, sla_t protectedbuffer_vaddr, size_t protectedbuffer_size, sla_t __attribute__((unused)) memregionbase_paddr, u32 __attribute__((unused)) memregion)
{
    u32 vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr;

    //(void)memregionbase_paddr;
    //(void)memregion_size;

    printf("SL: Bootstrapping VMX DMA protection...\n");

    // we use 1 pages for Vt-d bootstrapping
    HALT_ON_ERRORCOND(protectedbuffer_size >= (1 * PAGE_SIZE_4K));

    vmx_eap_vtd_ret_paddr = protectedbuffer_paddr;
    vmx_eap_vtd_ret_vaddr = protectedbuffer_vaddr;

    return vmx_eap_initialize_early(0, 0, 0, 0, 0, 0, 0, 0,
                vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr);
}
