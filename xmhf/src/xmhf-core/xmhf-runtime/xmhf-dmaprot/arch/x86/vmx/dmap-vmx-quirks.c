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

// author: Miao Yu [Superymk]
#ifdef __XMHF_ALLOW_HYPAPP_DISABLE_IGFX_IOMMU__

#include <xmhf.h>
#include "dmap-vmx-internal.h"

static VTD_DRHD* _vtd_find_igfx_drhd(VTD_DRHD* drhds, uint32_t vtd_num_drhd)
{
    // uint32_t i = 0;

    // FOREACH_S(i, vtd_num_drhd, VTD_MAX_DRHD, 0, 1)
    // {
    //     VTD_DRHD* drhd = &drhds[i];

    //     if(drhd->flags & ACPI_DMAR_INCLUDE_ALL == 0)
    //     {
    //         // Find the DRHD for an integrated GPU only
    //         return drhd;
    //     }
    // }

    // [TODO][Urgent] We hardcode the result for HP 2540p currently, a correct implementation should refer to 
    // <acpi_parse_dev_scope> in Xen 4.16.1
    static uint32_t ioh_bus = 0, ioh_dev = 0, ioh_fn = 0;
    uint32_t ioh_id = 0;

    #define IS_ILK(id)    (id == 0x00408086 || id == 0x00448086 || id== 0x00628086 || id == 0x006A8086)


    xmhf_baseplatform_arch_x86_pci_type1_read(ioh_bus, ioh_dev, ioh_fn, 0, sizeof(u32), &ioh_id);
    if(IS_ILK(ioh_id))
        return &drhds[1];

    (void)vtd_num_drhd;
    return NULL;
}

//! \brief Disable the IOMMU servicing the integrated GPU only. Other IOMMUs are not modified.
//!
//! @return Return true on success
bool _vtd_disable_igfx_drhd(VTD_DRHD* drhds, uint32_t vtd_num_drhd)
{
    VTD_DRHD* drhd = NULL;

    drhd = _vtd_find_igfx_drhd(drhds, vtd_num_drhd);
    if(!drhd)
        return false;

    _vtd_disable_dma_iommu(drhd);
    return true;
}

//! \brief Enable the IOMMU servicing the integrated GPU only. Other IOMMUs are not modified.
//!
//! @return Return true on success
bool _vtd_enable_igfx_drhd(VTD_DRHD* drhds, uint32_t vtd_num_drhd)
{
    VTD_DRHD* drhd = NULL;

    drhd = _vtd_find_igfx_drhd(drhds, vtd_num_drhd);
    if(!drhd)
        return false;

    _vtd_enable_dma_iommu(drhd);
    return true;
}


#endif // __XMHF_ALLOW_HYPAPP_DISABLE_IGFX_IOMMU__