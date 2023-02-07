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
#ifndef XMHF_DMAP_VMX_INTERNAL_H
#define XMHF_DMAP_VMX_INTERNAL_H

#include <xmhf.h>

#define NUM_PT_ENTRIES      512 // The number of page table entries in each level

#define PAE_get_pml4tindex(x)    ((x) >> 39ULL) & (NUM_PT_ENTRIES - 1ULL)
#define PAE_get_pdptindex(x)    ((x) >> 30ULL) & (NUM_PT_ENTRIES - 1ULL)
#define PAE_get_pdtindex(x)     ( (x) >> 21ULL) & (NUM_PT_ENTRIES - 1ULL)
#define PAE_get_ptindex(x)      ( (x) >> 12ULL) & (NUM_PT_ENTRIES - 1ULL)


#ifndef __ASSEMBLY__
extern struct dmap_vmx_cap g_vtd_cap_sagaw_mgaw_nd;

#define DMAR_OPERATION_TIMEOUT  SEC_TO_CYCLES(1)

#define IOMMU_WAIT_OP(drhd, reg, cond, sts, msg_for_false_cond)                 \
    do                                                                          \
    {                                                                           \
        uint64_t start_time = rdtsc64();                                        \
        while (1)                                                               \
        {                                                                       \
            _vtd_reg(drhd, VTD_REG_READ, reg, sts);                             \
            if (cond)                                                           \
                break;                                                          \
            if (rdtsc64() > start_time + DMAR_OPERATION_TIMEOUT)                \
            {                                                                   \
                printf("DMAR hardware malfunction:%s\n", (msg_for_false_cond)); \
                HALT();                                                         \
            }                                                                   \
            xmhf_cpu_relax();                                                   \
        }                                                                       \
    } while (0)

//vt-d register access function
extern void _vtd_reg(VTD_DRHD *dmardevice, u32 access, u32 reg, void *value);

// Return true if verification of VT-d capabilities succeed.
// Success means:
// (0) <out_cap> must be valid
// (1) Same AGAW, MGAW, and ND across VT-d units
// (2) supported MGAW to ensure our host address width is supported (32-bits)
// (3) AGAW must support 39-bits or 48-bits
// (4) Number of domains must not be unsupported
extern bool _vtd_verify_cap(VTD_DRHD* vtd_drhd, u32 vtd_num_drhd, struct dmap_vmx_cap* out_cap);

// initialize a DRHD unit
// note that the VT-d documentation does not describe the precise sequence of
// steps that need to be followed to initialize a DRHD unit!. we use our
// common sense instead...:p
extern void _vtd_drhd_initialize_earlyinit(VTD_DRHD *drhd, u32 vtd_ret_paddr);

//initialize a DRHD unit
//note that the VT-d documentation does not describe the precise sequence of
//steps that need to be followed to initialize a DRHD unit!. we use our
//common sense instead...:p
extern void _vtd_drhd_initialize_runtime(VTD_DRHD *drhd, u32 vtd_ret_paddr);

// vt-d invalidate cachess note: we do global invalidation currently
// [NOTE] <drhd0> refers to &vtd_drhd[0] and is used for __XMHF_VERIFICATION__ only.
extern void _vtd_invalidate_caches_single_iommu(VTD_DRHD *drhd, VTD_DRHD *drhd0);




/********* Other util functions *********/
extern void _vtd_print_and_clear_fault_registers(VTD_DRHD *drhd);
extern void _vtd_restart_dma_iommu(VTD_DRHD *drhd);
extern void _vtd_enable_dma_iommu(VTD_DRHD *drhd);
extern void _vtd_disable_dma_iommu(VTD_DRHD *drhd);

#endif // __ASSEMBLY__
#endif // XMHF_DMAP_VMX_INTERNAL_H