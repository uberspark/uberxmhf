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

//! @brief Modify an individual bit of Global Command Register.
extern void _vtd_drhd_issue_gcmd(VTD_DRHD *drhd, u32 offset, u32 val);

// Issue Write Buffer Flusing (WBF) if the IOMMU requires it.
extern void _vtd_drhd_issue_wbf(VTD_DRHD *drhd);

//------------------------------------------------------------------------------
// initialize a DRHD unit
// note that the VT-d documentation does not describe the precise sequence of
// steps that need to be followed to initialize a DRHD unit!. we use our
// common sense instead...:p
void _vtd_drhd_initialize_earlyinit(VTD_DRHD *drhd, u32 vtd_ret_paddr)
{
    VTD_GSTS_REG gsts;
    VTD_CCMD_REG ccmd;
    VTD_IOTLB_REG iotlb;

    // sanity check
    HALT_ON_ERRORCOND(drhd != NULL);

    // Clear <iommu_flags>
    memset(&drhd->iommu_flags, 0, sizeof(VTD_IOMMU_FLAGS));

    // Step 0. Read <cap> and <ecap>
    {
        VTD_CAP_REG cap;
        VTD_ECAP_REG ecap;

        // read ECAP register
        _vtd_reg(drhd, VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);
        drhd->iommu_flags.cap = cap;

        // read ECAP register
        _vtd_reg(drhd, VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&ecap.value);
        drhd->iommu_flags.ecap = ecap;
    }

    // check VT-d snoop control capabilities
    {
        if (vtd_ecap_sc(drhd))
            printf("	VT-d hardware Snoop Control (SC) capabilities present\n");
        else
            printf("	VT-d hardware Snoop Control (SC) unavailable\n");

        if (vtd_ecap_c(drhd))
        {
            printf("	VT-d hardware access to remapping structures COHERENT\n");
        }
        else
        {
            printf("	VT-d hardware access to remapping structures NON-COHERENT\n");
        }
    }

    // Init fault-recording registers
    {
        printf("	VT-d numbers of fault recording registers:%u\n", vtd_cap_frr_nums(drhd));
    }

    // 3. setup fault logging
    printf("	Setting Fault-reporting to NON-INTERRUPT mode...");
    {
        VTD_FECTL_REG fectl;

        // read FECTL
        fectl.value = 0;
        _vtd_reg(drhd, VTD_REG_READ, VTD_FECTL_REG_OFF, (void *)&fectl.value);

        // set interrupt mask bit and write
        fectl.bits.im = 1;
        _vtd_reg(drhd, VTD_REG_WRITE, VTD_FECTL_REG_OFF, (void *)&fectl.value);

        // check to see if the im bit actually stuck
        _vtd_reg(drhd, VTD_REG_READ, VTD_FECTL_REG_OFF, (void *)&fectl.value);

        if (!fectl.bits.im)
        {
            printf("	Failed to set fault-reporting. Halting!\n");
            HALT();
        }
    }
    printf("Done.\n");

    // 4. setup RET (root-entry)
    printf("	Setting up RET...");
    {
        VTD_RTADDR_REG rtaddr, rtaddr_readout;

        // setup RTADDR with base of RET
        rtaddr.value = (u64)vtd_ret_paddr | VTD_RTADDR_LEGACY_MODE;
        _vtd_reg(drhd, VTD_REG_WRITE, VTD_RTADDR_REG_OFF, (void *)&rtaddr.value);

        // read RTADDR and verify the base address
        rtaddr_readout.value = 0;
        IOMMU_WAIT_OP(drhd, VTD_RTADDR_REG_OFF, (rtaddr_readout.value == rtaddr.value), (void *)&rtaddr_readout.value, "	Failed to set RTADDR. Halting!");

        // latch RET address by using GCMD.SRTP
        _vtd_drhd_issue_gcmd(drhd, VTD_GCMD_BIT_SRTP, 1);

        // ensure the RET address was latched by the h/w
        IOMMU_WAIT_OP(drhd, VTD_GSTS_REG_OFF, gsts.bits.rtps, (void *)&gsts.value, "	Failed to latch RTADDR. Halting!");
    }
    printf("Done.\n");

    // If IOMMU needs mHV to issue WBF, then mHV needs to do so before invalidate caches.
    if (vtd_cap_require_wbf(drhd))
        _vtd_drhd_issue_wbf(drhd);

    // 5. invalidate CET cache
    printf("	Invalidating CET cache...");
    {
        // wait for context cache invalidation request to send
#ifndef __XMHF_VERIFICATION__
        IOMMU_WAIT_OP(drhd, VTD_CCMD_REG_OFF, !ccmd.bits.icc, (void *)&ccmd.value, "IOMMU is not ready to invalidate CET cache");
#endif

        // initialize CCMD to perform a global invalidation
        ccmd.value = 0;
        ccmd.bits.cirg = 1; // global invalidation
        ccmd.bits.icc = 1;  // invalidate context cache

        // perform the invalidation
        _vtd_reg(drhd, VTD_REG_WRITE, VTD_CCMD_REG_OFF, (void *)&ccmd.value);

        // wait for context cache invalidation completion status
#ifndef __XMHF_VERIFICATION__
        IOMMU_WAIT_OP(drhd, VTD_CCMD_REG_OFF, !ccmd.bits.icc, (void *)&ccmd.value, "Failed to invalidate CET cache");
#endif

        // if all went well CCMD CAIG = CCMD CIRG (i.e., actual = requested invalidation granularity)
        if (ccmd.bits.caig != 0x1)
        {
            printf("	Invalidatation of CET failed. Halting! (%u)\n", ccmd.bits.caig);
            HALT();
        }
    }
    printf("Done.\n");

    // 6. invalidate IOTLB
    printf("	Invalidating IOTLB...");
    {
        // wait for the IOTLB invalidation is available
        IOMMU_WAIT_OP(drhd, VTD_IOTLB_REG_OFF, !iotlb.bits.ivt, (void *)&iotlb.value, "IOMMU is not ready to invalidate IOTLB");

        // initialize IOTLB to perform a global invalidation
        iotlb.value = 0;
        iotlb.bits.iirg = 1; // global invalidation
        iotlb.bits.ivt = 1;  // invalidate

        // perform the invalidation
        _vtd_reg(drhd, VTD_REG_WRITE, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);

#ifndef __XMHF_VERIFICATION__
        // wait for the invalidation to complete
        IOMMU_WAIT_OP(drhd, VTD_IOTLB_REG_OFF, !iotlb.bits.ivt, (void *)&iotlb.value, "Failed to invalidate IOTLB");
#endif

        // if all went well IOTLB IAIG = IOTLB IIRG (i.e., actual = requested invalidation granularity)
        if (iotlb.bits.iaig != 0x1)
        {
            printf("	Invalidation of IOTLB failed. Halting! (%u)\n", iotlb.bits.iaig);
            HALT();
        }
    }
    printf("Done.\n");

    // 8. enable device
    printf("	Enabling device...");
    {
        // enable translation
        _vtd_drhd_issue_gcmd(drhd, VTD_GCMD_BIT_TE, 1);

        // wait for translation enabled status to go green...
        IOMMU_WAIT_OP(drhd, VTD_GSTS_REG_OFF, gsts.bits.tes, (void *)&gsts.value, "	DMA translation cannot be enabled. Halting!");
    }
    printf("Done.\n");
}

