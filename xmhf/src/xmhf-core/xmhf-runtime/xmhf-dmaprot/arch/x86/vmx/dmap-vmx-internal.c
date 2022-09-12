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

struct dmap_vmx_cap g_vtd_cap;

//------------------------------------------------------------------------------
// vt-d register access function
void _vtd_reg(VTD_DRHD *dmardevice, u32 access, u32 reg, void *value)
{
    u32 regtype = VTD_REG_32BITS, regaddr = 0;

    // obtain register type and base address
    switch (reg)
    {
    // 32-bit registers
    case VTD_VER_REG_OFF:
    case VTD_GCMD_REG_OFF:
    case VTD_GSTS_REG_OFF:
    case VTD_FSTS_REG_OFF:
    case VTD_FECTL_REG_OFF:
    case VTD_PMEN_REG_OFF:
        regtype = VTD_REG_32BITS;
        regaddr = dmardevice->regbaseaddr + reg;
        break;

    // 64-bit registers
    case VTD_CAP_REG_OFF:
    case VTD_ECAP_REG_OFF:
    case VTD_RTADDR_REG_OFF:
    case VTD_CCMD_REG_OFF:
        regtype = VTD_REG_64BITS;
        regaddr = dmardevice->regbaseaddr + reg;
        break;

    case VTD_IOTLB_REG_OFF:
    {
        VTD_ECAP_REG t_vtd_ecap_reg;
        regtype = VTD_REG_64BITS;
#ifndef __XMHF_VERIFICATION__
        _vtd_reg(dmardevice, VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&t_vtd_ecap_reg.value);
#endif
        regaddr = dmardevice->regbaseaddr + (t_vtd_ecap_reg.bits.iro * 16) + 0x8;
        break;
    }

    case VTD_IVA_REG_OFF:
    {
        VTD_ECAP_REG t_vtd_ecap_reg;
        regtype = VTD_REG_64BITS;
#ifndef __XMHF_VERIFICATION__
        _vtd_reg(dmardevice, VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&t_vtd_ecap_reg.value);
#endif
        regaddr = dmardevice->regbaseaddr + (t_vtd_ecap_reg.bits.iro * 16);
        break;
    }

    default:
        printf("%s: Halt, Unsupported register=%08x\n", __FUNCTION__, reg);
        HALT();
        break;
    }

    // perform the actual read or write request
    switch (regtype)
    {
    case VTD_REG_32BITS:
    { // 32-bit r/w
        if (access == VTD_REG_READ)
            *((u32 *)value) = xmhf_baseplatform_arch_flat_readu32(regaddr);
        else
            xmhf_baseplatform_arch_flat_writeu32(regaddr, *((u32 *)value));

        break;
    }

    case VTD_REG_64BITS:
    { // 64-bit r/w
        if (access == VTD_REG_READ)
            *((u64 *)value) = xmhf_baseplatform_arch_flat_readu64(regaddr);
        else
            xmhf_baseplatform_arch_flat_writeu64(regaddr, *((u64 *)value));

        break;
    }

    default:
        printf("%s: Halt, Unsupported access width=%08x\n", __FUNCTION__, regtype);
        HALT();
    }

    return;
}

// Return true if verification of VT-d capabilities succeed.
// Success means:
// (0) <out_cap> must be valid
// (1) Same AGAW, MGAW, and ND across VT-d units
// (2) supported MGAW to ensure our host address width is supported (32-bits)
// (3) AGAW must support 39-bits or 48-bits
// (4) Number of domains must not be unsupported
bool _vtd_verify_cap(VTD_DRHD* vtd_drhd, u32 vtd_num_drhd, struct dmap_vmx_cap *out_cap)
{
#define INVALID_SAGAW_VAL 0xFFFFFFFF
#define INVALID_MGAW_VAL 0xFFFFFFFF
#define INVALID_NUM_DOMAINS 0xFFFFFFFF

    VTD_CAP_REG cap;
    u32 i = 0;
    u32 last_sagaw = INVALID_SAGAW_VAL;
    u32 last_mgaw = INVALID_MGAW_VAL;
    u32 last_nd = INVALID_NUM_DOMAINS;

    // Sanity checks
    if (!out_cap)
        return false;

    if(!vtd_drhd)
        return false;

    if(!vtd_num_drhd || vtd_num_drhd >= VTD_MAX_DRHD) // Support maximum of VTD_MAX_DRHD VT-d units
        return false;

    for (i = 0; i < vtd_num_drhd; i++)
    {
        VTD_DRHD *drhd = &vtd_drhd[i];
        printf("%s: verifying DRHD unit %u...\n", __FUNCTION__, i);

        // read CAP register
        _vtd_reg(drhd, VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);

        // Check: Same AGAW, MGAW and ND across VT-d units
        if (cap.bits.sagaw != last_sagaw)
        {
            if (last_sagaw == INVALID_SAGAW_VAL)
            {
                // This must the first VT-d unit
                last_sagaw = cap.bits.sagaw;
            }
            else
            {
                // The current VT-d unit has different capabilities with some other units
                printf("  [VT-d] Check error! Different SAGAW capability found on VT-d unix %u. last sagaw:0x%08X, current sagaw:0x%08X\n",
                       i, last_sagaw, cap.bits.sagaw);
                return false;
            }
        }

        if (cap.bits.mgaw != last_mgaw)
        {
            if (last_mgaw == INVALID_MGAW_VAL)
            {
                // This must the first VT-d unit
                last_mgaw = cap.bits.mgaw;
            }
            else
            {
                // The current VT-d unit has different capabilities with some other units
                printf("  [VT-d] Check error! Different MGAW capability found on VT-d unix %u. last mgaw:0x%08X, current mgaw:0x%08X\n",
                       i, last_mgaw, cap.bits.mgaw);
                return false;
            }
        }

        if (cap.bits.nd != last_nd)
        {
            if (last_nd == INVALID_NUM_DOMAINS)
            {
                // This must the first VT-d unit
                last_nd = cap.bits.nd;
            }
            else
            {
                // The current VT-d unit has different capabilities with some other units
                printf("  [VT-d] Check error! Different ND capability found on VT-d unix %u. last nd:0x%08X, current nd:0x%08X\n",
                       i, last_nd, cap.bits.nd);
                return false;
            }
        }

        // Check: supported MGAW to ensure our host address width is supported (32-bits)
        if (cap.bits.mgaw < 31)
        {
            printf("  [VT-d] Check error! GAW < 31 (%u) unsupported.\n", cap.bits.mgaw);
            return false;
        }

        // Check: AGAW must support 39-bits or 48-bits
        if (!(cap.bits.sagaw & 0x2 || cap.bits.sagaw & 0x4))
        {
            printf("	[VT-d] Check error! AGAW does not support 3-level or 4-level page-table. See sagaw capabilities:0x%08X. Halting!\n", cap.bits.sagaw);
            return false;
        }
        else
        {
            out_cap->sagaw = cap.bits.sagaw;
        }

        // Check: Number of domains must not be unsupported
        if (cap.bits.nd == 0x7)
        {
            printf("  [VT-d] Check error! ND == 0x7 unsupported on VT-d unix %u.\n", i);
            return false;
        }
        else
        {
            out_cap->nd = cap.bits.nd;
        }
    }

    printf("Verify all Vt-d units success\n");

    return true;
}

//------------------------------------------------------------------------------
// initialize a DRHD unit
// note that the VT-d documentation does not describe the precise sequence of
// steps that need to be followed to initialize a DRHD unit!. we use our
// common sense instead...:p
void _vtd_drhd_initialize(VTD_DRHD *drhd, u32 vtd_ret_paddr)
{
    VTD_GCMD_REG gcmd;
    VTD_GSTS_REG gsts;
    VTD_FECTL_REG fectl;
    VTD_CAP_REG cap;
    VTD_RTADDR_REG rtaddr;
    VTD_CCMD_REG ccmd;
    VTD_IOTLB_REG iotlb;
    bool wbf_required = false;

    // sanity check
    HALT_ON_ERRORCOND(drhd != NULL);

    // check VT-d snoop control capabilities
    {
        VTD_ECAP_REG ecap;
        // read ECAP register
        _vtd_reg(drhd, VTD_REG_READ, VTD_ECAP_REG_OFF, (void *)&ecap.value);

        if (ecap.bits.sc)
            printf("	VT-d hardware Snoop Control (SC) capabilities present\n");
        else
            printf("	VT-d hardware Snoop Control (SC) unavailable\n");

        if (ecap.bits.c) {
            printf("	VT-d hardware access to remapping structures COHERENT\n");
        } else {
            printf("	VT-d hardware access to remapping structures NON-COHERENT\n");
            wbf_required = true;
        }
    }

    // 3. setup fault logging
    printf("	Setting Fault-reporting to NON-INTERRUPT mode...");
    {
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
        // setup RTADDR with base of RET
        rtaddr.value = (u64)vtd_ret_paddr;
        _vtd_reg(drhd, VTD_REG_WRITE, VTD_RTADDR_REG_OFF, (void *)&rtaddr.value);

        // read RTADDR and verify the base address
        rtaddr.value = 0;
        _vtd_reg(drhd, VTD_REG_READ, VTD_RTADDR_REG_OFF, (void *)&rtaddr.value);
        if (rtaddr.value != (u64)vtd_ret_paddr)
        {
            printf("	Failed to set RTADDR. Halting!\n");
            HALT();
        }

        // latch RET address by using GCMD.SRTP
        gcmd.value = 0;
        gcmd.bits.srtp = 1;
        _vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);

        // ensure the RET address was latched by the h/w
        _vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);

        if (!gsts.bits.rtps)
        {
            printf("	Failed to latch RTADDR. Halting!\n");
            HALT();
        }
    }
    printf("Done.\n");

    // 5. invalidate CET cache
    printf("	Invalidating CET cache...");
    {
        // wait for context cache invalidation request to send
#ifndef __XMHF_VERIFICATION__
        do
        {
            _vtd_reg(drhd, VTD_REG_READ, VTD_CCMD_REG_OFF, (void *)&ccmd.value);
        } while (ccmd.bits.icc);
#endif

        // initialize CCMD to perform a global invalidation
        ccmd.value = 0;
        ccmd.bits.cirg = 1; // global invalidation
        ccmd.bits.icc = 1;  // invalidate context cache

        // perform the invalidation
        _vtd_reg(drhd, VTD_REG_WRITE, VTD_CCMD_REG_OFF, (void *)&ccmd.value);

        // wait for context cache invalidation completion status
#ifndef __XMHF_VERIFICATION__
        do
        {
            _vtd_reg(drhd, VTD_REG_READ, VTD_CCMD_REG_OFF, (void *)&ccmd.value);
        } while (ccmd.bits.icc);
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
        // initialize IOTLB to perform a global invalidation
        iotlb.value = 0;
        iotlb.bits.iirg = 1; // global invalidation
        iotlb.bits.ivt = 1;  // invalidate

        // perform the invalidation
        _vtd_reg(drhd, VTD_REG_WRITE, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);

#ifndef __XMHF_VERIFICATION__
        // wait for the invalidation to complete
        do
        {
            _vtd_reg(drhd, VTD_REG_READ, VTD_IOTLB_REG_OFF, (void *)&iotlb.value);
        } while (iotlb.bits.ivt);
#endif

        // if all went well IOTLB IAIG = IOTLB IIRG (i.e., actual = requested invalidation granularity)
        if (iotlb.bits.iaig != 0x1)
        {
            printf("	Invalidation of IOTLB failed. Halting! (%u)\n", iotlb.bits.iaig);
            HALT();
        }
    }
    printf("Done.\n");

    // 7. disable options we dont support
    printf("	Disabling unsupported options...");
    {
        // disable advanced fault logging (AFL)
        gcmd.value = 0;
        gcmd.bits.eafl = 0;
        _vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);
        _vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
        if (gsts.bits.afls)
        {
            printf("	Could not disable AFL. Halting!\n");
            HALT();
        }

        // disabled queued invalidation (QI)
        gcmd.value = 0;
        gcmd.bits.qie = 0;
        _vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);
        _vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
        if (gsts.bits.qies)
        {
            printf("	Could not disable QI. Halting!\n");
            HALT();
        }

        // disable interrupt remapping (IR)
        gcmd.value = 0;
        gcmd.bits.ire = 0;
        _vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);
        _vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
        if (gsts.bits.ires)
        {
            printf("	Could not disable IR. Halting!\n");
            HALT();
        }
    }
    printf("Done.\n");

    // 8. enable device
    printf("	Enabling device...");
    {
        // enable translation
        gcmd.value = 0;
        gcmd.bits.te = 1;
#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
        assert(gcmd.bits.te == 1);
#endif

        _vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);

        // wait for translation enabled status to go green...
        _vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
#ifndef __XMHF_VERIFICATION__
        while (!gsts.bits.tes)
        {
            _vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
        }
#endif
    }
    printf("Done.\n");

    // 9. disable protected memory regions (PMR) if available
    printf("	Checking and disabling PMR...");
    {
        VTD_PMEN_REG pmen;
        _vtd_reg(drhd, VTD_REG_READ, VTD_CAP_REG_OFF, (void *)&cap.value);

        // PMR caps present, so disable it as we dont support that
        if (cap.bits.plmr || cap.bits.phmr)
        {
            _vtd_reg(drhd, VTD_REG_READ, VTD_PMEN_REG_OFF, (void *)&pmen.value);
            pmen.bits.epm = 0; // disable PMR
            _vtd_reg(drhd, VTD_REG_WRITE, VTD_PMEN_REG_OFF, (void *)&pmen.value);
#ifndef __XMHF_VERIFICATION__
            // wait for PMR disabled...
            do
            {
                _vtd_reg(drhd, VTD_REG_READ, VTD_PMEN_REG_OFF, (void *)&pmen.value);
            } while (pmen.bits.prs);
#endif
        }
    }
    printf("Done.\n");

    // 10. perform write buffer flush (WBF)
    if (wbf_required) {
        gcmd.value = 0;
        gcmd.bits.wbf = 1;
        _vtd_reg(drhd, VTD_REG_WRITE, VTD_GCMD_REG_OFF, (void *)&gcmd.value);
        do {
            _vtd_reg(drhd, VTD_REG_READ, VTD_GSTS_REG_OFF, (void *)&gsts.value);
        } while (gsts.bits.wbfs);
    }
}
