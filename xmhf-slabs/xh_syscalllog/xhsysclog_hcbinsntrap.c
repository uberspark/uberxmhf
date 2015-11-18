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

// syscalllog hypapp main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhfgeec.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <uapi_gcpustate.h>
//#include <uapi_slabmemacc.h>
#include <uapi_slabmempgtbl.h>

#include <xh_syscalllog.h>


// instruction trap
u32 sysclog_hcbinsntrap(u32 cpuindex, u32 guest_slab_index, u32 insntype){
    slab_params_t spl;
    xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp =
        (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;
    xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs =
        (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
    u32 status=XC_HYPAPPCB_CHAIN;
    u32 guest_rip, msrvalue;
    u32 info_vmexit_instruction_length;
    x86regs_t *r = (x86regs_t *)&gcpustate_gprs->gprs;

    if(!_sl_registered)
        return status;

    spl.src_slabid = XMHFGEEC_SLAB_XH_SYSCALLLOG;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.cpuid = cpuindex;
    //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;


    if (insntype == XC_HYPAPPCB_TRAP_INSTRUCTION_WRMSR){

         spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
        XMHF_SLAB_CALLNEW(&spl);
        msrvalue = r->ecx;

        switch(msrvalue){
            case IA32_SYSENTER_EIP_MSR:{
                //xmhf_hic_uapi_mempgtbl_desc_t *mdesc = (xmhf_hic_uapi_mempgtbl_desc_t *)&spl.in_out_params[2];
                //xmhf_uapi_slabmempgtbl_entry_params_t *smpgtblep =
                //    (xmhf_uapi_slabmempgtbl_entry_params_t *)spl.in_out_params;
                xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *getentryforpaddrp =
                (xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *)spl.in_out_params;
                xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
                (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;


              	_XDPRINTF_("%s[%u]: emulating WRMSR SYSENTER_EIP_MSR\n", __func__, (u16)cpuindex);

                shadow_sysenter_rip = ( ((u64)(u32)r->edx << 32) | (u32)r->eax ) ;

                 spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                gcpustate_vmrwp->encoding = VMCS_GUEST_SYSENTER_EIP;
                gcpustate_vmrwp->value = 0;
                XMHF_SLAB_CALLNEW(&spl);

                if(!sl_activated){
                    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;

                     spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR;
                    getentryforpaddrp->dst_slabid = guest_slab_index;
                    getentryforpaddrp->gpa = 0;
                    XMHF_SLAB_CALLNEW(&spl);

                     spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
                    setentryforpaddrp->dst_slabid = guest_slab_index;
                    setentryforpaddrp->gpa = 0;
                    setentryforpaddrp->entry = getentryforpaddrp->result_entry & ~(0x7);
                    XMHF_SLAB_CALLNEW(&spl);

                    sl_activated=true;
                }

                status = XC_HYPAPPCB_NOCHAIN;
            }
            break;

            default:
                break;
        }

    }else if (insntype == XC_HYPAPPCB_TRAP_INSTRUCTION_RDMSR){

         spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
        XMHF_SLAB_CALLNEW(&spl);
        msrvalue = r->ecx;

        switch(msrvalue){
            case IA32_SYSENTER_EIP_MSR:
              	_XDPRINTF_("%s[%u]: emulating RDMSR SYSENTER_EIP_MSR\n", __func__, (u16)cpuindex);

                r->edx = shadow_sysenter_rip >> 32;
                r->eax = (u32)shadow_sysenter_rip;

                 spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE;
                XMHF_SLAB_CALLNEW(&spl);

                status = XC_HYPAPPCB_NOCHAIN;
                break;
            default:
                break;
        }

    }else{ //some instruction we don't care about, so just fall through


    }

    //if we emulated the instruction then do not chain, but update instruction pointer
    //accordingly
    if(status == XC_HYPAPPCB_NOCHAIN){
        spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
        //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;

         spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
        gcpustate_vmrwp->encoding = VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH;
        XMHF_SLAB_CALLNEW(&spl);
        info_vmexit_instruction_length = gcpustate_vmrwp->value;

        gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
        XMHF_SLAB_CALLNEW(&spl);
        guest_rip = gcpustate_vmrwp->value;

        guest_rip+=info_vmexit_instruction_length;

         spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
        gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
        gcpustate_vmrwp->value = guest_rip;
        XMHF_SLAB_CALLNEW(&spl);
    }

    return status;
}

