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

/*
 * HIC UAPI (micro-API) implementation for XMHF
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>

/////
// forward prototypes

static void __xmhfhic_rtm_uapihandler_cpustate(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid);
static void __xmhfhic_rtm_uapihandler_physmem(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid);
static void __xmhfhic_rtm_uapihandler_mempgtbl(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid);






//////
// main UAPI handler, gets called by a slab
// src_slabid and cpuid are trusted input parameters provided by HIC
void __xmhfhic_rtm_uapihandler(u64 uapicall, u64 uapicall_num, u64 uapicall_subnum,
                               u64 reserved, u64 iparams, u64 oparams,
                               u64 src_slabid, u64 cpuid){

    //_XDPRINTF_("%s[%u]: uapi handler got control: uapicall=%x, uapicall_num=%x, \
    //           uapicall_subnum=%x, iparams=%x, oparams=%x, \
    //           src_slabid=%u, cpuid=%x, return_address=%x, return_rsp=%x, cr3=%x\n",
    //            __FUNCTION__, (u32)cpuid,
    //           uapicall, uapicall_num, uapicall_subnum,
    //           iparams, oparams,
    //           src_slabid, cpuid, return_address, return_rsp, read_cr3());


    //checks
    //1. src_slabid is a hypervisor slab
    if( !(_xmhfhic_common_slab_info_table[src_slabid].archdata.slabtype == HIC_SLAB_X86VMXX86PC_HYPERVISOR) ){
        _XDPRINTF_("%s[%u]: uapierr: src_slabid (%u) is not a hypervisor slab. Halting!\n", __FUNCTION__, (u32)cpuid, src_slabid);
        HALT();
    }
    //2. src_slabid should have capabilities for the requested uapicall_num
    if( !(_xmhfhic_common_slab_info_table[src_slabid].slab_uapicaps & HIC_SLAB_UAPICAP(uapicall_num)) ){
        _XDPRINTF_("%s[%u]: uapierr: src_slabid (%u) does not have uapi capability. Halting!\n", __FUNCTION__, (u32)cpuid, src_slabid);
        HALT();
    }

    switch(uapicall_num){
        case XMHF_HIC_UAPI_CPUSTATE:
            __xmhfhic_rtm_uapihandler_cpustate(uapicall_subnum, iparams, oparams, cpuid);
            break;

        case XMHF_HIC_UAPI_PHYSMEM:
            __xmhfhic_rtm_uapihandler_physmem(uapicall_subnum, iparams, oparams, cpuid);
            break;

        case XMHF_HIC_UAPI_MEMPGTBL:
            __xmhfhic_rtm_uapihandler_mempgtbl(uapicall_subnum, iparams, oparams, cpuid);
            break;

        default:
            _XDPRINTF_("%s[%u]: Unknown UAPI call %x. Halting!\n",
                    __FUNCTION__, (u32)cpuid, uapicall_num);
            HALT();
    }


    return;
}










//////
// cpustate UAPI sub-handler
static void __xmhfhic_rtm_uapihandler_cpustate(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid){
    //_XDPRINTF_("%s[%u]: Got control...\n", __FUNCTION__, (u32)cpuid);

    switch(uapicall_subnum){
        case XMHF_HIC_UAPI_CPUSTATE_VMREAD:{
            //iparams = encoding (u64), oparams = memory (u64 *)
            //checks:
            //1. oparams should be within source slab rwdata or stack memory extents
            //2. encoding cannot contain any value that is specific to HIC
            *(u64 *)oparams = xmhfhw_cpu_x86vmx_vmread(iparams);
        }
        break;

        case XMHF_HIC_UAPI_CPUSTATE_VMWRITE:{
            //iparams = encoding (u64), oparams = value (u64)
            //checks:
            //1. encoding cannot contain any value that is specific to HIC
            xmhfhw_cpu_x86vmx_vmwrite(iparams, oparams);
        }
        break;

        case XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD:{
            //iparams = NULL, oparams = x86regs64_t *
            //checks:
            //1. oparams should be within source slab rwdata or stack memory extents
            memcpy(oparams, & __xmhfhic_x86vmx_archdata[(u32)cpuid].vmx_gprs,
                   sizeof(x86regs64_t));
        }
        break;

        case XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE:{
            //iparams = x86regs64_t *, oparams=NULL
            //checks:
            //1. iparams should be within source slab rwdata, rodata or stack memory extents
            memcpy(& __xmhfhic_x86vmx_archdata[(u32)cpuid].vmx_gprs,
                   iparams,
                   sizeof(x86regs64_t));
        }
        break;

        case XMHF_HIC_UAPI_CPUSTATE_WRMSR:{
            //iparams = msr, oparams = value
            //checks
            //1. msr cannot contain any value that is specific to HIC
            wrmsr64((u32)iparams, oparams);
        }
        break;


        case XMHF_HIC_UAPI_CPUSTATE_RDMSR:{
            //iparams = msr, oparams = (u64 *)
            //checks:
            //1. msr cannot contain any value that is specific to HIC
            //2. oparams should be within source slab rwdata or stack memory extents
            *(u64 *)oparams = rdmsr64((u32)iparams);
        }
        break;

        default:
            _XDPRINTF_("%s[%u]: Unknown cpustate subcall %x. Halting!\n",
                    __FUNCTION__, (u32)cpuid, uapicall_subnum);
            HALT();
    }

}










//////
// physmem UAPI sub-handler
static void __xmhfhic_rtm_uapihandler_physmem(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid){
    //_XDPRINTF_("%s[%u]: Got control...\n", __FUNCTION__, (u32)cpuid);

    switch(uapicall_subnum){
        case XMHF_HIC_UAPI_PHYSMEM_PEEK:{
            //iparams = (xmhf_hic_uapi_physmem_desc_t *), oparams = unused
            //checks:
            //1. iparams is within source slab rwdata or stack section
            //2. destination slab is a guest slab
            //3. pdesc->addr_from and pdesc->numbytes is within destination slab memory extents
            //4. pdesc->addr_to is within source slab memory extents
            xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)iparams;
            memcpy(pdesc->addr_to, pdesc->addr_from, pdesc->numbytes);
        }
        break;

        case XMHF_HIC_UAPI_PHYSMEM_POKE:{
            //iparams = (xmhf_hic_uapi_physmem_desc_t *), oparams = unused
            //1. iparams is within source slab memory extents
            //2. destination slab is a guest slab
            //3. pdesc->addr_to and pdesc->numbytes is within destination slab memory extents
            //4. pdesc->addr_from is within source slab memory extents
            xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)iparams;
            memcpy(pdesc->addr_to, pdesc->addr_from, pdesc->numbytes);
        }
        break;


        default:
            _XDPRINTF_("%s[%u]: Unknown cpustate subcall %x. Halting!\n",
                    __FUNCTION__, (u32)cpuid, uapicall_subnum);
            HALT();

    }

}










//////
// mempgtbl UAPI sub-handler
static void __xmhfhic_rtm_uapihandler_mempgtbl(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid){
    //_XDPRINTF_("%s[%u]: Got control...\n", __FUNCTION__, (u32)cpuid);

    switch(uapicall_subnum){
        case XMHF_HIC_UAPI_MEMPGTBL_GETENTRY:{
            //iparams = xmhf_hic_uapi_mempgtbl_desc_t *; oparams = xmhf_hic_uapi_mempgtbl_desc_t *
            //checks:
            //1. iparams is within source slab memory extents
            //2. oparams is within source slab memory extents
            //3. destination slab (iparams->guest_slab_index) is a guest slab
            //4. iparams->gpa fits within destination slab mempgtbl extents (pdpt_index, pd_index and pt_index bounds)
            xmhf_hic_uapi_mempgtbl_desc_t *imdesc= (xmhf_hic_uapi_mempgtbl_desc_t *)iparams;
            xmhf_hic_uapi_mempgtbl_desc_t *omdesc= (xmhf_hic_uapi_mempgtbl_desc_t *)oparams;

            u64 pdpt_index = pae_get_pdpt_index(imdesc->gpa);
            u64 pd_index = pae_get_pdt_index(imdesc->gpa);
            u64 pt_index = pae_get_pt_index(imdesc->gpa);

            omdesc->entry = _xmhfhic_common_slab_info_table[imdesc->guest_slab_index].archdata.mempgtbl_pt[pdpt_index][pd_index][pt_index];
        }
        break;


        case XMHF_HIC_UAPI_MEMPGTBL_SETENTRY:{
            //iparams = xmhf_hic_uapi_mempgtbl_desc_t *; oparams = unused
            //checks:
            //1. iparams is within source slab memory extents
            //2. destination slab (iparams->guest_slab_index) is a guest slab
            //3. iparams->gpa fits within destination slab mempgtbl extents (pdpt_index, pd_index and pt_index bounds)
            //4. if iparams->entry has present bit set then entry is within destination slab memory extents
            xmhf_hic_uapi_mempgtbl_desc_t *imdesc= (xmhf_hic_uapi_mempgtbl_desc_t *)iparams;

            u64 pdpt_index = pae_get_pdpt_index(imdesc->gpa);
            u64 pd_index = pae_get_pdt_index(imdesc->gpa);
            u64 pt_index = pae_get_pt_index(imdesc->gpa);

            _xmhfhic_common_slab_info_table[imdesc->guest_slab_index].archdata.mempgtbl_pt[pdpt_index][pd_index][pt_index] = imdesc->entry;

        }
        break;


        default:
            _XDPRINTF_("%s[%u]: Unknown cpustate subcall %x. Halting!\n",
                    __FUNCTION__, (u32)cpuid, uapicall_subnum);
            HALT();

    }

}


