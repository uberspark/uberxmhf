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
 * slab trampoline that is mapped into every slab memory view
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>



//////////////////////////////////////////////////////////////////////////////
// HIC UAPI


static void __xmhfhic_rtm_uapihandler_mempgtbl(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid){
    //_XDPRINTF_("%s[%u]: Got control...\n",
    //            __FUNCTION__, (u32)cpuid);

    switch(uapicall_subnum){
        case XMHF_HIC_UAPI_MEMPGTBL_GETENTRY:{
            xmhf_hic_uapi_mempgtbl_desc_t *imdesc= (xmhf_hic_uapi_mempgtbl_desc_t *)iparams;
            xmhf_hic_uapi_mempgtbl_desc_t *omdesc= (xmhf_hic_uapi_mempgtbl_desc_t *)oparams;

            u64 pdpt_index = pae_get_pdpt_index(imdesc->gpa);
            u64 pd_index = pae_get_pdt_index(imdesc->gpa);
            u64 pt_index = pae_get_pt_index(imdesc->gpa);

            omdesc->entry = _xmhfhic_common_slab_info_table[imdesc->guest_slab_index].archdata.mempgtbl_pt[pdpt_index][pd_index][pt_index];
        }
        break;


        case XMHF_HIC_UAPI_MEMPGTBL_SETENTRY:{
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


static void __xmhfhic_rtm_uapihandler_physmem(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid){
    //_XDPRINTF_("%s[%u]: Got control...\n",
    //            __FUNCTION__, (u32)cpuid);

    switch(uapicall_subnum){
        case XMHF_HIC_UAPI_PHYSMEM_PEEK:{
            xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)iparams;
            memcpy(pdesc->addr_to, pdesc->addr_from, pdesc->numbytes);
        }
        break;


        case XMHF_HIC_UAPI_PHYSMEM_POKE:{
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



static void __xmhfhic_rtm_uapihandler_cpustate(u64 uapicall_subnum, u64 iparams, u64 oparams, u64 cpuid){
    //_XDPRINTF_("%s[%u]: Got control...\n",
    //            __FUNCTION__, (u32)cpuid);


    switch(uapicall_subnum){
        case XMHF_HIC_UAPI_CPUSTATE_VMREAD:{
            //iparams = encoding (u64), oparams = memory (u64 *)
            *(u64 *)oparams = xmhfhw_cpu_x86vmx_vmread(iparams);
        }
        break;

        case XMHF_HIC_UAPI_CPUSTATE_VMWRITE:{
            //iparams = encoding (u64), oparams = value (u64)
            xmhfhw_cpu_x86vmx_vmwrite(iparams, oparams);
        }
        break;

        case XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD:{
            //iparams = NULL, oparams = x86regs64_t *
            memcpy(oparams, & __xmhfhic_x86vmx_archdata[(u32)cpuid].vmx_gprs,
                   sizeof(x86regs64_t));
        }
        break;

        case XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE:{
            //iparams = x86regs64_t *, oparams=NULL
            memcpy(& __xmhfhic_x86vmx_archdata[(u32)cpuid].vmx_gprs,
                   iparams,
                   sizeof(x86regs64_t));
        }
        break;

        case XMHF_HIC_UAPI_CPUSTATE_WRMSR:{
            //iparams = msr, oparams = value
            wrmsr64((u32)iparams, oparams);
        }
        break;


        case XMHF_HIC_UAPI_CPUSTATE_RDMSR:{
            //iparams = msr, oparams = (u64 *)
            *(u64 *)oparams = rdmsr64((u32)iparams);
        }
        break;

        default:
            _XDPRINTF_("%s[%u]: Unknown cpustate subcall %x. Halting!\n",
                    __FUNCTION__, (u32)cpuid, uapicall_subnum);
            HALT();
    }

}


void __xmhfhic_rtm_uapihandler(u64 uapicall, u64 uapicall_num, u64 uapicall_subnum,
                               u64 reserved, u64 iparams, u64 oparams,  u64 src_slabid, u64 cpuid, u64 return_address, u64 return_rsp){

    //_XDPRINTF_("%s[%u]: uapi handler got control: uapicall=%x, uapicall_num=%x, \
    //           uapicall_subnum=%x, iparams=%x, oparams=%x, \
    //           src_slabid=%u, cpuid=%x, return_address=%x, return_rsp=%x, cr3=%x\n",
    //            __FUNCTION__, (u32)cpuid,
    //           uapicall, uapicall_num, uapicall_subnum,
    //           iparams, oparams,
    //           src_slabid, cpuid, return_address, return_rsp, read_cr3());


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


