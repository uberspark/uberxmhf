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

#include <xmhf.h>
#include <xmhf-debug.h>
#include <xmhf-core.h>

#include <xcihub.h>

/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

//////
XMHF_SLAB_INTERCEPT(xcihub)


static xc_hypapp_info_t _xcihub_hypapp_info_table[] = {
    {
        XMHF_HYP_SLAB_XHHYPERDEP,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_MEMORYFAULT) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },

    {
        XMHF_HYP_SLAB_XHAPPROVEXEC,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_MEMORYFAULT) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },

    {
        XMHF_HYP_SLAB_XHSSTEPTRACE,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_TRAP_EXCEPTION) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },

    {
        XMHF_HYP_SLAB_XHSYSCALLLOG,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_MEMORYFAULT) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_TRAP_INSTRUCTION) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },

};

#define HYPAPP_INFO_TABLE_NUMENTRIES (sizeof(_xcihub_hypapp_info_table)/sizeof(_xcihub_hypapp_info_table[0]))


static u64 _xcihub_hcbinvoke(u64 cbtype, u64 cbqual, u64 guest_slab_index){
    u64 status = XC_HYPAPPCB_CHAIN;
    u64 i;
    xc_hypappcb_inputparams_t hcb_iparams;
    xc_hypappcb_outputparams_t hcb_oparams;

    hcb_iparams.cbtype = cbtype;
    hcb_iparams.cbqual = cbqual;
    hcb_iparams.guest_slab_index = guest_slab_index;

    for(i=0; i < HYPAPP_INFO_TABLE_NUMENTRIES; i++){
        if(_xcihub_hypapp_info_table[i].cbmask & XC_HYPAPPCB_MASK(cbtype)){
            XMHF_SLAB_CALL(hypapp, _xcihub_hypapp_info_table[i].xmhfhic_slab_index, &hcb_iparams, sizeof(hcb_iparams), &hcb_oparams, sizeof(hcb_oparams));
            if(hcb_oparams.cbresult == XC_HYPAPPCB_NOCHAIN){
                status = XC_HYPAPPCB_NOCHAIN;
                break;
            }
        }
    }

    return status;
}


void xcihub_interface(slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 src_slabid, u64 cpuindex){
    u64 info_vmexit_reason;
    xc_hypappcb_inputparams_t hcb_iparams;
    xc_hypappcb_outputparams_t hcb_oparams;

	_XDPRINTF_("%s[%u]: Got control: RSP=%016llx\n",
                __FUNCTION__, (u32)cpuindex, read_rsp());

    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_REASON, &info_vmexit_reason);

    switch(info_vmexit_reason){


        //hypercall
        case VMX_VMEXIT_VMCALL:{
            if(_xcihub_hcbinvoke(XC_HYPAPPCB_HYPERCALL, 0, src_slabid) == XC_HYPAPPCB_CHAIN){
                u64 guest_rip;
                u64 info_vmexit_instruction_length;

                _XDPRINTF_("%s[%u]: VMX_VMEXIT_VMCALL\n", __FUNCTION__, (u32)cpuindex);

                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH, &info_vmexit_instruction_length);
                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_RIP, &guest_rip);
                guest_rip+=info_vmexit_instruction_length;
                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RIP, guest_rip);

                _XDPRINTF_("%s[%u]: adjusted guest_rip=%016llx\n", __FUNCTION__, (u32)cpuindex, guest_rip);
            }
        }
        break;



        //memory fault
		case VMX_VMEXIT_EPT_VIOLATION:{
            _xcihub_hcbinvoke(XC_HYPAPPCB_MEMORYFAULT, 0, src_slabid);
        }
		break;


        //shutdown
        case VMX_VMEXIT_INIT:
   		case VMX_VMEXIT_TASKSWITCH:
            _xcihub_hcbinvoke(XC_HYPAPPCB_SHUTDOWN, 0, src_slabid);
		break;



        ////io traps
		//case VMX_VMEXIT_IOIO:{
        //
        //
		//}
		//break;


        //instruction traps
        case VMX_VMEXIT_CPUID:{
            if(_xcihub_hcbinvoke(XC_HYPAPPCB_TRAP_INSTRUCTION, XC_HYPAPPCB_TRAP_INSTRUCTION_CPUID, src_slabid) == XC_HYPAPPCB_CHAIN){
                u64 guest_rip;
                u64 info_vmexit_instruction_length;
                bool clearsyscallretbit=false;
                x86regs64_t r;

                _XDPRINTF_("%s[%u]: VMX_VMEXIT_CPUID\n",
                    __FUNCTION__, (u32)cpuindex);

                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &r);

                if((u32)r.rax == 0x80000001)
                    clearsyscallretbit = true;

                cpuid((u32)r.rax, (u32 *)&r.rax, (u32 *)&r.rbx, (u32 *)&r.rcx, (u32 *)&r.rdx);

                if(clearsyscallretbit)
                    r.rdx = r.rdx & (u64)~(1ULL << 11);

                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE, &r, NULL);

                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH, &info_vmexit_instruction_length);
                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_RIP, &guest_rip);
                guest_rip+=info_vmexit_instruction_length;
                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RIP, guest_rip);

                _XDPRINTF_("%s[%u]: adjusted guest_rip=%016llx\n",
                    __FUNCTION__, (u32)cpuindex, guest_rip);
            }
        }
        break;


        case VMX_VMEXIT_WRMSR:{
            if(_xcihub_hcbinvoke(XC_HYPAPPCB_TRAP_INSTRUCTION, XC_HYPAPPCB_TRAP_INSTRUCTION_WRMSR, src_slabid) == XC_HYPAPPCB_CHAIN){

                u64 guest_rip;
                u64 info_vmexit_instruction_length;
                x86regs64_t r;

                _XDPRINTF_("%s[%u]: VMX_VMEXIT_WRMSR\n", __FUNCTION__, (u32)cpuindex);

                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &r);

                switch((u32)r.rcx){
                    case IA32_SYSENTER_CS_MSR:
                        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_SYSENTER_CS, ( ((u64)(u32)r.rdx << 32) | (u32)r.rax ));
                        break;
                    case IA32_SYSENTER_EIP_MSR:
                        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_SYSENTER_EIP, ( ((u64)(u32)r.rdx << 32) | (u32)r.rax ));
                        break;
                    case IA32_SYSENTER_ESP_MSR:
                        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_SYSENTER_ESP, ( ((u64)(u32)r.rdx << 32) | (u32)r.rax ));
                        break;
                    default:
                        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_WRMSR, r.rcx, ( ((u64)(u32)r.rdx << 32) | (u32)r.rax ));
                        break;
                }

                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH, &info_vmexit_instruction_length);
                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_RIP, &guest_rip);
                guest_rip+=info_vmexit_instruction_length;
                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RIP, guest_rip);

                _XDPRINTF_("%s[%u]: adjusted guest_rip=%016llx\n",
                    __FUNCTION__, (u32)cpuindex, guest_rip);

            }
        }
        break;


        case VMX_VMEXIT_RDMSR:{
            if(_xcihub_hcbinvoke(XC_HYPAPPCB_TRAP_INSTRUCTION, XC_HYPAPPCB_TRAP_INSTRUCTION_RDMSR, src_slabid) == XC_HYPAPPCB_CHAIN){
                u64 guest_rip, msrvalue;
                u64 info_vmexit_instruction_length;
                x86regs64_t r;

                _XDPRINTF_("%s[%u]: VMX_VMEXIT_RDMSR\n", __FUNCTION__, (u32)cpuindex);

                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &r);

                switch((u32)r.rcx){
                    case IA32_SYSENTER_CS_MSR:
                        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_SYSENTER_CS, &msrvalue);
                        r.rdx = msrvalue >> 32;
                        r.rax = (u32)msrvalue;
                        break;
                    case IA32_SYSENTER_EIP_MSR:
                        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_SYSENTER_EIP, &msrvalue);
                        r.rdx = msrvalue >> 32;
                        r.rax = (u32)msrvalue;
                        break;
                    case IA32_SYSENTER_ESP_MSR:
                        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_SYSENTER_ESP, &msrvalue);
                        r.rdx = msrvalue >> 32;
                        r.rax = (u32)msrvalue;
                        break;
                    default:
                        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_RDMSR, r.rcx, &msrvalue);
                        r.rdx = msrvalue >> 32;
                        r.rax = (u32)msrvalue;
                        break;
                }

                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE, &r, NULL);

                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH, &info_vmexit_instruction_length);
                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_RIP, &guest_rip);
                guest_rip+=info_vmexit_instruction_length;
                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RIP, guest_rip);

                _XDPRINTF_("%s[%u]: adjusted guest_rip=%016llx\n",
                    __FUNCTION__, (u32)cpuindex, guest_rip);
            }

        }
        break;






        //exception traps
        case VMX_VMEXIT_EXCEPTION:{
            _xcihub_hcbinvoke(XC_HYPAPPCB_TRAP_EXCEPTION, 0, src_slabid);
        }
        break;



        default:
            _XDPRINTF_("%s[%u]: unhandled intercept %x. Halting!\n",
                    __FUNCTION__, (u32)cpuindex, info_vmexit_reason);

            HALT();
    }


    //resume guest slab
    return;
}








