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
#include <xmhfhicslab.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <xcihub.h>

/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

//////
XMHF_SLAB_INTERCEPT(xcihub)



void slab_main(slab_params_t *sp){
    u32 info_vmexit_reason;
    slab_params_t spl;

	_XDPRINTF_("%s[%u]: Got control: ESP=%08x\n",
                __FUNCTION__, (u16)sp->cpuid, read_esp());

    spl.cpuid = sp->cpuid;
    spl.src_slabid = XMHF_HYP_SLAB_XCIHUB;
    spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;


    //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_REASON, &info_vmexit_reason);
    spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
    spl.in_out_params[2] = VMCS_INFO_VMEXIT_REASON;
    XMHF_SLAB_UAPI(&spl);
    info_vmexit_reason = spl.in_out_params[4];

    switch(info_vmexit_reason){

        //hypercall
        case VMX_VMEXIT_VMCALL:{
            if(xc_hcbinvoke(XMHF_HYP_SLAB_XCIHUB, sp->cpuid, XC_HYPAPPCB_HYPERCALL, 0, sp->src_slabid) == XC_HYPAPPCB_CHAIN){
                u32 guest_rip;
                u32 info_vmexit_instruction_length;

                _XDPRINTF_("%s[%u]: VMX_VMEXIT_VMCALL\n", __FUNCTION__, (u16)sp->cpuid);

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH, &info_vmexit_instruction_length);
                spl.in_out_params[2] = VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH;
                XMHF_SLAB_UAPI(&spl);
                info_vmexit_instruction_length = spl.in_out_params[4];

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_RIP, &guest_rip);
                spl.in_out_params[2] = VMCS_GUEST_RIP;
                XMHF_SLAB_UAPI(&spl);
                guest_rip = spl.in_out_params[4];
                guest_rip+=info_vmexit_instruction_length;

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RIP, guest_rip);
                spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                spl.in_out_params[2] = VMCS_GUEST_RIP;
                spl.in_out_params[4] = guest_rip;
                XMHF_SLAB_UAPI(&spl);

                _XDPRINTF_("%s[%u]: adjusted guest_rip=%08x\n", __FUNCTION__, (u16)sp->cpuid, guest_rip);
            }
        }
        break;


        //memory fault
		case VMX_VMEXIT_EPT_VIOLATION:{
            xc_hcbinvoke(XMHF_HYP_SLAB_XCIHUB, sp->cpuid, XC_HYPAPPCB_MEMORYFAULT, 0, sp->src_slabid);
        }
		break;


        //shutdown
        case VMX_VMEXIT_INIT:
   		case VMX_VMEXIT_TASKSWITCH:
            xc_hcbinvoke(XMHF_HYP_SLAB_XCIHUB, sp->cpuid, XC_HYPAPPCB_SHUTDOWN, 0, sp->src_slabid);
		break;



        ////io traps
		//case VMX_VMEXIT_IOIO:{
        //
        //
		//}
		//break;


        //instruction traps
        case VMX_VMEXIT_CPUID:{
            if(xc_hcbinvoke(XMHF_HYP_SLAB_XCIHUB, sp->cpuid, XC_HYPAPPCB_TRAP_INSTRUCTION,
                            XC_HYPAPPCB_TRAP_INSTRUCTION_CPUID, sp->src_slabid) == XC_HYPAPPCB_CHAIN){
                u32 guest_rip;
                u32 info_vmexit_instruction_length;
                //bool clearsyscallretbit=false; //x86_64
                x86regs_t r;

                _XDPRINTF_("%s[%u]: VMX_VMEXIT_CPUID\n",
                    __FUNCTION__, (u16)sp->cpuid);

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &r);
                spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
                XMHF_SLAB_UAPI(&spl);
                memcpy(&r, &spl.in_out_params[2], sizeof(x86regs_t));

                //x86_64
                //if((u32)r.eax == 0x80000001)
                //    clearsyscallretbit = true;

                xmhfhw_cpu_cpuid((u32)r.eax, (u32 *)&r.eax, (u32 *)&r.ebx, (u32 *)&r.ecx, (u32 *)&r.edx);

                //x86_64
                //if(clearsyscallretbit)
                //    r.edx = r.edx & (u64)~(1ULL << 11);

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE, &r, NULL);
                spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE;
                memcpy(&spl.in_out_params[2], &r, sizeof(x86regs_t));
                XMHF_SLAB_UAPI(&spl);

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH, &info_vmexit_instruction_length);
                spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
                spl.in_out_params[2] = VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH;
                XMHF_SLAB_UAPI(&spl);
                info_vmexit_instruction_length = spl.in_out_params[4];

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_RIP, &guest_rip);
                spl.in_out_params[2] = VMCS_GUEST_RIP;
                XMHF_SLAB_UAPI(&spl);
                guest_rip = spl.in_out_params[4];
                guest_rip+=info_vmexit_instruction_length;

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RIP, guest_rip);
                spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                spl.in_out_params[2] = VMCS_GUEST_RIP;
                spl.in_out_params[4] = guest_rip;
                XMHF_SLAB_UAPI(&spl);

                _XDPRINTF_("%s[%u]: adjusted guest_rip=%08x\n",
                    __FUNCTION__, (u16)sp->cpuid, guest_rip);
            }
        }
        break;


        case VMX_VMEXIT_WRMSR:{

            //if(xc_hcbinvoke(XMHF_HYP_SLAB_XCIHUB, sp->cpuid,
            //                XC_HYPAPPCB_TRAP_INSTRUCTION, XC_HYPAPPCB_TRAP_INSTRUCTION_WRMSR, sp->src_slabid) == XC_HYPAPPCB_CHAIN)
            {

                u32 guest_rip;
                u32 info_vmexit_instruction_length;
                x86regs_t r;

                _XDPRINTF_("%s[%u]: VMX_VMEXIT_WRMSR\n", __FUNCTION__, (u16)sp->cpuid);

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &r);
                spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
                XMHF_SLAB_UAPI(&spl);
                memcpy(&r, &spl.in_out_params[2], sizeof(x86regs_t));

                switch((u32)r.ecx){
                    case IA32_SYSENTER_CS_MSR:
                        //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_SYSENTER_CS, ( ((u64)(u32)r.rdx << 32) | (u32)r.rax ));
                        spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                        spl.in_out_params[2] = VMCS_GUEST_SYSENTER_CS;
                        spl.in_out_params[4] = r.eax;
                        XMHF_SLAB_UAPI(&spl);
                        break;
                    case IA32_SYSENTER_EIP_MSR:
                        //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_SYSENTER_EIP, ( ((u64)(u32)r.rdx << 32) | (u32)r.rax ));
                        spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                        spl.in_out_params[2] = VMCS_GUEST_SYSENTER_EIP;
                        spl.in_out_params[4] = r.eax;
                        XMHF_SLAB_UAPI(&spl);
                        break;
                    case IA32_SYSENTER_ESP_MSR:
                        //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_SYSENTER_ESP, ( ((u64)(u32)r.rdx << 32) | (u32)r.rax ));
                        spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                        spl.in_out_params[2] = VMCS_GUEST_SYSENTER_ESP;
                        spl.in_out_params[4] = r.eax;
                        XMHF_SLAB_UAPI(&spl);
                        break;
                    default:
                        //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_WRMSR, r.rcx, ( ((u64)(u32)r.rdx << 32) | (u32)r.rax ));
                        spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_WRMSR;
                        spl.in_out_params[2] = r.ecx;
                        spl.in_out_params[3] = r.eax;
                        spl.in_out_params[4] = r.edx;
                        XMHF_SLAB_UAPI(&spl);
                        break;
                }

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH, &info_vmexit_instruction_length);
                spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
                spl.in_out_params[2] = VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH;
                XMHF_SLAB_UAPI(&spl);
                info_vmexit_instruction_length = spl.in_out_params[4];

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_RIP, &guest_rip);
                spl.in_out_params[2] = VMCS_GUEST_RIP;
                XMHF_SLAB_UAPI(&spl);
                guest_rip = spl.in_out_params[4];
                guest_rip+=info_vmexit_instruction_length;

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RIP, guest_rip);
                spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                spl.in_out_params[2] = VMCS_GUEST_RIP;
                spl.in_out_params[4] = guest_rip;
                XMHF_SLAB_UAPI(&spl);

                _XDPRINTF_("%s[%u]: adjusted guest_rip=%08x\n",
                    __FUNCTION__, (u16)sp->cpuid, guest_rip);

            }
        }
        break;


        case VMX_VMEXIT_RDMSR:{
            //if(xc_hcbinvoke(XMHF_HYP_SLAB_XCIHUB, sp->cpuid, XC_HYPAPPCB_TRAP_INSTRUCTION,
            //                XC_HYPAPPCB_TRAP_INSTRUCTION_RDMSR, sp->src_slabid) == XC_HYPAPPCB_CHAIN)
            {
                u32 guest_rip;
                u64 msrvalue;
                u32 info_vmexit_instruction_length;
                x86regs_t r;

                _XDPRINTF_("%s[%u]: VMX_VMEXIT_RDMSR\n", __FUNCTION__, (u16)sp->cpuid);

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &r);
                spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
                XMHF_SLAB_UAPI(&spl);
                memcpy(&r, &spl.in_out_params[2], sizeof(x86regs_t));


                switch((u32)r.ecx){
                    case IA32_SYSENTER_CS_MSR:
                        //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_SYSENTER_CS, &msrvalue);
                        spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
                        spl.in_out_params[2] = VMCS_GUEST_SYSENTER_CS;
                        XMHF_SLAB_UAPI(&spl);
                        r.edx = 0;
                        r.eax = spl.in_out_params[4];
                        break;
                    case IA32_SYSENTER_EIP_MSR:
                        //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_SYSENTER_EIP, &msrvalue);
                        spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
                        spl.in_out_params[2] = VMCS_GUEST_SYSENTER_EIP;
                        XMHF_SLAB_UAPI(&spl);
                        r.edx = 0;
                        r.eax = spl.in_out_params[4];
                        break;
                    case IA32_SYSENTER_ESP_MSR:
                        //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_SYSENTER_ESP, &msrvalue);
                        spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
                        spl.in_out_params[2] = VMCS_GUEST_SYSENTER_ESP;
                        XMHF_SLAB_UAPI(&spl);
                        r.edx = 0;
                        r.eax = spl.in_out_params[4];
                        break;
                    default:
                        //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_RDMSR, r.rcx, &msrvalue);
                        spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_RDMSR;
                        spl.in_out_params[2] = r.ecx;
                        XMHF_SLAB_UAPI(&spl);
                        r.edx = spl.in_out_params[4];
                        r.eax = spl.in_out_params[3];
                        break;
                }

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE, &r, NULL);
                spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE;
                memcpy(&spl.in_out_params[2], &r, sizeof(x86regs_t));
                XMHF_SLAB_UAPI(&spl);

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH, &info_vmexit_instruction_length);
                spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
                spl.in_out_params[2] = VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH;
                XMHF_SLAB_UAPI(&spl);
                info_vmexit_instruction_length = spl.in_out_params[4];

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_RIP, &guest_rip);
                spl.in_out_params[2] = VMCS_GUEST_RIP;
                XMHF_SLAB_UAPI(&spl);
                guest_rip = spl.in_out_params[4];
                guest_rip+=info_vmexit_instruction_length;

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RIP, guest_rip);
                spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                spl.in_out_params[2] = VMCS_GUEST_RIP;
                spl.in_out_params[4] = guest_rip;
                XMHF_SLAB_UAPI(&spl);

                _XDPRINTF_("%s[%u]: adjusted guest_rip=%08x\n",
                    __FUNCTION__, (u16)sp->cpuid, guest_rip);
            }

        }
        break;


        //exception traps
        case VMX_VMEXIT_EXCEPTION:{
            xc_hcbinvoke(XMHF_HYP_SLAB_XCIHUB, sp->cpuid, XC_HYPAPPCB_TRAP_EXCEPTION, 0, sp->src_slabid);
        }
        break;


        default:
            _XDPRINTF_("%s[%u]: unhandled intercept %x. Halting!\n",
                    __FUNCTION__, (u16)sp->cpuid, info_vmexit_reason);

            HALT();
    }


    //resume guest slab
    return;
}




/*
void slab_interface(slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 src_slabid, u64 cpuindex){
    u64 info_vmexit_reason;
    xc_hypappcb_inputparams_t hcb_iparams;
    xc_hypappcb_outputparams_t hcb_oparams;

	_XDPRINTF_("%s[%u]: Got control: RSP=%016llx\n",
                __FUNCTION__, (u32)cpuindex, read_rsp());

    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_REASON, &info_vmexit_reason);

    switch(info_vmexit_reason){


        //hypercall
        case VMX_VMEXIT_VMCALL:{
            if(xc_hcbinvoke(XC_HYPAPPCB_HYPERCALL, 0, src_slabid) == XC_HYPAPPCB_CHAIN){
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
            xc_hcbinvoke(XC_HYPAPPCB_MEMORYFAULT, 0, src_slabid);
        }
		break;


        //shutdown
        case VMX_VMEXIT_INIT:
   		case VMX_VMEXIT_TASKSWITCH:
            xc_hcbinvoke(XC_HYPAPPCB_SHUTDOWN, 0, src_slabid);
		break;



        ////io traps
		//case VMX_VMEXIT_IOIO:{
        //
        //
		//}
		//break;


        //instruction traps
        case VMX_VMEXIT_CPUID:{
            if(xc_hcbinvoke(XC_HYPAPPCB_TRAP_INSTRUCTION, XC_HYPAPPCB_TRAP_INSTRUCTION_CPUID, src_slabid) == XC_HYPAPPCB_CHAIN){
                u64 guest_rip;
                u64 info_vmexit_instruction_length;
                bool clearsyscallretbit=false;
                x86regs64_t r;

                _XDPRINTF_("%s[%u]: VMX_VMEXIT_CPUID\n",
                    __FUNCTION__, (u32)cpuindex);

                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &r);

                if((u32)r.rax == 0x80000001)
                    clearsyscallretbit = true;

                xmhfhw_cpu_cpuid((u32)r.rax, (u32 *)&r.rax, (u32 *)&r.rbx, (u32 *)&r.rcx, (u32 *)&r.rdx);

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

            if(xc_hcbinvoke(XC_HYPAPPCB_TRAP_INSTRUCTION, XC_HYPAPPCB_TRAP_INSTRUCTION_WRMSR, src_slabid) == XC_HYPAPPCB_CHAIN){

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
            if(xc_hcbinvoke(XC_HYPAPPCB_TRAP_INSTRUCTION, XC_HYPAPPCB_TRAP_INSTRUCTION_RDMSR, src_slabid) == XC_HYPAPPCB_CHAIN){
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
            xc_hcbinvoke(XC_HYPAPPCB_TRAP_EXCEPTION, 0, src_slabid);
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
*/







