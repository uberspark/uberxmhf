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
#include <xmhfgeec.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <xc_ihub.h>
#include <uapi_gcpustate.h>
#include <uapi_hcpustate.h>
#include <xh_hyperdep.h>
#include <xh_syscalllog.h>
#include <xh_ssteptrace.h>
#include <xh_approvexec.h>

/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

//////
//XMHF_SLAB_INTERCEPT(xcihub)




void slab_main(slab_params_t *sp){
	u32 info_vmexit_reason;
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;
	xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs = (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
	xmhf_uapi_hcpustate_msr_params_t *hcpustate_msrp = (xmhf_uapi_hcpustate_msr_params_t *)spl.in_out_params;

	_XDPRINTF_("XCIHUB[%u]: Got control: src=%u, dst=%u, esp=%08x, eflags=%08x\n",
		(u16)sp->cpuid, sp->src_slabid, sp->dst_slabid, CASM_FUNCCALL(read_esp,CASM_NOPARAM),
			CASM_FUNCCALL(read_eflags, CASM_NOPARAM));

	spl.cpuid = sp->cpuid;
	spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;


	//store GPRs
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE;
	memcpy(&gcpustate_gprs->gprs, &sp->in_out_params[0], sizeof(x86regs_t));
	XMHF_SLAB_CALLNEW(&spl);

	//grab exit reason
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
	gcpustate_vmrwp->encoding = VMCS_INFO_VMEXIT_REASON;
	XMHF_SLAB_CALLNEW(&spl);
	info_vmexit_reason = gcpustate_vmrwp->value;

	switch(info_vmexit_reason){

		//hypercall
		case VMX_VMEXIT_VMCALL:{
		    if(xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, sp->cpuid, XC_HYPAPPCB_HYPERCALL, 0, sp->src_slabid) == XC_HYPAPPCB_CHAIN){
			xcihub_icptvmcall((u16)sp->cpuid);
			}
		}
		break;


        //memory fault
		case VMX_VMEXIT_EPT_VIOLATION:{
            xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, sp->cpuid, XC_HYPAPPCB_MEMORYFAULT, 0, sp->src_slabid);
        }
		break;


        //shutdown
        case VMX_VMEXIT_INIT:
   		case VMX_VMEXIT_TASKSWITCH:
            xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, sp->cpuid, XC_HYPAPPCB_SHUTDOWN, 0, sp->src_slabid);
		break;



        ////io traps
		//case VMX_VMEXIT_IOIO:{
        //
        //
		//}
		//break;


        //instruction traps
        case VMX_VMEXIT_CPUID:{
            if(xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, sp->cpuid, XC_HYPAPPCB_TRAP_INSTRUCTION,
                            XC_HYPAPPCB_TRAP_INSTRUCTION_CPUID, sp->src_slabid) == XC_HYPAPPCB_CHAIN){
                u32 guest_rip;
                u32 info_vmexit_instruction_length;
                //bool clearsyscallretbit=false; //x86_64
                x86regs_t r;

                _XDPRINTF_("%s[%u]: VMX_VMEXIT_CPUID\n",
                    __func__, (u16)sp->cpuid);

                spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
                XMHF_SLAB_CALLNEW(&spl);
                memcpy(&r, &gcpustate_gprs->gprs, sizeof(x86regs_t));

                //x86_64
                //if((u32)r.eax == 0x80000001)
                //    clearsyscallretbit = true;

 CASM_FUNCCALL(xmhfhw_cpu_cpuid,(u32)r.eax, (u32 *)&r.eax, (u32 *)&r.ebx, (u32 *)&r.ecx, (u32 *)&r.edx);

                //x86_64
                //if(clearsyscallretbit)
                //    r.edx = r.edx & (u64)~(1ULL << 11);

                spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE;
                memcpy(&gcpustate_gprs->gprs, &r, sizeof(x86regs_t));
                XMHF_SLAB_CALLNEW(&spl);

                {
                    spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
                    gcpustate_vmrwp->encoding = VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH;
                    XMHF_SLAB_CALLNEW(&spl);
                    info_vmexit_instruction_length = gcpustate_vmrwp->value;
                }

                {
                    gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
                    XMHF_SLAB_CALLNEW(&spl);
                    guest_rip = gcpustate_vmrwp->value;
                    guest_rip+=info_vmexit_instruction_length;
                }

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RIP, guest_rip);
                spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
                gcpustate_vmrwp->value = guest_rip;
                XMHF_SLAB_CALLNEW(&spl);

                _XDPRINTF_("%s[%u]: adjusted guest_rip=%08x\n",
                    __func__, (u16)sp->cpuid, guest_rip);
            }
        }
        break;


        case VMX_VMEXIT_WRMSR:{

            if(xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, sp->cpuid,
                            XC_HYPAPPCB_TRAP_INSTRUCTION, XC_HYPAPPCB_TRAP_INSTRUCTION_WRMSR, sp->src_slabid) == XC_HYPAPPCB_CHAIN)
            {

                u32 guest_rip;
                u32 info_vmexit_instruction_length;
                x86regs_t r;

                _XDPRINTF_("%s[%u]: VMX_VMEXIT_WRMSR\n", __func__, (u16)sp->cpuid);

                spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
                XMHF_SLAB_CALLNEW(&spl);
                memcpy(&r, &gcpustate_gprs->gprs, sizeof(x86regs_t));

                switch((u32)r.ecx){
                    case IA32_SYSENTER_CS_MSR:
                        spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                        gcpustate_vmrwp->encoding = VMCS_GUEST_SYSENTER_CS;
                        gcpustate_vmrwp->value = r.eax;
                        XMHF_SLAB_CALLNEW(&spl);
                        break;
                    case IA32_SYSENTER_EIP_MSR:
                        spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                        gcpustate_vmrwp->encoding = VMCS_GUEST_SYSENTER_EIP;
                        gcpustate_vmrwp->value = r.eax;
                        XMHF_SLAB_CALLNEW(&spl);
                        break;
                    case IA32_SYSENTER_ESP_MSR:
                        spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                        gcpustate_vmrwp->encoding = VMCS_GUEST_SYSENTER_ESP;
                        gcpustate_vmrwp->value = r.eax;
                        XMHF_SLAB_CALLNEW(&spl);
                        break;
                    default:
                        spl.dst_slabid = XMHFGEEC_SLAB_UAPI_HCPUSTATE;
                        spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_WRMSR;
                        hcpustate_msrp->msr = r.ecx;
                        hcpustate_msrp->value = ((u64)r.edx << 32) | (u64)r.eax;
                        XMHF_SLAB_CALLNEW(&spl);
                        break;
                }

                {
                    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
                    spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
                    gcpustate_vmrwp->encoding = VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH;
                    XMHF_SLAB_CALLNEW(&spl);
                    info_vmexit_instruction_length = gcpustate_vmrwp->value;
                }

                {
                    gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
                    XMHF_SLAB_CALLNEW(&spl);
                    guest_rip = gcpustate_vmrwp->value;
                    guest_rip+=info_vmexit_instruction_length;
                }

                spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
                gcpustate_vmrwp->value = guest_rip;
                XMHF_SLAB_CALLNEW(&spl);

                _XDPRINTF_("%s[%u]: adjusted guest_rip=%08x\n",
                    __func__, (u16)sp->cpuid, guest_rip);

            }
        }
        break;


        case VMX_VMEXIT_RDMSR:{
            if(xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, sp->cpuid, XC_HYPAPPCB_TRAP_INSTRUCTION,
                            XC_HYPAPPCB_TRAP_INSTRUCTION_RDMSR, sp->src_slabid) == XC_HYPAPPCB_CHAIN)
            {
                u32 guest_rip;
                u64 msrvalue;
                u32 info_vmexit_instruction_length;
                x86regs_t r;

                _XDPRINTF_("%s[%u]: VMX_VMEXIT_RDMSR\n", __func__, (u16)sp->cpuid);

                spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
                XMHF_SLAB_CALLNEW(&spl);
                memcpy(&r, &gcpustate_gprs->gprs, sizeof(x86regs_t));


                switch((u32)r.ecx){
                    case IA32_SYSENTER_CS_MSR:
                        {
                            spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
                            gcpustate_vmrwp->encoding = VMCS_GUEST_SYSENTER_CS;
                            XMHF_SLAB_CALLNEW(&spl);
                            r.edx = 0;
                            r.eax = gcpustate_vmrwp->value;
                        }
                        break;
                    case IA32_SYSENTER_EIP_MSR:
                        spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
                        gcpustate_vmrwp->encoding = VMCS_GUEST_SYSENTER_EIP;
                        XMHF_SLAB_CALLNEW(&spl);
                        r.edx = 0;
                        r.eax = gcpustate_vmrwp->value;
                        break;
                    case IA32_SYSENTER_ESP_MSR:
                        spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
                        gcpustate_vmrwp->encoding = VMCS_GUEST_SYSENTER_ESP;
                        XMHF_SLAB_CALLNEW(&spl);
                        r.edx = 0;
                        r.eax = gcpustate_vmrwp->value;
                        break;
                    default:
                        spl.dst_slabid = XMHFGEEC_SLAB_UAPI_HCPUSTATE;
                        spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_RDMSR;
                        hcpustate_msrp->msr = r.ecx;
                        XMHF_SLAB_CALLNEW(&spl);
                        r.edx = (u32)((u64)hcpustate_msrp->value >> 32);
                        r.eax = (u32)hcpustate_msrp->value;
                        break;
                }

                spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
                spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE;
                memcpy(&gcpustate_gprs->gprs, &r, sizeof(x86regs_t));
                XMHF_SLAB_CALLNEW(&spl);

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

                _XDPRINTF_("%s[%u]: adjusted guest_rip=%08x\n",
                    __func__, (u16)sp->cpuid, guest_rip);
            }

        }
        break;


        //exception traps
        case VMX_VMEXIT_EXCEPTION:{
            xc_hcbinvoke(XMHFGEEC_SLAB_XC_IHUB, sp->cpuid, XC_HYPAPPCB_TRAP_EXCEPTION, 0, sp->src_slabid);
        }
        break;


        default:
            _XDPRINTF_("%s[%u]: unhandled intercept %x. Halting!\n",
                    __func__, (u16)sp->cpuid, info_vmexit_reason);

            HALT();
    }



    //load GPRs
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
    XMHF_SLAB_CALLNEW(&spl);
    memcpy(&sp->in_out_params[0], &gcpustate_gprs->gprs, sizeof(x86regs_t));


    _XDPRINTF_("XCIHUB[%u]: Resuming guest, esp=%08x\n", (u16)sp->cpuid, CASM_FUNCCALL(read_esp,CASM_NOPARAM));


    //resume guest slab
    return;
}







