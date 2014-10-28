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

#include <xcihub.h>

//////
XMHF_SLAB_INTERCEPT(xcihub)

/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

void xcihub_interface(slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 src_slabid, u64 cpuindex){
    u64 info_vmexit_reason;

	_XDPRINTF_("%s[%u]: Got control: RSP=%016llx\n",
                __FUNCTION__, (u32)cpuindex, read_rsp());

    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_REASON, &info_vmexit_reason);

    switch(info_vmexit_reason){


        //hypercall
        case VMX_VMEXIT_VMCALL:{
            u64 guest_rip;
            u64 info_vmexit_instruction_length;

            _XDPRINTF_("%s[%u]: VMX_VMEXIT_VMCALL\n",
                __FUNCTION__, (u32)cpuindex);

            XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH, &info_vmexit_instruction_length);
            XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_RIP, &guest_rip);
            guest_rip+=info_vmexit_instruction_length;
            XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RIP, guest_rip);

            _XDPRINTF_("%s[%u]: adjusted guest_rip=%016llx\n",
                __FUNCTION__, (u32)cpuindex, guest_rip);

        }
        break;



        //memory fault
		case VMX_VMEXIT_EPT_VIOLATION:{



        }
		break;



        //io traps
		case VMX_VMEXIT_IOIO:{




		}
		break;


        //instruction traps
        case VMX_VMEXIT_CPUID:{
            u64 guest_rip;
            u64 info_vmexit_instruction_length;
            bool clearsyscallretbit=false;
            x86regs64_t r;

            _XDPRINTF_("%s[%u]: VMX_VMEXIT_cpuindex\n",
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
        break;



        //exception traps
        case VMX_VMEXIT_EXCEPTION:{




        }
        break;



        default:
            _XDPRINTF_("%s[%u]: unhandled intercept %x. Halting!\n",
                    __FUNCTION__, (u32)cpuindex, info_vmexit_reason);

            HALT();
    }


	//_XDPRINTF_("%s[%u]: Halting!\n",
    //            __FUNCTION__, (u32)cpuindex);
    //HALT();

    return;
}


