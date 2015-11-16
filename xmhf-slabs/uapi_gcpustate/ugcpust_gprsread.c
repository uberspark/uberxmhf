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
 * guest CPU state uAPI
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <xc.h>
#include <uapi_gcpustate.h>

static x86regs_t guestgprs[MAX_PLATFORM_CPUS];

static u64 guestmsrs[GCPUSTATE_MSR_MAXCOUNT];

/*
static bool _uapicheck_encoding_used_by_hic(u64 encoding){
    if( (u32)encoding & 0xFFFF0000 )
        return false;

    if( (u16)encoding == 0x0000 || (u16)encoding == 0x4000 || (u16)encoding == 0x4002 || (u16)encoding == 0x401E )
        return true;

    if( ((u16)encoding & 0xFF00) == 0x20 ||
       ((u16)encoding & 0xFF00) == 0x6C ||
       ((u16)encoding & 0xFF00) == 0x4C ||
       ((u16)encoding & 0xFF00) == 0x2C ||
       ((u16)encoding & 0xFF00) == 0x0C)
        return true;

    return false;
}*/


/////
void slab_main(slab_params_t *sp){
    //xmhf_uapi_params_hdr_t *uapiphdr = (xmhf_uapi_params_hdr_t *)sp->in_out_params;

#if 0
    _XDPRINTF_("UAPI_GCPUSTATE: esp=%x, src=%u, dst=%u\n",
               CASM_FUNCCALL(read_esp, CASM_NOPARAM), sp->src_slabid, sp->dst_slabid);
    HALT();
#endif // 0

    switch(sp->dst_uapifn){
        case XMHF_HIC_UAPI_CPUSTATE_VMREAD:{
            xmhf_uapi_gcpustate_vmrw_params_t *vmrwp =
                (xmhf_uapi_gcpustate_gprs_params_t *)sp->in_out_params;

            vmrwp->value = CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,vmrwp->encoding);
        }
        break;

        case XMHF_HIC_UAPI_CPUSTATE_VMWRITE:{
            xmhf_uapi_gcpustate_vmrw_params_t *vmrwp =
                (xmhf_uapi_gcpustate_gprs_params_t *)sp->in_out_params;

            CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite, vmrwp->encoding, vmrwp->value);
        }
        break;


        case XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD:{
            xmhf_uapi_gcpustate_gprs_params_t *gprs =
                (xmhf_uapi_gcpustate_gprs_params_t *)sp->in_out_params;

            memcpy(&gprs->gprs, &guestgprs[(u16)sp->cpuid], sizeof(x86regs_t));
        }
        break;

        case XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE:{
            xmhf_uapi_gcpustate_gprs_params_t *gprs =
                (xmhf_uapi_gcpustate_gprs_params_t *)sp->in_out_params;

            memcpy(&guestgprs[(u16)sp->cpuid], &gprs->gprs, sizeof(x86regs_t));

        }
        break;


        case XMHFGEEC_UAPI_CPUSTATE_GUESTMSRREAD:{
            xmhf_uapi_gcpustate_msrrw_params_t *msrrwp =
                (xmhf_uapi_gcpustate_msrrw_params_t *)sp->in_out_params;

		if(msrrwp->msr < GCPUSTATE_MSR_TOTAL){
			msrrwp->value = guestmsrs[msrrwp->msr];

			 //TODO: make core specific guestmsrs load
			 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, guestmsrs);
			 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_HIGH, 0);
			 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, GCPUSTATE_MSR_TOTAL);
			 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, guestmsrs);
			 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_HIGH, 0);
			 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, GCPUSTATE_MSR_TOTAL);
		}

        }
        break;

        case XMHFGEEC_UAPI_CPUSTATE_GUESTMSRWRITE:{
            xmhf_uapi_gcpustate_msrrw_params_t *msrrwp =
                (xmhf_uapi_gcpustate_msrrw_params_t *)sp->in_out_params;

		if(msrrwp->msr < GCPUSTATE_MSR_TOTAL){
			guestmsrs[msrrwp->msr] = msrrwp->value;

			 //TODO: make core specific guestmsrs load
			 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, guestmsrs);
			 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_HIGH, 0);
			 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, GCPUSTATE_MSR_TOTAL);
			 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, guestmsrs);
			 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_HIGH, 0);
			 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, GCPUSTATE_MSR_TOTAL);

		}

        }
        break;


        default:
            _XDPRINTF_("UAPI_GCPUSTATE[%u]: Unknown uAPI function %x. Halting!\n",
                    (u16)sp->cpuid, sp->dst_uapifn);
            HALT();
            return;
    }


}
