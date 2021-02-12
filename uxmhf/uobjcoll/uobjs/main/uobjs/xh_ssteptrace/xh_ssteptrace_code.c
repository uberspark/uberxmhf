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

// hyperdep hypapp main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/uapi_gcpustate.h>
//#include <uapi_slabmemacc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xh_ssteptrace.h>


//////
//XMHF_SLABNEW(xhssteptrace)



static uint8_t _st_tracebuffer[256];

// trace (single-step) on
static void st_on(uint32_t cpuindex, uint32_t guest_slab_index){
    uint32_t guest_rflags;
    uint32_t exception_bitmap;
    slab_params_t spl;
    xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp =
        (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;

    spl.src_slabid = XMHFGEEC_SLAB_XH_SSTEPTRACE;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.cpuid = cpuindex;
    //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;

if(!ssteptrace_on){
     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
    gcpustate_vmrwp->encoding = VMCS_GUEST_RFLAGS;
    ugcpust_slab_main(&spl);
    guest_rflags = gcpustate_vmrwp->value;

    gcpustate_vmrwp->encoding = VMCS_CONTROL_EXCEPTION_BITMAP;
    ugcpust_slab_main(&spl);
    exception_bitmap = gcpustate_vmrwp->value;

    guest_rflags |= EFLAGS_TF;
    exception_bitmap |= (1 << 1);

     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
    gcpustate_vmrwp->encoding = VMCS_CONTROL_EXCEPTION_BITMAP;
    gcpustate_vmrwp->value = exception_bitmap;
    ugcpust_slab_main(&spl);

    gcpustate_vmrwp->encoding = VMCS_GUEST_RFLAGS;
    gcpustate_vmrwp->value = guest_rflags;
    ugcpust_slab_main(&spl);

    ssteptrace_on=true;
}
}

// trace (single-step) off
static void st_off(uint32_t cpuindex, uint32_t guest_slab_index){
    uint32_t guest_rflags;
    uint32_t exception_bitmap;
    slab_params_t spl;
    xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp =
        (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;

    spl.src_slabid = XMHFGEEC_SLAB_XH_SSTEPTRACE;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.cpuid = cpuindex;
    //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;


if(ssteptrace_on){
     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
    gcpustate_vmrwp->encoding = VMCS_GUEST_RFLAGS;
    ugcpust_slab_main(&spl);
    guest_rflags = gcpustate_vmrwp->value;

    gcpustate_vmrwp->encoding = VMCS_CONTROL_EXCEPTION_BITMAP;
    ugcpust_slab_main(&spl);
    exception_bitmap = gcpustate_vmrwp->value;


    guest_rflags &= ~(EFLAGS_TF);
    exception_bitmap &= ~(1 << 1);

     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
    gcpustate_vmrwp->encoding = VMCS_CONTROL_EXCEPTION_BITMAP;
    gcpustate_vmrwp->value = exception_bitmap;
    ugcpust_slab_main(&spl);

    gcpustate_vmrwp->encoding = VMCS_GUEST_RFLAGS;
    gcpustate_vmrwp->value = guest_rflags;
    ugcpust_slab_main(&spl);

    ssteptrace_on=false;
}
}




static uint8_t _st_sigdatabase[][SHA_DIGEST_LENGTH] = {
  {0xd1, 0x4e, 0x30, 0x25,  0x8e,  0x16, 0x85, 0x9b, 0x21, 0x81, 0x74, 0x78, 0xbb, 0x1b, 0x5d, 0x99, 0xb5, 0x48, 0x60, 0xca},
  {0xa1, 0x4e, 0x30, 0x25,  0x8e,  0x16, 0x85, 0x9b, 0x21, 0x71, 0x74, 0x78, 0xbb, 0x1b, 0x5d, 0x99, 0xb5, 0x48, 0x60, 0xca},
  {0xf1, 0x4e, 0x30, 0x25,  0x8e,  0x16, 0x85, 0x9b, 0x21, 0x81, 0x54, 0x78, 0xbb, 0x1b, 0x5d, 0x99, 0xb5, 0x48, 0x60, 0xca},
  {0xe1, 0x4e, 0x30, 0x25,  0x9e,  0x16, 0x85, 0x9b, 0x21, 0x81, 0x74, 0x78, 0x6b, 0x1b, 0x5d, 0x99, 0xb5, 0x48, 0x60, 0xca},
};

#define NUMENTRIES_ST_SIGDATABASE  (sizeof(_st_sigdatabase)/sizeof(_st_sigdatabase[0]))


// scan for a trace match with incoming trace in buffer
static bool st_scanforsignature(uint8_t *buffer, uint32_t buffer_size){
    uint8_t digest[SHA_DIGEST_LENGTH];
    uint64_t i;

    //compute SHA-1 of the buffer
    unsigned long outlen = 20; // not sure what outlen is for, placeholder for now...
    uberspark_uobjrtl_crypto__hashes_sha1__sha1_memory(buffer, buffer_size, digest, &outlen);

    //compare computed SHA-1 to the signature database
    for(i=0; i < NUMENTRIES_ST_SIGDATABASE; i++){
        if(!uberspark_uobjrtl_crt__memcmp(&digest, &_st_sigdatabase[i], SHA_DIGEST_LENGTH)){
            return true;
        }
    }

    //no match
    return false;
}



//////
// hypapp callbacks


// initialization
static void _hcb_initialize(uint32_t cpuindex){

	_XDPRINTF_("%s[%u]: xhssteptrace initializing...\n", __func__,
            (uint16_t)cpuindex);

}


// hypercall
static void _hcb_hypercall(uint32_t cpuindex, uint32_t guest_slab_index){
    slab_params_t spl;
    xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs =
        (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
    x86regs_t *gprs = (x86regs_t *)&gcpustate_gprs->gprs;
	uint32_t call_id;
	//uint64_t gpa;

    spl.src_slabid = XMHFGEEC_SLAB_XH_SSTEPTRACE;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.cpuid = cpuindex;
    //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;

     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
    ugcpust_slab_main(&spl);

    call_id = gprs->eax;
    //gpa = ((uint64_t)gprs->edx << 32) | gprs->ebx;

	//_XDPRINTF_("%s[%u]: call_id=%x, gpa=%016llx\n", __func__, (uint16_t)cpuindex, call_id, gpa);

	switch(call_id){

		case SSTEPTRACE_REGISTER:{
			ssteptrace_codepaddr = gprs->edx;
			_XDPRINTF_("%s[%u]: call_id=%x(REGISTER) at paddr=0x%08x\n", __func__, (uint16_t)cpuindex, call_id, ssteptrace_codepaddr);
		}
		break;

		case SSTEPTRACE_ON:{
		    _XDPRINTF_("%s[%u]: call_id=%x(TRACE_ON)\n", __func__, (uint16_t)cpuindex, call_id);
			st_on(cpuindex, guest_slab_index);
		}
		break;

		case SSTEPTRACE_OFF:{
		    _XDPRINTF_("%s[%u]: call_id=%x(TRACE_OFF)\n", __func__, (uint16_t)cpuindex, call_id);
			st_off(cpuindex, guest_slab_index);
		}
		break;

		default:
            //_XDPRINTF_("%s[%u]: unsupported hypercall %x. Ignoring\n", __func__, (uint16_t)cpuindex, call_id);
			break;
	}



}


// trap exception
static void _hcb_trap_exception(uint32_t cpuindex, uint32_t guest_slab_index){
    uint32_t info_vmexit_interruption_information;
    uint32_t guest_rip, guest_rip_paddr;
    slab_params_t spl;
    xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp =
        (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;

    //xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)&spl.in_out_params[2];
    //xmhf_uapi_slabmemacc_params_t *smemaccp = (xmhf_uapi_slabmemacc_params_t *)spl.in_out_params;

    spl.src_slabid = XMHFGEEC_SLAB_XH_SSTEPTRACE;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.cpuid = cpuindex;

    if(ssteptrace_on){
        //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;
         spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
        gcpustate_vmrwp->encoding = VMCS_INFO_VMEXIT_INTERRUPT_INFORMATION;
        ugcpust_slab_main(&spl);
        info_vmexit_interruption_information = gcpustate_vmrwp->value;

        _XDPRINTF_("%s[%u]: guest slab %u exception %u...\n",
                   __func__, (uint16_t)cpuindex, guest_slab_index,
                   (uint8_t)info_vmexit_interruption_information);

        if((uint8_t)info_vmexit_interruption_information != 0x1)
            return;

        gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
        ugcpust_slab_main(&spl);
        guest_rip = gcpustate_vmrwp->value;

        //copy 256 bytes from the current guest RIP for trace inference
        //spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMACC;
        //smemaccp->dst_slabid = guest_slab_index;
        //smemaccp->addr_to = &_st_tracebuffer;
        //smemaccp->addr_from = guest_rip;
        //smemaccp->numbytes = sizeof(_st_tracebuffer);
        ////spl.in_out_params[0] = XMHF_HIC_UAPI_PHYSMEM;
        // spl.dst_uapifn = XMHF_HIC_UAPI_PHYSMEM_PEEK;
        //XMHF_SLAB_CALLNEW(&spl);

        guest_rip_paddr = ssteptrace_codepaddr | (guest_rip & 0x00000FFFUL);
        _XDPRINTF_("%s[%u]: guest slab RIP=%x, RIP paddr=0x%08x\n",
                   __func__, (uint16_t)cpuindex, guest_rip, guest_rip_paddr);

        CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmemaccess_copy, &_st_tracebuffer, guest_rip_paddr, sizeof(_st_tracebuffer));

        //try to see if we found a match in our trace database
        st_scanforsignature(&_st_tracebuffer, sizeof(_st_tracebuffer));
        _XDPRINTF_("%s[%u]: scan complete\n",
                   __func__, (uint16_t)cpuindex);

    }

}


// shutdown
static void _hcb_shutdown(uint32_t cpuindex, uint32_t guest_slab_index){
	_XDPRINTF_("%s[%u]: guest slab %u shutdown...\n",
            __func__, (uint16_t)cpuindex, guest_slab_index);
}











///////
// slab interface

// void slab_interface(slab_input_params_t *iparams, uint64_t iparams_size, slab_output_params_t *oparams, uint64_t oparams_size, uint64_t src_slabid, uint64_t cpuindex){
void xh_ssteptrace_slab_main(slab_params_t *sp){
    //xc_hypappcb_inputparams_t *hcb_iparams = (xc_hypappcb_inputparams_t *)iparams;
    //xc_hypappcb_outputparams_t *hcb_oparams = (xc_hypappcb_outputparams_t *)oparams;
    xc_hypappcb_params_t *hcbp = (xc_hypappcb_params_t *)&sp->in_out_params[0];
    hcbp->cbresult=XC_HYPAPPCB_CHAIN;


	//_XDPRINTF_("XHSSTEPTRACE[%u]: Got control, cbtype=%x: ESP=%08x\n",
    //            (uint16_t)sp->cpuid, hcbp->cbtype, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_esp,CASM_NOPARAM));


    switch(hcbp->cbtype){
        case XC_HYPAPPCB_INITIALIZE:{
            _hcb_initialize(sp->cpuid);
        }
        break;

        case XC_HYPAPPCB_HYPERCALL:{
            _hcb_hypercall(sp->cpuid, hcbp->guest_slab_index);
        }
        break;

        //case XC_HYPAPPCB_MEMORYFAULT:{
        //
        //
        //}
        //break;

        case XC_HYPAPPCB_SHUTDOWN:{
            _hcb_shutdown(sp->cpuid, hcbp->guest_slab_index);
        }
        break;

        //case XC_HYPAPPCB_TRAP_IO:{
        //
        //
        //}
        //break;

        //case XC_HYPAPPCB_TRAP_INSTRUCTION:{
        //
        //
        //}
        //break;

        case XC_HYPAPPCB_TRAP_EXCEPTION:{
            _hcb_trap_exception(sp->cpuid, hcbp->guest_slab_index);
        }
        break;


        default:{
            _XDPRINTF_("%s[%u]: Unknown cbtype. Ignoring!\n",
                __func__, (uint16_t)sp->cpuid);
        }
    }

}
