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

#include <xmhf.h>
#include <xmhfgeec.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <uapi_gcpustate.h>
#include <uapi_slabmempgtbl.h>

#include <xh_hyperdep.h>


//////
//XMHF_SLABNEW(xhhyperdep)

#define HYPERDEP_ACTIVATEDEP			0xC0
#define HYPERDEP_DEACTIVATEDEP			0xC1



//activate DEP for a given page (at gpa)
static void hd_activatedep(u32 cpuindex, u32 guest_slab_index, u64 gpa){
	slab_params_t spl;
	//xmhf_hic_uapi_mempgtbl_desc_t *mdesc = (xmhf_hic_uapi_mempgtbl_desc_t *)&spl.in_out_params[2];
        //xmhf_uapi_slabmempgtbl_entry_params_t *smpgtblep =
        //    (xmhf_uapi_slabmempgtbl_entry_params_t *)spl.in_out_params;
    xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *getentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *)spl.in_out_params;
    xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;


	spl.src_slabid = XMHFGEEC_SLAB_XH_HYPERDEP;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
	spl.cpuid = cpuindex;
	//spl.in_out_params[0] = XMHF_HIC_UAPI_MEMPGTBL;

    if(!hd_activated){

        if(gpa != 0){
            spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR;
            getentryforpaddrp->dst_slabid = guest_slab_index;
            getentryforpaddrp->gpa = gpa;
            XMHF_SLAB_CALLNEW(&spl);

            _XDPRINTF_("%s[%u]: original entry for gpa=%016llx is %016llx\n", __func__, (u16)cpuindex,
                       gpa, getentryforpaddrp->result_entry);

             spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
            setentryforpaddrp->dst_slabid = guest_slab_index;
            setentryforpaddrp->gpa = gpa;
            setentryforpaddrp->entry = getentryforpaddrp->result_entry & ~(0x4); //execute-disable
            XMHF_SLAB_CALLNEW(&spl);

            _XDPRINTF_("%s[%u]: activated DEP for page at gpa %016llx\n", __func__, (u16)cpuindex, gpa);

            hd_activated=true;
        }
    }
}

//deactivate DEP for a given page (at gpa)
static void hd_deactivatedep(u32 cpuindex, u32 guest_slab_index, u64 gpa){
	slab_params_t spl;
	//xmhf_hic_uapi_mempgtbl_desc_t *mdesc = (xmhf_hic_uapi_mempgtbl_desc_t *)&spl.in_out_params[2];
    //    xmhf_uapi_slabmempgtbl_entry_params_t *smpgtblep =
    //        (xmhf_uapi_slabmempgtbl_entry_params_t *)spl.in_out_params;
    xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *getentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *)spl.in_out_params;
    xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;


	spl.src_slabid = XMHFGEEC_SLAB_XH_HYPERDEP;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
	spl.cpuid = cpuindex;
	//spl.in_out_params[0] = XMHF_HIC_UAPI_MEMPGTBL;

    if(hd_activated){

        if(gpa != 0){
             spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR;
            getentryforpaddrp->dst_slabid = guest_slab_index;
            getentryforpaddrp->gpa = gpa;
            XMHF_SLAB_CALLNEW(&spl);

            _XDPRINTF_("%s[%u]: original entry for gpa=%016llx is %016llx\n", __func__,
                       (u16)cpuindex, gpa, getentryforpaddrp->result_entry);

             spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
            setentryforpaddrp->dst_slabid = guest_slab_index;
            setentryforpaddrp->gpa = gpa;
            setentryforpaddrp->entry = getentryforpaddrp->result_entry & ~(0x7);
            setentryforpaddrp->entry |= 0x7; //execute, read-write
            XMHF_SLAB_CALLNEW(&spl);

            _XDPRINTF_("%s[%u]: deactivated DEP for page at gpa %016llx\n", __func__, (u16)cpuindex, gpa);

            hd_activated=false;
        }
    }
}








//////
// hypapp callbacks

// initialization
static void _hcb_initialize(u32 cpuindex){
	_XDPRINTF_("%s[%u]: hyperDEP initializing...\n", __func__, (u16)cpuindex);
}


// hypercall
static void _hcb_hypercall(u32 cpuindex, u32 guest_slab_index){
    slab_params_t spl;
    xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs =
        (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
    x86regs_t *gprs = (x86regs_t *)&gcpustate_gprs->gprs;
	u32 call_id;
	u64 gpa;

    spl.src_slabid = XMHFGEEC_SLAB_XH_HYPERDEP;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.cpuid = cpuindex;
    //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;

     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
    XMHF_SLAB_CALLNEW(&spl);

    call_id = gprs->eax;
    gpa = ((u64)gprs->ebx << 32) | gprs->edx;

	_XDPRINTF_("%s[%u]: call_id=%x, gpa=%016llx\n", __func__, (u16)cpuindex, call_id, gpa);


	switch(call_id){

		case HYPERDEP_ACTIVATEDEP:{
			hd_activatedep(cpuindex, guest_slab_index, gpa);
		}
		break;

		case HYPERDEP_DEACTIVATEDEP:{
			hd_deactivatedep(cpuindex, guest_slab_index, gpa);
		}
		break;

		default:
            _XDPRINTF_("%s[%u]: unsupported hypercall %x. Ignoring\n",
                       __func__, (u16)cpuindex, call_id);
			break;
	}

}

//shutdown
static void _hcb_shutdown(u32 cpuindex, u32 guest_slab_index){
	_XDPRINTF_("%s[%u]: guest slab %u shutdown...\n", __func__, (u16)cpuindex, guest_slab_index);
}


//memory fault
static void _hcb_memoryfault(u32 cpuindex, u32 guest_slab_index, u64 gpa, u64 gva, u64 errorcode){
	_XDPRINTF_("%s[%u]: memory fault in guest slab %u; gpa=%016llx, gva=%016llx, errorcode=%016llx, data page execution?\n",
            __func__, (u16)cpuindex, guest_slab_index, gpa, gva, errorcode);
    //HALT();
}












//////
// slab interface

//void slab_interface(slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 src_slabid, u64 cpuindex){
void slab_main(slab_params_t *sp){
    //xc_hypappcb_inputparams_t *hcb_iparams = (xc_hypappcb_inputparams_t *)iparams;
    //xc_hypappcb_outputparams_t *hcb_oparams = (xc_hypappcb_outputparams_t *)oparams;
    xc_hypappcb_params_t *hcbp = (xc_hypappcb_params_t *)&sp->in_out_params[0];
    hcbp->cbresult=XC_HYPAPPCB_CHAIN;


	_XDPRINTF_("XHHYPERDEP[%u]: Got control, cbtype=%x: ESP=%08x\n",
                (u16)sp->cpuid, hcbp->cbtype, CASM_FUNCCALL(read_esp,CASM_NOPARAM));


    switch(hcbp->cbtype){
        case XC_HYPAPPCB_INITIALIZE:{
            _hcb_initialize(sp->cpuid);
        }
        break;

        case XC_HYPAPPCB_HYPERCALL:{
            _hcb_hypercall(sp->cpuid, hcbp->guest_slab_index);

        }
        break;

        case XC_HYPAPPCB_MEMORYFAULT:{
         	u64 errorcode;
         	u64 gpa;
         	u64 gva;
         	slab_params_t spl;
       	    xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp =
                (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;


         	spl.src_slabid = XMHFGEEC_SLAB_XH_HYPERDEP;
         	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
         	spl.cpuid = sp->cpuid;
            //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;
             spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;

            gcpustate_vmrwp->encoding = VMCS_INFO_EXIT_QUALIFICATION;
            XMHF_SLAB_CALLNEW(&spl);
            errorcode = gcpustate_vmrwp->value;

            gcpustate_vmrwp->encoding = VMCS_INFO_GUEST_PADDR_FULL;
            XMHF_SLAB_CALLNEW(&spl);
            gpa = gcpustate_vmrwp->value;

            gcpustate_vmrwp->encoding = VMCS_INFO_GUEST_LINEAR_ADDRESS;
            XMHF_SLAB_CALLNEW(&spl);
            gva = gcpustate_vmrwp->value;

            _hcb_memoryfault(sp->cpuid, hcbp->guest_slab_index, gpa, gva, errorcode);
        }
        break;

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

        //case XC_HYPAPPCB_TRAP_EXCEPTION:{
        //
        //
        //}
        //break;


        default:{
            _XDPRINTF_("%s[%u]: Unknown cbtype. Ignoring!\n",
                __func__, (u16)sp->cpuid);
        }
    }

}
