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
#include <xmhfhicslab.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <xhhyperdep.h>


//////
XMHF_SLABNEW(xhhyperdep)

#define HYPERDEP_ACTIVATEDEP			0xC0
#define HYPERDEP_DEACTIVATEDEP			0xC1



//activate DEP for a given page (at gpa)
static void hd_activatedep(u32 cpuindex, u32 guest_slab_index, u64 gpa){
	slab_params_t spl;
	xmhf_hic_uapi_mempgtbl_desc_t *mdesc = (xmhf_hic_uapi_mempgtbl_desc_t *)&spl.in_out_params[2];

	spl.src_slabid = XMHF_HYP_SLAB_XHHYPERDEP;
	spl.cpuid = cpuindex;
	spl.in_out_params[0] = XMHF_HIC_UAPI_MEMPGTBL;

    if(!hd_activated){
        mdesc->guest_slab_index = guest_slab_index;
        mdesc->gpa = gpa;

        if(mdesc->gpa != 0){
            //XMHF_HIC_SLAB_UAPI_MEMPGTBL(XMHF_HIC_UAPI_MEMPGTBL_GETENTRY, &mdesc, &mdesc);
            spl.in_out_params[1] = XMHF_HIC_UAPI_MEMPGTBL_GETENTRY;
            XMHF_SLAB_UAPI(&spl);

            _XDPRINTF_("%s[%u]: original entry for gpa=%016llx is %016llx\n", __FUNCTION__, (u16)cpuindex,
                       gpa, mdesc->entry);

            mdesc->entry &= ~(0x4); //execute-disable

            //XMHF_HIC_SLAB_UAPI_MEMPGTBL(XMHF_HIC_UAPI_MEMPGTBL_SETENTRY, &mdesc, NULL);
            spl.in_out_params[1] = XMHF_HIC_UAPI_MEMPGTBL_SETENTRY;
            XMHF_SLAB_UAPI(&spl);

            _XDPRINTF_("%s[%u]: activated DEP for page at gpa %016llx\n", __FUNCTION__, (u16)cpuindex, gpa);

            hd_activated=true;
        }
    }
}

//deactivate DEP for a given page (at gpa)
static void hd_deactivatedep(u32 cpuindex, u32 guest_slab_index, u64 gpa){
	slab_params_t spl;
	xmhf_hic_uapi_mempgtbl_desc_t *mdesc = (xmhf_hic_uapi_mempgtbl_desc_t *)&spl.in_out_params[2];

    if(hd_activated){
        mdesc->guest_slab_index = guest_slab_index;
        mdesc->gpa = gpa;

        if(mdesc->gpa != 0){
            //XMHF_HIC_SLAB_UAPI_MEMPGTBL(XMHF_HIC_UAPI_MEMPGTBL_GETENTRY, &mdesc, &mdesc);
            spl.in_out_params[1] = XMHF_HIC_UAPI_MEMPGTBL_GETENTRY;
            XMHF_SLAB_UAPI(&spl);

            _XDPRINTF_("%s[%u]: original entry for gpa=%016llx is %016llx\n", __FUNCTION__, (u16)cpuindex, gpa, mdesc->entry);

            mdesc->entry &= ~(0x7);
            mdesc->entry |= 0x7; //execute, read-write

            //XMHF_HIC_SLAB_UAPI_MEMPGTBL(XMHF_HIC_UAPI_MEMPGTBL_SETENTRY, &mdesc, NULL);
            spl.in_out_params[1] = XMHF_HIC_UAPI_MEMPGTBL_SETENTRY;
            XMHF_SLAB_UAPI(&spl);


            _XDPRINTF_("%s[%u]: deactivated DEP for page at gpa %016llx\n", __FUNCTION__, (u16)cpuindex, gpa);

            hd_activated=false;
        }
    }
}








//////
// hypapp callbacks

// initialization
static void _hcb_initialize(u32 cpuindex){
	_XDPRINTF_("%s[%u]: hyperDEP initializing...\n", __FUNCTION__, (u16)cpuindex);
}


// hypercall
static void _hcb_hypercall(u32 cpuindex, u32 guest_slab_index){
    slab_params_t spl;
    x86regs_t *gprs = (x86regs_t *)&spl.in_out_params[2];
	u32 call_id;
	u64 gpa;

    spl.src_slabid = XMHF_HYP_SLAB_XHHYPERDEP;
    spl.cpuid = cpuindex;
    spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;

    //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &gprs);
    spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
    XMHF_SLAB_UAPI(&spl);

    call_id = gprs->eax;
    gpa = ((u64)gprs->edx << 32) | gprs->ebx;

	_XDPRINTF_("%s[%u]: call_id=%x, gpa=%016llx\n", __FUNCTION__, (u16)cpuindex, call_id, gpa);


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
                       __FUNCTION__, (u16)cpuindex, call_id);
			break;
	}

}

//shutdown
static void _hcb_shutdown(u32 cpuindex, u32 guest_slab_index){
	_XDPRINTF_("%s[%u]: guest slab %u shutdown...\n", __FUNCTION__, (u16)cpuindex, guest_slab_index);
}


//memory fault
static void _hcb_memoryfault(u32 cpuindex, u32 guest_slab_index, u64 gpa, u64 gva, u64 errorcode){
	_XDPRINTF_("%s[%u]: memory fault in guest slab %u; gpa=%016llx, gva=%016llx, errorcode=%016llx, data page execution?\n",
            __FUNCTION__, (u16)cpuindex, guest_slab_index, gpa, gva, errorcode);
    HALT();
}












//////
// slab interface

//void slab_interface(slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 src_slabid, u64 cpuindex){
void slab_main(slab_params_t *sp){
    //xc_hypappcb_inputparams_t *hcb_iparams = (xc_hypappcb_inputparams_t *)iparams;
    //xc_hypappcb_outputparams_t *hcb_oparams = (xc_hypappcb_outputparams_t *)oparams;
    xc_hypappcb_params_t *hcbp = (xc_hypappcb_params_t *)&sp->in_out_params[0];
    hcbp->cbresult=XC_HYPAPPCB_CHAIN;


	_XDPRINTF_("%s[%u]: Got control, cbtype=%x: ESP=%08x\n",
                __FUNCTION__, (u16)sp->cpuid, hcbp->cbtype, read_esp());


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

         	spl.src_slabid = XMHF_HYP_SLAB_XHHYPERDEP;
         	spl.cpuid = sp->cpuid;
            spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;
            spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMREAD;

         	//XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_EXIT_QUALIFICATION, &errorcode);
            spl.in_out_params[2] = VMCS_INFO_EXIT_QUALIFICATION;
            XMHF_SLAB_UAPI(&spl);
            errorcode = spl.in_out_params[4];

         	//XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_GUEST_PADDR_FULL, &gpa);
            spl.in_out_params[2] = VMCS_INFO_GUEST_PADDR_FULL;
            XMHF_SLAB_UAPI(&spl);
            gpa = spl.in_out_params[4];

         	//XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_GUEST_LINEAR_ADDRESS, &gva);
            spl.in_out_params[2] = VMCS_INFO_GUEST_LINEAR_ADDRESS;
            XMHF_SLAB_UAPI(&spl);
            gva = spl.in_out_params[4];

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
            _XDPRINTF_("%s[%u]: Unknown cbtype. Halting!\n",
                __FUNCTION__, (u16)sp->cpuid);
            HALT();
        }
    }

}
