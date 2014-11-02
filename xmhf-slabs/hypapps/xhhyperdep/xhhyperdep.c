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
#include <xmhf-debug.h>
#include <xmhf-core.h>

#include <xhhyperdep.h>


//////
XMHF_SLAB(xhhyperdep)

#define HYPERDEP_ACTIVATEDEP			0xC0
#define HYPERDEP_DEACTIVATEDEP			0xC1


//activate DEP for a given page (at gpa)
static void hd_activatedep(u64 cpuindex, u64 guest_slab_index, u64 gpa){
	xmhf_hic_uapi_mempgtbl_desc_t mdesc;

	mdesc.guest_slab_index = guest_slab_index;
	mdesc.gpa = gpa;

    XMHF_HIC_SLAB_UAPI_MEMPGTBL(XMHF_HIC_UAPI_MEMPGTBL_GETENTRY, &mdesc, &mdesc);
    _XDPRINTF_("%s[%u]: original entry for gpa=%x is %x\n", __FUNCTION__, (u32)cpuindex, gpa, mdesc.entry);

    mdesc.entry &= ~(0x7);
    mdesc.entry |= 0x3; //execute-disable, read-write

    XMHF_HIC_SLAB_UAPI_MEMPGTBL(XMHF_HIC_UAPI_MEMPGTBL_SETENTRY, &mdesc, NULL);

    _XDPRINTF_("%s[%u]: activated DEP for page at gpa %x\n", __FUNCTION__, (u32)cpuindex, gpa);
}

//deactivate DEP for a given page (at gpa)
static void hd_deactivatedep(u64 cpuindex, u64 guest_slab_index, u64 gpa){
	xmhf_hic_uapi_mempgtbl_desc_t mdesc;

	mdesc.guest_slab_index = guest_slab_index;
	mdesc.gpa = gpa;

    XMHF_HIC_SLAB_UAPI_MEMPGTBL(XMHF_HIC_UAPI_MEMPGTBL_GETENTRY, &mdesc, &mdesc);
    _XDPRINTF_("%s[%u]: original entry for gpa=%x is %x\n", __FUNCTION__, (u32)cpuindex, gpa, mdesc.entry);

    mdesc.entry &= ~(0x7);
    mdesc.entry |= 0x7; //execute, read-write

    XMHF_HIC_SLAB_UAPI_MEMPGTBL(XMHF_HIC_UAPI_MEMPGTBL_SETENTRY, &mdesc, NULL);

    _XDPRINTF_("%s[%u]: deactivated DEP for page at gpa %x\n", __FUNCTION__, (u32)cpuindex, gpa);
}








//////
// hypapp callbacks

// initialization
static void _hcb_initialize(u64 cpuindex){
	_XDPRINTF_("%s[%u]: hyperDEP initializing...\n", __FUNCTION__, (u32)cpuindex);
}


// hypercall
static void _hcb_hypercall(u64 cpuindex, u64 guest_slab_index){
    x86regs64_t gprs;
	u64 call_id;
	u64 gpa;

    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &gprs);

    call_id = gprs.rax;
    gpa = gprs.rbx;

	_XDPRINTF_("%s[%u]: call_id=%x, gpa=%x\n", __FUNCTION__, (u32)cpuindex, call_id, gpa);


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
                       __FUNCTION__, (u32)cpuindex, call_id);
			break;
	}

}

//shutdown
static void _hcb_shutdown(u64 cpuindex, u64 guest_slab_index){
	_XDPRINTF_("%s[%u]: guest slab %u shutdown...\n", __FUNCTION__, (u32)cpuindex, guest_slab_index);
}


//memory fault
static void _hcb_memoryfault(u64 cpuindex, u64 guest_slab_index, u64 gpa, u64 gva, u64 errorcode){
	_XDPRINTF_("%s[%u]: memory fault in guest slab %u; gpa=%x, gva=%x, errorcode=%x, data page execution?\n", __FUNCTION__, (u32)cpuindex, guest_slab_index, gpa, gva, errorcode);
}












//////
// slab interface

void xhhyperdep_interface(slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 src_slabid, u64 cpuindex){
    xc_hypappcb_inputparams_t *hcb_iparams = (xc_hypappcb_inputparams_t *)iparams;
    xc_hypappcb_outputparams_t *hcb_oparams = (xc_hypappcb_outputparams_t *)oparams;
    hcb_oparams->cbresult=XC_HYPAPPCB_CHAIN;


	_XDPRINTF_("%s[%u]: Got control, cbtype=%x: RSP=%016llx\n",
                __FUNCTION__, (u32)cpuindex, hcb_iparams->cbtype, read_rsp());


    switch(hcb_iparams->cbtype){
        case XC_HYPAPPCB_INITIALIZE:{
            //_hcb_initialize(cpuindex);
        }
        break;

        case XC_HYPAPPCB_HYPERCALL:{
            //_hcb_hypercall(cpuindex, hcb_iparams->guest_slab_index);

        }
        break;

        case XC_HYPAPPCB_MEMORYFAULT:{
         	//u64 errorcode;
         	//u64 gpa;
         	//u64 gva;

         	//XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_EXIT_QUALIFICATION, &errorcode);
         	//XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_GUEST_PADDR_FULL, &gpa);
         	//XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_GUEST_LINEAR_ADDRESS, &gva);

            //_hcb_memoryfault(cpuindex, hcb_iparams->guest_slab_index, gpa, gva, errorcode);
        }
        break;

        case XC_HYPAPPCB_SHUTDOWN:{
            //_hcb_shutdown(cpuindex, hcb_iparams->guest_slab_index);
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
                __FUNCTION__, (u32)cpuindex);
            HALT();
        }
    }

}
