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
#define HYPERDEP_INITIALIZE				0xC2



/*
static void hd_activatedep(context_desc_t context_desc, u32 gpa){
	u64 entry;
    slab_retval_t srval;

    srval = XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTGETPROT, XMHF_SLAB_XCAPI_FNXCAPIHPTGETPROT_SIZE, context_desc, gpa);
    _XDPRINTF_("\n%s:%u originalprotection=%08x", __FUNCTION__, context_desc.cpu_desc.cpu_index, srval.retval_u32);
    //_XDPRINTF_("\n%s:%u originalprotection=%08x", __FUNCTION__, context_desc.cpu_desc.cpu_index, XMHF_SLAB_CALL(xc_api_hpt_getprot(context_desc, gpa)) );
	srval = XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTGETENTRY, XMHF_SLAB_XCAPI_FNXCAPIHPTGETENTRY_SIZE, context_desc, (u64)gpa);
    entry = srval.retval_u64;
    XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTSETENTRY, XMHF_SLAB_XCAPI_FNXCAPIHPTSETENTRY_SIZE, context_desc, (u64)gpa, entry);
	XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTSETPROT, XMHF_SLAB_XCAPI_FNXCAPIHPTSETPROT_SIZE, context_desc, (u64)gpa, (u32)(MEMP_PROT_PRESENT | MEMP_PROT_READWRITE | MEMP_PROT_NOEXECUTE));

	//flush hpt caches on CPU
    XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTFLUSHCACHES, XMHF_SLAB_XCAPI_FNXCAPIHPTFLUSHCACHES_SIZE, context_desc);
	//quiesce all CPUs to perform TLB shootdown
    XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPIPLATFORM_INDEX, XMHF_SLAB_XCAPIPLATFORM_FNQUIESCECPUSINPARTITION, XMHF_SLAB_XCAPIPLATFORM_FNQUIESCECPUSINPARTITION_SIZE, context_desc);

	_XDPRINTF_("\nCPU(%02x): %s removed EXECUTE permission for page at gpa %08x", context_desc.cpu_desc.cpu_index, __FUNCTION__, gpa);
}

//de-activate DEP protection
static void hd_deactivatedep(context_desc_t context_desc, u32 gpa){
	XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTSETPROT, XMHF_SLAB_XCAPI_FNXCAPIHPTSETPROT_SIZE, context_desc, (u64)gpa, (u32)(MEMP_PROT_PRESENT | MEMP_PROT_READWRITE | MEMP_PROT_EXECUTE));

	//flush hpt caches on CPU
    XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTFLUSHCACHES, XMHF_SLAB_XCAPI_FNXCAPIHPTFLUSHCACHES_SIZE, context_desc);
	//quiesce all CPUs to perform TLB shootdown
    XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPIPLATFORM_INDEX, XMHF_SLAB_XCAPIPLATFORM_FNQUIESCECPUSINPARTITION, XMHF_SLAB_XCAPIPLATFORM_FNQUIESCECPUSINPARTITION_SIZE, context_desc);


	_XDPRINTF_("\nCPU(%02x): %s added EXECUTE permission for page at gpa %08x", context_desc.cpu_desc.cpu_index, __FUNCTION__, gpa);

}

static void hd_initialize(context_desc_t context_desc){
	_XDPRINTF_("%s: nothing to do\n", __FUNCTION__);
}
*/


// hypapp initialization
static void _hcb_initialize(u64 cpuindex){

	_XDPRINTF_("CPU %s[%u]: hyperDEP initializing...\n", __FUNCTION__, (u32)cpuindex);

}



static void _hcb_hypercall(u64 cpuindex, u64 guest_slab_index, u64 hypercall_id, u64 hypercall_param){
	_XDPRINTF_("CPU %s[%u]: call number=%x\n", __FUNCTION__, (u32)cpuindex, hypercall_id);


/*	u64 status=XC_HYPAPPCB_HANDLED;
	u64 call_id;
	u64 gva, gpa;
    //slab_retval_t srval;

	call_id= hypercall_id;

	gva=hypercall_param;

	_XDPRINTF_("CPU %s[%u]: call number=%x, gva=%x", __FUNCTION__, (u32)cpuindex, call_id, gva);

	switch(call_id){
		case HYPERDEP_INITIALIZE:{
			hd_initialize(context_desc);
		}
		break;

		case HYPERDEP_ACTIVATEDEP:{
			srval = XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTLVL2PAGEWALK, XMHF_SLAB_XCAPI_FNXCAPIHPTLVL2PAGEWALK_SIZE, context_desc, gva);
			gpa = srval.retval_u32;
			if(gpa == 0xFFFFFFFFUL){
				_XDPRINTF_("CPU(%02x): WARNING: unable to get translation for gva=%x, just returning\n", context_desc.cpu_desc.cpu_index, gva);
				return status;
			}
			_XDPRINTF_("CPU(%02x): translated gva=%x to gpa=%x\n", context_desc.cpu_desc.cpu_index, gva, gpa);
			hd_activatedep(context_desc, gpa);
		}
		break;

		case HYPERDEP_DEACTIVATEDEP:{
			srval = XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTLVL2PAGEWALK, XMHF_SLAB_XCAPI_FNXCAPIHPTLVL2PAGEWALK_SIZE, context_desc, gva);
            gpa = srval.retval_u32;
			if(gpa == 0xFFFFFFFFUL){
				_XDPRINTF_("CPU(%02x): WARNING: unable to get translation for gva=%x, just returning\n", context_desc.cpu_desc.cpu_index, gva);
				return status;
			}
			_XDPRINTF_("CPU(%02x): translated gva=%x to gpa=%x\n", context_desc.cpu_desc.cpu_index, gva, gpa);
			hd_deactivatedep(context_desc, gpa);
		}
		break;

		default:
			_XDPRINTF_("CPU(0x%02x): unsupported hypercall (0x%08x)!!\n",
			  context_desc.cpu_desc.cpu_index, call_id);
			status=APP_ERROR;
			break;
	}

	return status;
*/

}

static void _hcb_shutdown(u64 cpuindex, u64 guest_slab_index){
	_XDPRINTF_("CPU %s[%u]: guest slab %u shutdown...\n", __FUNCTION__, (u32)cpuindex, guest_slab_index);
}


static void _hcb_memoryfault(u64 cpuindex, u64 guest_slab_index, u64 gpa, u64 gva, u64 error_code){

	_XDPRINTF_("CPU %s[%u]: memory fault in guest slab %u; data page execution?. Halting!\n",
            __FUNCTION__, (u32)cpuindex, guest_slab_index);

	HALT();
}


/////////////////////////////////////////////////////////////////////
void xhhyperdep_interface(slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 src_slabid, u64 cpuindex){
    xc_hypappcb_inputparams_t *hcb_iparams = (xc_hypappcb_inputparams_t *)iparams;
    xc_hypappcb_outputparams_t *hcb_oparams = (xc_hypappcb_outputparams_t *)oparams;
    hcb_oparams->cbresult=XC_HYPAPPCB_CHAIN;


	_XDPRINTF_("%s[%u]: Got control, cbtype=%x: RSP=%016llx\n",
                __FUNCTION__, (u32)cpuindex, hcb_iparams->cbtype, read_rsp());


    switch(hcb_iparams->cbtype){
        case XC_HYPAPPCB_INITIALIZE:{
            _hcb_initialize(cpuindex);
        }
        break;

        case XC_HYPAPPCB_HYPERCALL:{
            _hcb_hypercall(cpuindex, hcb_iparams->guest_slab_index, 0, 0);
        }
        break;

        case XC_HYPAPPCB_MEMORYFAULT:{
            _hcb_memoryfault(cpuindex, hcb_iparams->guest_slab_index, 0, 0, 0);
        }
        break;

        case XC_HYPAPPCB_SHUTDOWN:{
            _hcb_shutdown(cpuindex, hcb_iparams->guest_slab_index);
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
