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

// ropdet hypapp main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhfgeec.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <uapi_gcpustate.h>
#include <xh_ropdet.h>



#define ROPDET_REGISTER    			0x1E0
#define ROPDET_COLLECTBRANCHES			0x1E1
#define ROPDET_CHECK         			0x1E2

bool valid_ropdet_trace_id = false;
u32 g_ropdet_trace_id = 0;
bool ropdet_collectbranches_on = false;


static void rd_register(u32 cpuindex, u32 guest_slab_index, u32 ropdet_trace_id,
				u32 ropdet_trace_baseaddr){

	if(ropdet_trace_id > ROPDET_MAX_TRACE_IDS){
		_XDPRINTF_("%s.%u: ropdet_trace_id > ROPDET_MAX_TRACE_IDS, \
			ignoring registration call\n", __func__, __LINE__);
		return;
	}

	g_ropdet_trace_id = ropdet_trace_id;
	valid_ropdet_trace_id = true;
}


static void rd_collectbranches(u32 cpuindex, u32 guest_slab_index){
    slab_params_t spl;
    xmhf_uapi_gcpustate_msrrw_params_t *gcpustate_msrrwp =
        (xmhf_uapi_gcpustate_msrrw_params_t *)spl.in_out_params;




	if(valid_ropdet_trace_id){

		spl.src_slabid = XMHFGEEC_SLAB_XH_ROPDET;
		spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
		spl.cpuid = cpuindex;
		spl.dst_uapifn = XMHFGEEC_UAPI_CPUSTATE_GUESTMSRREAD;
		gcpustate_msrrwp->msr = GCPUSTATE_MSR_IA32_DEBUGCTL;
		XMHF_SLAB_CALLNEW(&spl);
		gcpustate_msrrwp->value |= (1UL << 8);
		spl.dst_uapifn = XMHFGEEC_UAPI_CPUSTATE_GUESTMSRWRITE;
		XMHF_SLAB_CALLNEW(&spl);

		ropdet_collectbranches_on = true;
	}


}

void rd_check(u32 cpuindex, u32 guest_slab_index){
	u32 i;
	u32 l_branchbuffer[16];
    slab_params_t spl;
    xmhf_uapi_gcpustate_msrrw_params_t *gcpustate_msrrwp =
        (xmhf_uapi_gcpustate_msrrw_params_t *)spl.in_out_params;


	if(ropdet_collectbranches_on == false)
		return;

	//stop branch collection
	spl.src_slabid = XMHFGEEC_SLAB_XH_ROPDET;
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	spl.cpuid = cpuindex;
	spl.dst_uapifn = XMHFGEEC_UAPI_CPUSTATE_GUESTMSRREAD;
	gcpustate_msrrwp->msr = GCPUSTATE_MSR_IA32_DEBUGCTL;
	XMHF_SLAB_CALLNEW(&spl);
	gcpustate_msrrwp->value &= ~(1UL << 8);
	spl.dst_uapifn = XMHFGEEC_UAPI_CPUSTATE_GUESTMSRWRITE;
	XMHF_SLAB_CALLNEW(&spl);

	ropdet_collectbranches_on = false;

	//consolidate all LBR to MSR values into local buffer
	for(i = 0; i < 16; i++){
		gcpustate_msrrwp->msr = GCPUSTATE_MSR_LASTBRANCH_0_TO_IP + i;
		XMHF_SLAB_CALLNEW(&spl);
		l_branchbuffer[i] = (u32)gcpustate_msrrwp->value;
	}


	if(valid_ropdet_trace_id == false)
		return;

        //compare branch offsets for trace and halt if there is mismatch
        for(i = 0; i < 16; i++){
		if(l_branchbuffer[i] != ropdet_trace_ids[g_ropdet_trace_id][i]){
			_XDPRINTF_("%s.%u: ALERT: Branch trace mismatch. Possible ROP. Halting!\n",
				__func__, __LINE__);
			HALT();
		}
        }

}




//////
// hypapp callbacks


// initialization
static void _hcb_initialize(u32 cpuindex){

	_XDPRINTF_("%s[%u]: xh_ropdet initializing...\n", __func__,
            (u16)cpuindex);

}



// hypercall
static void _hcb_hypercall(u32 cpuindex, u32 guest_slab_index){
    slab_params_t spl;
    xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs =
        (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
    x86regs_t *gprs = (x86regs_t *)&gcpustate_gprs->gprs;
	u32 call_id;
	u32 ropdet_trace_id, ropdet_trace_baseaddr;

    spl.src_slabid = XMHFGEEC_SLAB_XH_ROPDET;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.cpuid = cpuindex;

     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
    XMHF_SLAB_CALLNEW(&spl);

    call_id = gprs->eax;
    ropdet_trace_id  = gprs->ebx;
	ropdet_trace_baseaddr = gprs->edx;

    _XDPRINTF_("%s[%u]: call_id=%x\n", __func__, (u16)cpuindex, call_id);

	switch(call_id){

		case ROPDET_REGISTER:{
			rd_register(cpuindex, guest_slab_index, ropdet_trace_id,
				ropdet_trace_baseaddr);
		}
		break;

		case ROPDET_COLLECTBRANCHES:{
			rd_collectbranches(cpuindex, guest_slab_index);
		}
		break;


		case ROPDET_CHECK:{
			rd_check(cpuindex, guest_slab_index);
		}
		break;


		default:
		    _XDPRINTF_("%s[%u]: unsupported hypercall %x. Ignoring\n",
			       __func__, (u16)cpuindex, call_id);
				break;
	}



}


// shutdown
static void _hcb_shutdown(u32 cpuindex, u32 guest_slab_index){
	_XDPRINTF_("%s[%u]: guest slab %u shutdown...\n",
            __func__, (u16)cpuindex, guest_slab_index);
}




// instruction trap
static u32 _hcb_trap_instruction(u32 cpuindex, u32 guest_slab_index, u32 insntype){
    slab_params_t spl;
    xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs =
        (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
    u32 status=XC_HYPAPPCB_CHAIN;
    u32 guest_rip, msrvalue;
    u32 info_vmexit_instruction_length;
    x86regs_t *r = (x86regs_t *)&gcpustate_gprs->gprs;

    if(ropdet_collectbranches_on == false)
        return status;

    spl.src_slabid = XMHFGEEC_SLAB_XH_ROPDET;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.cpuid = cpuindex;

    if (insntype == XC_HYPAPPCB_TRAP_INSTRUCTION_WRMSR){

        spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
        XMHF_SLAB_CALLNEW(&spl);
        msrvalue = r->ecx;

        switch(msrvalue){

		case MSR_LBR_SELECT:
		case MSR_LASTBRANCH_TOS:
		case MSR_IA32_DEBUGCTL:
		case MSR_LASTBRANCH_0_FROM_IP:
		case MSR_LASTBRANCH_1_FROM_IP:
		case MSR_LASTBRANCH_2_FROM_IP:
		case MSR_LASTBRANCH_3_FROM_IP:
		case MSR_LASTBRANCH_4_FROM_IP:
		case MSR_LASTBRANCH_5_FROM_IP:
		case MSR_LASTBRANCH_6_FROM_IP:
		case MSR_LASTBRANCH_7_FROM_IP:
		case MSR_LASTBRANCH_8_FROM_IP:
		case MSR_LASTBRANCH_9_FROM_IP:
		case MSR_LASTBRANCH_10_FROM_IP:
		case MSR_LASTBRANCH_11_FROM_IP:
		case MSR_LASTBRANCH_12_FROM_IP:
		case MSR_LASTBRANCH_13_FROM_IP:
		case MSR_LASTBRANCH_14_FROM_IP:
		case MSR_LASTBRANCH_15_FROM_IP:
		case MSR_LASTBRANCH_0_TO_IP:
		case MSR_LASTBRANCH_1_TO_IP:
		case MSR_LASTBRANCH_2_TO_IP:
		case MSR_LASTBRANCH_3_TO_IP:
		case MSR_LASTBRANCH_4_TO_IP:
		case MSR_LASTBRANCH_5_TO_IP:
		case MSR_LASTBRANCH_6_TO_IP:
		case MSR_LASTBRANCH_7_TO_IP:
		case MSR_LASTBRANCH_8_TO_IP:
		case MSR_LASTBRANCH_9_TO_IP:
		case MSR_LASTBRANCH_10_TO_IP:
		case MSR_LASTBRANCH_11_TO_IP:
		case MSR_LASTBRANCH_12_TO_IP:
		case MSR_LASTBRANCH_13_TO_IP:
		case MSR_LASTBRANCH_14_TO_IP:
		case MSR_LASTBRANCH_15_TO_IP:
		{

              	_XDPRINTF_("%s[%u]: ALERT: writes to LBR/debug MSRs. Halting\n",
				__func__, (u16)cpuindex);
		HALT();
		}
            break;

            default:
                break;
        }
    }


    return status;
}





///////
// slab interface

void slab_main(slab_params_t *sp){
    xc_hypappcb_params_t *hcbp = (xc_hypappcb_params_t *)&sp->in_out_params[0];
    hcbp->cbresult=XC_HYPAPPCB_CHAIN;


	_XDPRINTF_("XHROPDET[%u]: Got control, cbtype=%x: ESP=%08x\n",
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

        case XC_HYPAPPCB_TRAP_INSTRUCTION:{
            hcbp->cbresult = _hcb_trap_instruction(sp->cpuid, hcbp->guest_slab_index, hcbp->cbqual);
        }
        break;

        //case XC_HYPAPPCB_TRAP_EXCEPTION:{
        //    _hcb_trap_exception(sp->cpuid, hcbp->guest_slab_index);
       // }
       // break;


        default:{
            _XDPRINTF_("%s[%u]: Unknown cbtype. Ignoring!\n",
                __func__, (u16)sp->cpuid);
        }
    }

}

