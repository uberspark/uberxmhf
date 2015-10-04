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







/*
static u8 _st_tracebuffer[256];

// trace (single-step) on
static void st_on(u32 cpuindex, u32 guest_slab_index){
    u32 guest_rflags;
    u32 exception_bitmap;
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
    XMHF_SLAB_CALLNEW(&spl);
    guest_rflags = gcpustate_vmrwp->value;

    gcpustate_vmrwp->encoding = VMCS_CONTROL_EXCEPTION_BITMAP;
    XMHF_SLAB_CALLNEW(&spl);
    exception_bitmap = gcpustate_vmrwp->value;

    guest_rflags |= EFLAGS_TF;
    exception_bitmap |= (1 << 1);

     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
    gcpustate_vmrwp->encoding = VMCS_CONTROL_EXCEPTION_BITMAP;
    gcpustate_vmrwp->value = exception_bitmap;
    XMHF_SLAB_CALLNEW(&spl);

    gcpustate_vmrwp->encoding = VMCS_GUEST_RFLAGS;
    gcpustate_vmrwp->value = guest_rflags;
    XMHF_SLAB_CALLNEW(&spl);

    ssteptrace_on=true;
}
}

// trace (single-step) off
static void st_off(u32 cpuindex, u32 guest_slab_index){
    u32 guest_rflags;
    u32 exception_bitmap;
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
    XMHF_SLAB_CALLNEW(&spl);
    guest_rflags = gcpustate_vmrwp->value;

    gcpustate_vmrwp->encoding = VMCS_CONTROL_EXCEPTION_BITMAP;
    XMHF_SLAB_CALLNEW(&spl);
    exception_bitmap = gcpustate_vmrwp->value;


    guest_rflags &= ~(EFLAGS_TF);
    exception_bitmap &= ~(1 << 1);

     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
    gcpustate_vmrwp->encoding = VMCS_CONTROL_EXCEPTION_BITMAP;
    gcpustate_vmrwp->value = exception_bitmap;
    XMHF_SLAB_CALLNEW(&spl);

    gcpustate_vmrwp->encoding = VMCS_GUEST_RFLAGS;
    gcpustate_vmrwp->value = guest_rflags;
    XMHF_SLAB_CALLNEW(&spl);

    ssteptrace_on=false;
}
}



static u8 _st_sigdatabase[][SHA_DIGEST_LENGTH] = {
  {0xd1, 0x4e, 0x30, 0x25,  0x8e,  0x16, 0x85, 0x9b, 0x21, 0x81, 0x74, 0x78, 0xbb, 0x1b, 0x5d, 0x99, 0xb5, 0x48, 0x60, 0xca},
  {0xa1, 0x4e, 0x30, 0x25,  0x8e,  0x16, 0x85, 0x9b, 0x21, 0x71, 0x74, 0x78, 0xbb, 0x1b, 0x5d, 0x99, 0xb5, 0x48, 0x60, 0xca},
  {0xf1, 0x4e, 0x30, 0x25,  0x8e,  0x16, 0x85, 0x9b, 0x21, 0x81, 0x54, 0x78, 0xbb, 0x1b, 0x5d, 0x99, 0xb5, 0x48, 0x60, 0xca},
  {0xe1, 0x4e, 0x30, 0x25,  0x9e,  0x16, 0x85, 0x9b, 0x21, 0x81, 0x74, 0x78, 0x6b, 0x1b, 0x5d, 0x99, 0xb5, 0x48, 0x60, 0xca},
};

#define NUMENTRIES_ST_SIGDATABASE  (sizeof(_st_sigdatabase)/sizeof(_st_sigdatabase[0]))


// scan for a trace match with incoming trace in buffer
static bool st_scanforsignature(u8 *buffer, u32 buffer_size){
    u8 digest[SHA_DIGEST_LENGTH];
    u64 i;

    //compute SHA-1 of the buffer
    sha1(buffer, buffer_size, digest);

    //compare computed SHA-1 to the signature database
    for(i=0; i < NUMENTRIES_ST_SIGDATABASE; i++){
        if(!memcmp(&digest, &_st_sigdatabase[i], SHA_DIGEST_LENGTH)){
            return true;
        }
    }

    //no match
    return false;
}
*/


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

/*
// trap exception
static void _hcb_trap_exception(u32 cpuindex, u32 guest_slab_index){
    u32 info_vmexit_interruption_information;
    u32 guest_rip;
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
        XMHF_SLAB_CALLNEW(&spl);
        info_vmexit_interruption_information = gcpustate_vmrwp->value;

        _XDPRINTF_("%s[%u]: guest slab %u exception %u...\n",
                   __func__, (u16)cpuindex, guest_slab_index,
                   (u8)info_vmexit_interruption_information);

        if((u8)info_vmexit_interruption_information != 0x1)
            return;

        gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
        XMHF_SLAB_CALLNEW(&spl);
        guest_rip = gcpustate_vmrwp->value;

        _XDPRINTF_("%s[%u]: guest slab RIP=%x\n",
                   __func__, (u16)cpuindex, guest_rip);

        //copy 256 bytes from the current guest RIP for trace inference
        //spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMACC;
        //smemaccp->dst_slabid = guest_slab_index;
        //smemaccp->addr_to = &_st_tracebuffer;
        //smemaccp->addr_from = guest_rip;
        //smemaccp->numbytes = sizeof(_st_tracebuffer);
        ////spl.in_out_params[0] = XMHF_HIC_UAPI_PHYSMEM;
        // spl.dst_uapifn = XMHF_HIC_UAPI_PHYSMEM_PEEK;
        //XMHF_SLAB_CALLNEW(&spl);
        CASM_FUNCCALL(xmhfhw_sysmemaccess_copy, &_st_tracebuffer, guest_rip, sizeof(_st_tracebuffer));

        //try to see if we found a match in our trace database
        st_scanforsignature(&_st_tracebuffer, sizeof(_st_tracebuffer));
        _XDPRINTF_("%s[%u]: scan complete\n",
                   __func__, (u16)cpuindex);

    }

}
*/

// shutdown
static void _hcb_shutdown(u32 cpuindex, u32 guest_slab_index){
	_XDPRINTF_("%s[%u]: guest slab %u shutdown...\n",
            __func__, (u16)cpuindex, guest_slab_index);
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

        //case XC_HYPAPPCB_TRAP_INSTRUCTION:{
        //
        //
        //}
        //break;

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

