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

#include <xc.h>
#include <xhssteptrace.h>


//////
XMHF_SLAB(xhssteptrace)

#define SSTEPTRACE_REGISTER    			0xE0
#define SSTEPTRACE_ON          			0xE1
#define SSTEPTRACE_OFF         			0xE2


static u8 _st_tracebuffer[256];

// trace (single-step) on
static void st_on(u64 cpuindex, u64 guest_slab_index){
    u64 guest_rflags;
    u64 exception_bitmap;

if(!ssteptrace_on){
    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_RFLAGS, &guest_rflags);
    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_CONTROL_EXCEPTION_BITMAP, &exception_bitmap);
    guest_rflags |= EFLAGS_TF;
    exception_bitmap |= (1 << 1);
    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_CONTROL_EXCEPTION_BITMAP, exception_bitmap);
    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RFLAGS, guest_rflags);

    ssteptrace_on=true;
}
}

// trace (single-step) off
static void st_off(u64 cpuindex, u64 guest_slab_index){
    u64 guest_rflags;
    u64 exception_bitmap;

if(ssteptrace_on){
    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_RFLAGS, &guest_rflags);
    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_CONTROL_EXCEPTION_BITMAP, &exception_bitmap);
    guest_rflags &= ~(EFLAGS_TF);
    exception_bitmap &= ~(1 << 1);
    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_CONTROL_EXCEPTION_BITMAP, exception_bitmap);
    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RFLAGS, guest_rflags);

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
static bool st_scanforsignature(u8 *buffer, u64 buffer_size){
    u8 digest[SHA_DIGEST_LENGTH];
    u64 i;

    //compute SHA-1 of the buffer
    sha1_buffer(buffer, buffer_size, digest);

    //compare computed SHA-1 to the signature database
    for(i=0; i < NUMENTRIES_ST_SIGDATABASE; i++){
        if(!memcmp(&digest, &_st_sigdatabase[i], SHA_DIGEST_LENGTH)){
            return true;
        }
    }

    //no match
    return false;
}



//////
// hypapp callbacks


// initialization
static void _hcb_initialize(u64 cpuindex){

	_XDPRINTF_("%s[%u]: xhssteptrace initializing...\n", __FUNCTION__, (u32)cpuindex);

}


// hypercall
static void _hcb_hypercall(u64 cpuindex, u64 guest_slab_index){
    x86regs64_t gprs;
	u64 call_id;
	u64 gpa;

    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &gprs);

    call_id = gprs.rax;
    gpa = gprs.rbx;

	_XDPRINTF_("%s[%u]: call_id=%x, gpa=%x\n", __FUNCTION__, (u32)cpuindex,
            call_id, gpa);


	switch(call_id){

		case SSTEPTRACE_ON:{
			st_on(cpuindex, guest_slab_index);
		}
		break;

		case SSTEPTRACE_OFF:{
			st_off(cpuindex, guest_slab_index);
		}
		break;

		default:
            _XDPRINTF_("%s[%u]: unsupported hypercall %x. Ignoring\n",
                       __FUNCTION__, (u32)cpuindex, call_id);
			break;
	}



}


// trap exception
static void _hcb_trap_exception(u64 cpuindex, u64 guest_slab_index){
    u64 info_vmexit_interruption_information;
    u64 guest_rip;
    xmhf_hic_uapi_physmem_desc_t pdesc;

    if(ssteptrace_on){
        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_INTERRUPT_INFORMATION, &info_vmexit_interruption_information);

        _XDPRINTF_("%s[%u]: guest slab %u exception %u...\n", __FUNCTION__, (u32)cpuindex, guest_slab_index, (u8)info_vmexit_interruption_information);

        if((u8)info_vmexit_interruption_information != 0x1)
            return;

        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_RIP, &guest_rip);

        //copy 256 bytes from the current guest RIP for trace inference
        pdesc.guest_slab_index = guest_slab_index;
        pdesc.addr_to = &_st_tracebuffer;
        pdesc.addr_from = guest_rip;
        pdesc.numbytes = sizeof(_st_tracebuffer);
        XMHF_HIC_SLAB_UAPI_PHYSMEM(XMHF_HIC_UAPI_PHYSMEM_PEEK, &pdesc, NULL);

        //try to see if we found a match in our trace database
        st_scanforsignature(&_st_tracebuffer, sizeof(_st_tracebuffer));
    }

}


// shutdown
static void _hcb_shutdown(u64 cpuindex, u64 guest_slab_index){
	_XDPRINTF_("%s[%u]: guest slab %u shutdown...\n", __FUNCTION__, (u32)cpuindex, guest_slab_index);
}











///////
// slab interface

void xhssteptrace_interface(slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 src_slabid, u64 cpuindex){
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
            _hcb_hypercall(cpuindex, hcb_iparams->guest_slab_index);
        }
        break;

        //case XC_HYPAPPCB_MEMORYFAULT:{
        //
        //
        //}
        //break;

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

        case XC_HYPAPPCB_TRAP_EXCEPTION:{
            _hcb_trap_exception(cpuindex, hcb_iparams->guest_slab_index);
        }
        break;


        default:{
            _XDPRINTF_("%s[%u]: Unknown cbtype. Halting!\n",
                __FUNCTION__, (u32)cpuindex);
            //HALT();
        }
    }

}
