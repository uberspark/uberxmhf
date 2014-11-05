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

// syscalllog hypapp main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhf-debug.h>
#include <xmhf-core.h>

#include <xhsyscalllog.h>


//////
XMHF_SLAB(xhsyscalllog)

#define SYSCALLLOG_REGISTER     			0xF0


static u8 _sl_pagebuffer[PAGE_SIZE_4K];
static u8 _sl_syscalldigest[SHA_DIGEST_LENGTH];
static bool _sl_registered=false;
static u64 shadow_sysenter_rip=0;



#define MAX_SL_LOG_SIZE 128
typedef struct {
    bool syscallmodified;
    u8 syscalldigest[SHA_DIGEST_LENGTH];
    x86regs64_t r;
} sl_log_type_t;

sl_log_type_t sl_log[128];

static u64 sl_log_index=0;

// logs given info into memory buffer sl_log
static void sl_loginfo(bool syscallmodified, u8 *digest, x86regs64_t *r){
    if(sl_log_index < MAX_SL_LOG_SIZE){
        sl_log[sl_log_index].syscallmodified = syscallmodified;
        memcpy(&sl_log[sl_log_index].syscalldigest, digest, SHA_DIGEST_LENGTH);
        memcpy(&sl_log[sl_log_index].r, r, sizeof(x86regs64_t));
        sl_log_index++;
    }
}



//register a syscall handler code page (at gpa)
static void sl_register(u64 cpuindex, u64 guest_slab_index, u64 gpa){
        xmhf_hic_uapi_physmem_desc_t pdesc;

        _XDPRINTF_("%s[%u]: starting...\n", __FUNCTION__, (u32)cpuindex);

        //copy code page at gpa
        pdesc.guest_slab_index = guest_slab_index;
        pdesc.addr_to = &_sl_pagebuffer;
        pdesc.addr_from = gpa;
        pdesc.numbytes = sizeof(_sl_pagebuffer);
        XMHF_HIC_SLAB_UAPI_PHYSMEM(XMHF_HIC_UAPI_PHYSMEM_PEEK, &pdesc, NULL);

        _XDPRINTF_("%s[%u]: grabbed page contents at gpa=%x\n",
               __FUNCTION__, (u32)cpuindex, gpa);

        //compute SHA-1 of the syscall page
        sha1_buffer(&_sl_pagebuffer, sizeof(_sl_pagebuffer), _sl_syscalldigest);


        _XDPRINTF_("%s[%u]: computed SHA-1: %*D\n",
               __FUNCTION__, (u32)cpuindex, SHA_DIGEST_LENGTH, _sl_syscalldigest, " ");

        _sl_registered=true;
}


//////
// hypapp callbacks

// initialization
static void _hcb_initialize(u64 cpuindex){
	_XDPRINTF_("%s[%u]: syscalllog initializing...\n", __FUNCTION__, (u32)cpuindex);
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

		case SYSCALLLOG_REGISTER:{
			sl_register(cpuindex, guest_slab_index, gpa);
		}
		break;

		default:
            _XDPRINTF_("%s[%u]: unsupported hypercall %x. Ignoring\n",
                       __FUNCTION__, (u32)cpuindex, call_id);
			break;
	}

}


// memory fault
static void _hcb_memoryfault(u64 cpuindex, u64 guest_slab_index, u64 gpa, u64 gva, u64 errorcode){
    xmhf_hic_uapi_physmem_desc_t pdesc;
    u8 syscalldigest[SHA_DIGEST_LENGTH];
    bool syscallhandler_modified=false;
    x86regs64_t r;

    if(!_sl_registered)
        return;

	_XDPRINTF_("%s[%u]: memory fault in guest slab %u; gpa=%x, gva=%x, errorcode=%x, sysenter execution?\n",
            __FUNCTION__, (u32)cpuindex, guest_slab_index, gpa, gva, errorcode);


    //read GPR state
    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &r);

    //copy code page at SYSENTER (referenced by shadow_sysenter_rip)
    pdesc.guest_slab_index = guest_slab_index;
    pdesc.addr_to = &_sl_pagebuffer;
    pdesc.addr_from = shadow_sysenter_rip;
    pdesc.numbytes = sizeof(_sl_pagebuffer);
    XMHF_HIC_SLAB_UAPI_PHYSMEM(XMHF_HIC_UAPI_PHYSMEM_PEEK, &pdesc, NULL);

    //compute SHA-1 of the syscall page
    sha1_buffer(&_sl_pagebuffer, sizeof(_sl_pagebuffer), syscalldigest);

    //check to see if syscall handler has been modified
    if(memcmp(&_sl_syscalldigest, &syscalldigest, SHA_DIGEST_LENGTH))
        syscallhandler_modified=true;

	_XDPRINTF_("%s[%u]: syscall modified = %s\n",
            __FUNCTION__, (u32)cpuindex, (syscallhandler_modified ? "true" : "false"));


    //log GPR state, syscall modified status and digest
    sl_loginfo(syscallhandler_modified, &syscalldigest, &r);

    //set guest RIP to shadow_sysenter_rip to continue execution
    XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RIP, shadow_sysenter_rip);
}


// instruction trap
static u64 _hcb_trap_instruction(u64 cpuindex, u64 guest_slab_index, u64 insntype){
    u64 status=XC_HYPAPPCB_CHAIN;
    u64 guest_rip, msrvalue;
    u64 info_vmexit_instruction_length;
    x86regs64_t r;

    if(!_sl_registered)
        return status;

    if (insntype == XC_HYPAPPCB_TRAP_INSTRUCTION_WRMSR){

        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &r);

        switch((u32)r.rcx){
            case IA32_SYSENTER_EIP_MSR:{
                xmhf_hic_uapi_mempgtbl_desc_t mdesc;

              	_XDPRINTF_("%s[%u]: emulating WRMSR SYSENTER_EIP_MSR\n", __FUNCTION__, (u32)cpuindex);

                shadow_sysenter_rip = ( ((u64)(u32)r.rdx << 32) | (u32)r.rax ) ;
                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_SYSENTER_EIP, 0);

                mdesc.guest_slab_index = guest_slab_index;
                mdesc.gpa = 0;
                XMHF_HIC_SLAB_UAPI_MEMPGTBL(XMHF_HIC_UAPI_MEMPGTBL_GETENTRY, &mdesc, &mdesc);
                mdesc.entry &= ~(0x7);
                XMHF_HIC_SLAB_UAPI_MEMPGTBL(XMHF_HIC_UAPI_MEMPGTBL_SETENTRY, &mdesc, NULL);

                status = XC_HYPAPPCB_NOCHAIN;
            }
            break;

            default:
                break;
        }

    }else if (insntype == XC_HYPAPPCB_TRAP_INSTRUCTION_RDMSR){

        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &r);

        switch((u32)r.rcx){
            case IA32_SYSENTER_EIP_MSR:
              	_XDPRINTF_("%s[%u]: emulating RDMSR SYSENTER_EIP_MSR\n", __FUNCTION__, (u32)cpuindex);

                r.rdx = shadow_sysenter_rip >> 32;
                r.rax = (u32)shadow_sysenter_rip;

                XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE, &r, NULL);
                status = XC_HYPAPPCB_NOCHAIN;
                break;
            default:
                break;
        }

    }else{ //some instruction we don't care about, so just fall through


    }

    //if we emulated the instruction then do not chain, but update instruction pointer
    //accordingly
    if(status == XC_HYPAPPCB_NOCHAIN){
        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH, &info_vmexit_instruction_length);
        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_RIP, &guest_rip);
        guest_rip+=info_vmexit_instruction_length;
        XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RIP, guest_rip);
    }

    return status;
}


// shutdown
static void _hcb_shutdown(u64 cpuindex, u64 guest_slab_index){
	_XDPRINTF_("%s[%u]: guest slab %u shutdown...\n", __FUNCTION__, (u32)cpuindex, guest_slab_index);
}












//////
// slab interface

void xhsyscalllog_interface(slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 src_slabid, u64 cpuindex){
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

        case XC_HYPAPPCB_MEMORYFAULT:{
         	u64 errorcode;
         	u64 gpa;
         	u64 gva;

         	XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_EXIT_QUALIFICATION, &errorcode);
         	XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_GUEST_PADDR_FULL, &gpa);
         	XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_GUEST_LINEAR_ADDRESS, &gva);

            _hcb_memoryfault(cpuindex, hcb_iparams->guest_slab_index, gpa, gva, errorcode);
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

        case XC_HYPAPPCB_TRAP_INSTRUCTION:{
            hcb_oparams->cbresult = _hcb_trap_instruction(cpuindex, hcb_iparams->guest_slab_index, hcb_iparams->cbqual);
        }
        break;

        //case XC_HYPAPPCB_TRAP_EXCEPTION:{
        //
        //
        //}
        //break;


        default:{
            _XDPRINTF_("%s[%u]: Unknown cbtype. Halting!\n",
                __FUNCTION__, (u32)cpuindex);
            //HALT();
        }
    }

}
