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
#include <xmhfhicslab.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <xhsyscalllog.h>


//////
//XMHF_SLABNEW(xhsyscalllog)

#define SYSCALLLOG_REGISTER     			0xF0


static u8 _sl_pagebuffer[PAGE_SIZE_4K];
static u8 _sl_syscalldigest[SHA_DIGEST_LENGTH];
static u64 shadow_sysenter_rip=0;



#define MAX_SL_LOG_SIZE 128
typedef struct {
    bool syscallmodified;
    u8 syscalldigest[SHA_DIGEST_LENGTH];
    x86regs_t r;
} sl_log_type_t;

sl_log_type_t sl_log[128];

static u64 sl_log_index=0;

// logs given info into memory buffer sl_log
static void sl_loginfo(bool syscallmodified, u8 *digest, x86regs_t *r){
    if(sl_log_index < MAX_SL_LOG_SIZE){
        sl_log[sl_log_index].syscallmodified = syscallmodified;
        memcpy(&sl_log[sl_log_index].syscalldigest, digest, SHA_DIGEST_LENGTH);
        memcpy(&sl_log[sl_log_index].r, r, sizeof(x86regs_t));
        sl_log_index++;
    }
}



//register a syscall handler code page (at gpa)
static void sl_register(u32 cpuindex, u32 guest_slab_index, u64 gpa){
        slab_params_t spl;
        xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)&spl.in_out_params[2];

        _XDPRINTF_("%s[%u]: starting...\n", __func__, (u16)cpuindex);
        spl.src_slabid = XMHF_HYP_SLAB_XHSYSCALLLOG;
        spl.cpuid = cpuindex;
        spl.in_out_params[0] = XMHF_HIC_UAPI_PHYSMEM;

        //copy code page at gpa
        pdesc->guest_slab_index = guest_slab_index;
        pdesc->addr_to = &_sl_pagebuffer;
        pdesc->addr_from = gpa;
        pdesc->numbytes = sizeof(_sl_pagebuffer);
        //XMHF_HIC_SLAB_UAPI_PHYSMEM(XMHF_HIC_UAPI_PHYSMEM_PEEK, &pdesc, NULL);
        spl.in_out_params[1] = XMHF_HIC_UAPI_PHYSMEM_PEEK;
        XMHF_SLAB_UAPI(&spl);

        _XDPRINTF_("%s[%u]: grabbed page contents at gpa=%016llx\n",
               __func__, (u16)cpuindex, gpa);

        //compute SHA-1 of the syscall page
        sha1_buffer(&_sl_pagebuffer, sizeof(_sl_pagebuffer), _sl_syscalldigest);


        _XDPRINTF_("%s[%u]: computed SHA-1: %*D\n",
               __func__, (u16)cpuindex, SHA_DIGEST_LENGTH, _sl_syscalldigest, " ");

        _sl_registered=true;
}


//////
// hypapp callbacks

// initialization
static void _hcb_initialize(u32 cpuindex){
	_XDPRINTF_("%s[%u]: syscalllog initializing...\n", __func__, (u16)cpuindex);
}

// hypercall
static void _hcb_hypercall(u32 cpuindex, u32 guest_slab_index){
    slab_params_t spl;
    x86regs_t *gprs = (x86regs_t *)&spl.in_out_params[2];
	u32 call_id;
	u64 gpa;

    spl.src_slabid = XMHF_HYP_SLAB_XHAPPROVEXEC;
    spl.cpuid = cpuindex;
    spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;

    //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &gprs);
    spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
    XMHF_SLAB_UAPI(&spl);

    call_id = gprs->eax;
    gpa = ((u64)gprs->edx << 32) | gprs->ebx;

	_XDPRINTF_("%s[%u]: call_id=%x, gpa=%016llx\n", __func__, (u16)cpuindex, call_id, gpa);


	switch(call_id){

		case SYSCALLLOG_REGISTER:{
			sl_register(cpuindex, guest_slab_index, gpa);
		}
		break;

		default:
            _XDPRINTF_("%s[%u]: unsupported hypercall %x. Ignoring\n",
                       __func__, (u16)cpuindex, call_id);
			break;
	}

}


// memory fault
static void _hcb_memoryfault(u32 cpuindex, u32 guest_slab_index, u64 gpa, u64 gva, u64 errorcode){
    slab_params_t spl;
    xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)&spl.in_out_params[2];
    u8 syscalldigest[SHA_DIGEST_LENGTH];
    bool syscallhandler_modified=false;
    x86regs_t r;

    if(!_sl_registered)
        return;

	_XDPRINTF_("%s[%u]: memory fault in guest slab %u; gpa=%016llx, gva=%016llx, errorcode=%016llx, sysenter execution?\n",
            __func__, (u16)cpuindex, guest_slab_index, gpa, gva, errorcode);

    spl.src_slabid = XMHF_HYP_SLAB_XHAPPROVEXEC;
    spl.cpuid = cpuindex;
    spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;


    //read GPR state
    //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &r);
    spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
    XMHF_SLAB_UAPI(&spl);
    memcpy(&r, &spl.in_out_params[2], sizeof(x86regs_t));

    //copy code page at SYSENTER (referenced by shadow_sysenter_rip)
    pdesc->guest_slab_index = guest_slab_index;
    pdesc->addr_to = &_sl_pagebuffer;
    pdesc->addr_from = shadow_sysenter_rip;
    pdesc->numbytes = sizeof(_sl_pagebuffer);
    //XMHF_HIC_SLAB_UAPI_PHYSMEM(XMHF_HIC_UAPI_PHYSMEM_PEEK, &pdesc, NULL);
    spl.in_out_params[0] = XMHF_HIC_UAPI_PHYSMEM;
    spl.in_out_params[1] = XMHF_HIC_UAPI_PHYSMEM_PEEK;
    XMHF_SLAB_UAPI(&spl);

    //compute SHA-1 of the syscall page
    sha1_buffer(&_sl_pagebuffer, sizeof(_sl_pagebuffer), syscalldigest);

    //check to see if syscall handler has been modified
    if(memcmp(&_sl_syscalldigest, &syscalldigest, SHA_DIGEST_LENGTH))
        syscallhandler_modified=true;

	_XDPRINTF_("%s[%u]: syscall modified = %s\n",
            __func__, (u16)cpuindex, (syscallhandler_modified ? "true" : "false"));


    //log GPR state, syscall modified status and digest
    sl_loginfo(syscallhandler_modified, &syscalldigest, &r);

    //set guest RIP to shadow_sysenter_rip to continue execution
    //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RIP, shadow_sysenter_rip);
    spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;
    spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
    spl.in_out_params[2] = VMCS_GUEST_RIP;
    spl.in_out_params[4] = (u32)shadow_sysenter_rip;
    XMHF_SLAB_UAPI(&spl);

}


// instruction trap
static u32 _hcb_trap_instruction(u32 cpuindex, u32 guest_slab_index, u32 insntype){
    slab_params_t spl;
    u32 status=XC_HYPAPPCB_CHAIN;
    u32 guest_rip, msrvalue;
    u32 info_vmexit_instruction_length;
    x86regs_t *r = (x86regs_t *)&spl.in_out_params[2];

    if(!_sl_registered)
        return status;

    spl.src_slabid = XMHF_HYP_SLAB_XHSYSCALLLOG;
    spl.cpuid = cpuindex;
    spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;


    if (insntype == XC_HYPAPPCB_TRAP_INSTRUCTION_WRMSR){

        //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &r);
        spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
        XMHF_SLAB_UAPI(&spl);
        msrvalue = r->ecx;

        switch(msrvalue){
            case IA32_SYSENTER_EIP_MSR:{
                xmhf_hic_uapi_mempgtbl_desc_t *mdesc = (xmhf_hic_uapi_mempgtbl_desc_t *)&spl.in_out_params[2];

              	_XDPRINTF_("%s[%u]: emulating WRMSR SYSENTER_EIP_MSR\n", __func__, (u16)cpuindex);

                shadow_sysenter_rip = ( ((u64)(u32)r->edx << 32) | (u32)r->eax ) ;

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_SYSENTER_EIP, 0);
                spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                spl.in_out_params[2] = VMCS_GUEST_SYSENTER_EIP;
                spl.in_out_params[4] = 0;
                XMHF_SLAB_UAPI(&spl);

                if(!sl_activated){
                    mdesc->guest_slab_index = guest_slab_index;
                    mdesc->gpa = 0;
                    spl.in_out_params[0] = XMHF_HIC_UAPI_MEMPGTBL;
                    spl.in_out_params[1] = XMHF_HIC_UAPI_MEMPGTBL_GETENTRY;
                    //XMHF_HIC_SLAB_UAPI_MEMPGTBL(XMHF_HIC_UAPI_MEMPGTBL_GETENTRY, &mdesc, &mdesc);
                    XMHF_SLAB_UAPI(&spl);

                    mdesc->entry &= ~(0x7);

                    //XMHF_HIC_SLAB_UAPI_MEMPGTBL(XMHF_HIC_UAPI_MEMPGTBL_SETENTRY, &mdesc, NULL);
                    spl.in_out_params[1] = XMHF_HIC_UAPI_MEMPGTBL_SETENTRY;
                    XMHF_SLAB_UAPI(&spl);

                    sl_activated=true;
                }

                status = XC_HYPAPPCB_NOCHAIN;
            }
            break;

            default:
                break;
        }

    }else if (insntype == XC_HYPAPPCB_TRAP_INSTRUCTION_RDMSR){

        //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD, NULL, &r);
        spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
        XMHF_SLAB_UAPI(&spl);
        msrvalue = r->ecx;

        switch(msrvalue){
            case IA32_SYSENTER_EIP_MSR:
              	_XDPRINTF_("%s[%u]: emulating RDMSR SYSENTER_EIP_MSR\n", __func__, (u16)cpuindex);

                r->edx = shadow_sysenter_rip >> 32;
                r->eax = (u32)shadow_sysenter_rip;

                //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE, &r, NULL);
                spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE;
                XMHF_SLAB_UAPI(&spl);

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
        spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;

        //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH, &info_vmexit_instruction_length);
        spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
        spl.in_out_params[2] = VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH;
        XMHF_SLAB_UAPI(&spl);
        info_vmexit_instruction_length = spl.in_out_params[4];

        //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMREAD, VMCS_GUEST_RIP, &guest_rip);
        spl.in_out_params[2] = VMCS_GUEST_RIP;
        XMHF_SLAB_UAPI(&spl);
        guest_rip = spl.in_out_params[4];

        guest_rip+=info_vmexit_instruction_length;

        //XMHF_HIC_SLAB_UAPI_CPUSTATE(XMHF_HIC_UAPI_CPUSTATE_VMWRITE, VMCS_GUEST_RIP, guest_rip);
        spl.in_out_params[1] = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
        spl.in_out_params[2] = VMCS_GUEST_RIP;
        spl.in_out_params[4] = guest_rip;
        XMHF_SLAB_UAPI(&spl);
    }

    return status;
}


// shutdown
static void _hcb_shutdown(u32 cpuindex, u32 guest_slab_index){
	_XDPRINTF_("%s[%u]: guest slab %u shutdown...\n",
            __func__, (u16)cpuindex, guest_slab_index);
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
                __func__, (u16)sp->cpuid, hcbp->cbtype, read_esp());


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

         	spl.src_slabid = XMHF_HYP_SLAB_XHAPPROVEXEC;
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

        case XC_HYPAPPCB_TRAP_INSTRUCTION:{
            hcbp->cbresult = _hcb_trap_instruction(sp->cpuid, hcbp->guest_slab_index, hcbp->cbqual);
        }
        break;

        //case XC_HYPAPPCB_TRAP_EXCEPTION:{
        //
        //
        //}
        //break;


        default:{
            _XDPRINTF_("%s[%u]: Unknown cbtype. Halting!\n",
                __func__, (u16)sp->cpuid);
            //HALT();
        }
    }

}
