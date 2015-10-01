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
#include <xmhfgeec.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <uapi_gcpustate.h>
//#include <uapi_slabmemacc.h>
#include <uapi_slabmempgtbl.h>

#include <xh_syscalllog.h>


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

static sl_log_type_t sl_log[128];

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
        //xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)&spl.in_out_params[2];
        //xmhf_uapi_slabmemacc_params_t *smemaccp = (xmhf_uapi_slabmemacc_params_t *)spl.in_out_params;

        _XDPRINTF_("%s[%u]: starting...\n", __func__, (u16)cpuindex);
        spl.src_slabid = XMHFGEEC_SLAB_XH_SYSCALLLOG;
        //spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMACC;
        spl.cpuid = cpuindex;
        //spl.in_out_params[0] = XMHF_HIC_UAPI_PHYSMEM;

        //copy code page at gpa
        //smemaccp->dst_slabid = guest_slab_index;
        //smemaccp->addr_to = &_sl_pagebuffer;
        //smemaccp->addr_from = gpa;
        //smemaccp->numbytes = sizeof(_sl_pagebuffer);
        // spl.dst_uapifn = XMHF_HIC_UAPI_PHYSMEM_PEEK;
        //XMHF_SLAB_CALLNEW(&spl);
	CASM_FUNCCALL(xmhfhw_sysmemaccess_copy, &_sl_pagebuffer,
		gpa, sizeof(_sl_pagebuffer));

        _XDPRINTF_("%s[%u]: grabbed page contents at gpa=%016llx\n",
               __func__, (u16)cpuindex, gpa);

        //compute SHA-1 of the syscall page
        sha1(&_sl_pagebuffer, sizeof(_sl_pagebuffer), _sl_syscalldigest);


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
    xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs =
        (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
    x86regs_t *gprs = (x86regs_t *)&gcpustate_gprs->gprs;
	u32 call_id;
	u64 gpa;

    spl.src_slabid = XMHFGEEC_SLAB_XH_SYSCALLLOG;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.cpuid = cpuindex;
    //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;

     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
    XMHF_SLAB_CALLNEW(&spl);

    call_id = gprs->eax;
    gpa = ((u64)gprs->ebx << 32) | gprs->edx;

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
    xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp =
        (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;
    xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs =
        (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
    //xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)&spl.in_out_params[2];
    //xmhf_uapi_slabmemacc_params_t *smemaccp = (xmhf_uapi_slabmemacc_params_t *)spl.in_out_params;

    u8 syscalldigest[SHA_DIGEST_LENGTH];
    bool syscallhandler_modified=false;
    x86regs_t r;

    if(!_sl_registered)
        return;

	_XDPRINTF_("%s[%u]: memory fault in guest slab %u; gpa=%016llx, gva=%016llx, errorcode=%016llx, sysenter execution?\n",
            __func__, (u16)cpuindex, guest_slab_index, gpa, gva, errorcode);

    spl.src_slabid = XMHFGEEC_SLAB_XH_SYSCALLLOG;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.cpuid = cpuindex;
    //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;


    //read GPR state
     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
    XMHF_SLAB_CALLNEW(&spl);
    memcpy(&r, &gcpustate_gprs->gprs, sizeof(x86regs_t));

    //copy code page at SYSENTER (referenced by shadow_sysenter_rip)
    //spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMACC;
    //smemaccp->dst_slabid = guest_slab_index;
    //smemaccp->addr_to = &_sl_pagebuffer;
    //smemaccp->addr_from = shadow_sysenter_rip;
    //smemaccp->numbytes = sizeof(_sl_pagebuffer);
    ////spl.in_out_params[0] = XMHF_HIC_UAPI_PHYSMEM;
    // spl.dst_uapifn = XMHF_HIC_UAPI_PHYSMEM_PEEK;
    //XMHF_SLAB_CALLNEW(&spl);
    CASM_FUNCCALL(xmhfhw_sysmemaccess_copy, &_sl_pagebuffer,
		shadow_sysenter_rip, sizeof(_sl_pagebuffer));

    //compute SHA-1 of the syscall page
    sha1(&_sl_pagebuffer, sizeof(_sl_pagebuffer), syscalldigest);

    //check to see if syscall handler has been modified
    if(memcmp(&_sl_syscalldigest, &syscalldigest, SHA_DIGEST_LENGTH))
        syscallhandler_modified=true;

	_XDPRINTF_("%s[%u]: syscall modified = %s\n",
            __func__, (u16)cpuindex, (syscallhandler_modified ? "true" : "false"));


    //log GPR state, syscall modified status and digest
    sl_loginfo(syscallhandler_modified, &syscalldigest, &r);

    //set guest RIP to shadow_sysenter_rip to continue execution
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;
     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
    gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
    gcpustate_vmrwp->value = shadow_sysenter_rip;
    XMHF_SLAB_CALLNEW(&spl);

}


// instruction trap
static u32 _hcb_trap_instruction(u32 cpuindex, u32 guest_slab_index, u32 insntype){
    slab_params_t spl;
    xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp =
        (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;
    xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs =
        (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
    u32 status=XC_HYPAPPCB_CHAIN;
    u32 guest_rip, msrvalue;
    u32 info_vmexit_instruction_length;
    x86regs_t *r = (x86regs_t *)&gcpustate_gprs->gprs;

    if(!_sl_registered)
        return status;

    spl.src_slabid = XMHFGEEC_SLAB_XH_SYSCALLLOG;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.cpuid = cpuindex;
    //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;


    if (insntype == XC_HYPAPPCB_TRAP_INSTRUCTION_WRMSR){

         spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
        XMHF_SLAB_CALLNEW(&spl);
        msrvalue = r->ecx;

        switch(msrvalue){
            case IA32_SYSENTER_EIP_MSR:{
                //xmhf_hic_uapi_mempgtbl_desc_t *mdesc = (xmhf_hic_uapi_mempgtbl_desc_t *)&spl.in_out_params[2];
                //xmhf_uapi_slabmempgtbl_entry_params_t *smpgtblep =
                //    (xmhf_uapi_slabmempgtbl_entry_params_t *)spl.in_out_params;
                xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *getentryforpaddrp =
                (xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *)spl.in_out_params;
                xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
                (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;


              	_XDPRINTF_("%s[%u]: emulating WRMSR SYSENTER_EIP_MSR\n", __func__, (u16)cpuindex);

                shadow_sysenter_rip = ( ((u64)(u32)r->edx << 32) | (u32)r->eax ) ;

                 spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
                gcpustate_vmrwp->encoding = VMCS_GUEST_SYSENTER_EIP;
                gcpustate_vmrwp->value = 0;
                XMHF_SLAB_CALLNEW(&spl);

                if(!sl_activated){
                    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;

                     spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR;
                    getentryforpaddrp->dst_slabid = guest_slab_index;
                    getentryforpaddrp->gpa = 0;
                    XMHF_SLAB_CALLNEW(&spl);

                     spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
                    setentryforpaddrp->dst_slabid = guest_slab_index;
                    setentryforpaddrp->gpa = 0;
                    setentryforpaddrp->entry = getentryforpaddrp->result_entry & ~(0x7);
                    XMHF_SLAB_CALLNEW(&spl);

                    sl_activated=true;
                }

                status = XC_HYPAPPCB_NOCHAIN;
            }
            break;

            default:
                break;
        }

    }else if (insntype == XC_HYPAPPCB_TRAP_INSTRUCTION_RDMSR){

         spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
        XMHF_SLAB_CALLNEW(&spl);
        msrvalue = r->ecx;

        switch(msrvalue){
            case IA32_SYSENTER_EIP_MSR:
              	_XDPRINTF_("%s[%u]: emulating RDMSR SYSENTER_EIP_MSR\n", __func__, (u16)cpuindex);

                r->edx = shadow_sysenter_rip >> 32;
                r->eax = (u32)shadow_sysenter_rip;

                 spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE;
                XMHF_SLAB_CALLNEW(&spl);

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
        spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
        //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;

         spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
        gcpustate_vmrwp->encoding = VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH;
        XMHF_SLAB_CALLNEW(&spl);
        info_vmexit_instruction_length = gcpustate_vmrwp->value;

        gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
        XMHF_SLAB_CALLNEW(&spl);
        guest_rip = gcpustate_vmrwp->value;

        guest_rip+=info_vmexit_instruction_length;

         spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
        gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
        gcpustate_vmrwp->value = guest_rip;
        XMHF_SLAB_CALLNEW(&spl);
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


	_XDPRINTF_("XHSYSCALLLOG[%u]: Got control, cbtype=%x: ESP=%08x\n",
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

         	spl.src_slabid = XMHFGEEC_SLAB_XH_SYSCALLLOG;
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
            _XDPRINTF_("%s[%u]: Unknown cbtype. Ignoring!\n",
                __func__, (u16)sp->cpuid);
        }
    }

}
