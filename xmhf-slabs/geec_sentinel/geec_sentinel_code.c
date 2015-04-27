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

/*
 * HIC trampoline and stubs
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <xc.h>
#include <geec_sentinel.h>
#include <geec_primesmp.h> //TODO: we rely on this only for cpuidtable, need to eliminate


__attribute__((section(".data"))) u32 __xmhfhic_safestack_indices[MAX_PLATFORM_CPUS] = { 0 };
__attribute__((section(".data"))) __xmhfhic_safestack_element_t __xmhfhic_safestack[MAX_PLATFORM_CPUS][512];


void __xmhfhic_safepush(u32 cpuid, u32 src_slabid, u32 dst_slabid, u32 hic_calltype,
                        void *caller_stack_frame, slab_params_t *sp)
{
    u32 safestack_index =  __xmhfhic_safestack_indices[(u16)cpuid];
    if(safestack_index >=0 && safestack_index < 512) {
        __xmhfhic_safestack[(u16)cpuid][safestack_index].src_slabid = src_slabid;
        __xmhfhic_safestack[(u16)cpuid][safestack_index].dst_slabid = dst_slabid;
        __xmhfhic_safestack[(u16)cpuid][safestack_index].hic_calltype = hic_calltype;
        __xmhfhic_safestack[(u16)cpuid][safestack_index].caller_stack_frame = caller_stack_frame;
        __xmhfhic_safestack[(u16)cpuid][safestack_index].sp = sp;

        safestack_index++;
        __xmhfhic_safestack_indices[(u16)cpuid] = safestack_index;
    }
}

void __xmhfhic_safepop(u32 cpuid, u32 *src_slabid, u32 *dst_slabid, u32 *hic_calltype,
                       void **caller_stack_framep, slab_params_t **spp)
{
    u32 safestack_index =  __xmhfhic_safestack_indices[(u16)cpuid]-1;
    if(safestack_index >=0 && safestack_index < 512){
        *src_slabid = __xmhfhic_safestack[(u16)cpuid][safestack_index].src_slabid;
        *dst_slabid = __xmhfhic_safestack[(u16)cpuid][safestack_index].dst_slabid;
        *hic_calltype = __xmhfhic_safestack[(u16)cpuid][safestack_index].hic_calltype;
        *caller_stack_framep = __xmhfhic_safestack[(u16)cpuid][safestack_index].caller_stack_frame;
        *spp = __xmhfhic_safestack[(u16)cpuid][safestack_index].sp;

        __xmhfhic_safestack_indices[(u16)cpuid] = safestack_index;
    }
}





//////
// sentinel stubs, invoked by their CASM counterparts
//////

/*static void _geec_sentinel_dump_exframe(x86vmx_exception_frame_t *exframe){
    //dump relevant info
    _XDPRINTF_("%s: [START]\n\n", __func__);
    _XDPRINTF_("exception %x\n", exframe->vector);
    _XDPRINTF_("errorcode=0x%08x\n", exframe->error_code);
    _XDPRINTF_("CS:EIP:EFLAGS = 0x%08x:0x%08x:0x%08x\n", exframe->orig_cs, exframe->orig_rip, exframe->orig_rflags);
    _XDPRINTF_("SS:ESP = 0x%08x:0x%08x\n", exframe->orig_ss, exframe->orig_rsp);
    _XDPRINTF_("EAX=0x%08x, EBX=0x%08x\n", exframe->eax, exframe->ebx);
    _XDPRINTF_("ECX=0x%08x, EDX=0x%08x\n", exframe->ecx, exframe->edx);
    _XDPRINTF_("ESI=0x%08x, EDI=0x%08x\n", exframe->esi, exframe->edi);
    _XDPRINTF_("EBP=0x%08x, ESP=0x%08x\n", exframe->ebp, exframe->esp);
    _XDPRINTF_("%s: [END]\n\n", __func__);
}*/

////// exceptions

void _geec_sentinel_exception_stub(x86vmx_exception_frame_t *exframe){
    slab_params_t spl;

    memset(&spl, 0, sizeof(spl));


    spl.slab_ctype = XMHFGEEC_SENTINEL_CALL_EXCEPTION;
    spl.src_slabid = XMHFGEEC_SLAB_GEEC_SENTINEL; //XXX: TODO: grab src_slabid based on exframe->orig_rip
    spl.dst_slabid = XMHFGEEC_SLAB_XC_EXHUB;
    spl.cpuid = __xmhfhic_x86vmx_cpuidtable[xmhf_baseplatform_arch_x86_getcpulapicid()];
    memcpy(&spl.in_out_params[0], exframe,
           sizeof(x86vmx_exception_frame_t));

    //_geec_sentinel_dump_exframe(spl.in_out_params);
    geec_sentinel_main(&spl, &spl);
}



////// intercepts

void _geec_sentinel_intercept_stub(x86regs_t *r){
    slab_params_t spl;

    memset(&spl, 0, sizeof(spl));

    spl.slab_ctype = XMHFGEEC_SENTINEL_CALL_INTERCEPT;
    spl.src_slabid = CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VPID);
    spl.dst_slabid = XMHFGEEC_SLAB_XC_IHUB;
    spl.cpuid = __xmhfhic_x86vmx_cpuidtable[xmhf_baseplatform_arch_x86_getcpulapicid()];
    memcpy(&spl.in_out_params[0], r, sizeof(x86regs_t));

    geec_sentinel_main(&spl, &spl);

}





////// sysenter

//in general sp->xxx is untrusted and must be sanity checked
void _geec_sentinel_sysenter_stub(slab_params_t *sp, void *caller_stack_frame){

    //sanity check sp
    sp->cpuid = __xmhfhic_x86vmx_cpuidtable[xmhf_baseplatform_arch_x86_getcpulapicid()];

    if( !(sp->slab_ctype == XMHFGEEC_SENTINEL_RET_VfT_PROG_TO_uVT_uVU_PROG ||
          sp->slab_ctype == XMHFGEEC_SENTINEL_CALL_uVT_uVU_PROG_TO_VfT_PROG
          ) ){
        _XDPRINTF_("%s[ln:%u]: inconsistent sp->xxx (%x). halting!\n", __func__,
                   __LINE__, sp->slab_ctype);
        HALT();
    }

    sp->src_slabid =
        (CASM_FUNCCALL(read_cr3, CASM_NOPARAM) - _xmhfhic_common_slab_info_table[XMHFGEEC_SLAB_GEEC_SENTINEL].mempgtbl_cr3)/PAGE_SIZE_4K;

    _XDPRINTF_("%s: sp=%x, cpuid=%u, src=%u, dst=%u, ctype=%x\n", __func__,
               (u32)sp, (u16)sp->cpuid, sp->src_slabid, sp->dst_slabid, sp->slab_ctype);

    geec_sentinel_main(sp, caller_stack_frame);
}








//////
// geec sentinel helper functions
//////

static void _geec_sentinel_transition_vft_prog_to_uvt_uvu_prog(slab_params_t *sp, void *caller_stack_frame){
    slab_params_t *dst_sp;

    _XDPRINTF_("%s[%u]: src=%u, dst=%u\n", __func__, (u16)sp->cpuid, sp->src_slabid, sp->dst_slabid);

    //save caller stack frame address (esp)
    _XDPRINTF_("%s[%u]: src tos before=%x\n", __func__, (u16)sp->cpuid, _xmhfhic_common_slab_info_table[sp->src_slabid].slabtos[(u16)sp->cpuid]);
    _xmhfhic_common_slab_info_table[sp->src_slabid].slabtos[(u16)sp->cpuid] =
        (u32)caller_stack_frame;
    _XDPRINTF_("%s[%u]: src tos after=%x\n", __func__, (u16)sp->cpuid, _xmhfhic_common_slab_info_table[sp->src_slabid].slabtos[(u16)sp->cpuid]);


    //make space on destination slab stack for slab_params_t and copy parameters
    {
        _XDPRINTF_("%s[%u]: dst tos before=%x\n", __func__, (u16)sp->cpuid, _xmhfhic_common_slab_info_table[sp->dst_slabid].slabtos[(u16)sp->cpuid]);
        _xmhfhic_common_slab_info_table[sp->dst_slabid].slabtos[(u16)sp->cpuid] -= sizeof(slab_params_t);
        _XDPRINTF_("%s[%u]: dst tos after=%x\n", __func__, (u16)sp->cpuid, _xmhfhic_common_slab_info_table[sp->dst_slabid].slabtos[(u16)sp->cpuid]);
        dst_sp = (slab_params_t *) _xmhfhic_common_slab_info_table[sp->dst_slabid].slabtos[(u16)sp->cpuid];
        _XDPRINTF_("%s[%u]: copying params to dst_sp=%x from sp=%x\n", __func__, (u16)sp->cpuid,
                   (u32)dst_sp, (u32)sp);
        memcpy(dst_sp, sp, sizeof(slab_params_t));

    }

    //push src_slabid, dst_slabid, hic_calltype, caller_stack_frame and sp
    //tuple to safe stack
    _XDPRINTF_("%s[%u]: safepush: {cpuid: %u, src: %u, dst: %u, ctype: 0x%x, \
               csf=0x%x, sp=0x%x \n",
            __func__, (u16)sp->cpuid,
               (u16)sp->cpuid, sp->src_slabid, sp->dst_slabid, sp->slab_ctype,
               caller_stack_frame, sp);

    __xmhfhic_safepush((u16)sp->cpuid, sp->src_slabid, sp->dst_slabid,
                       sp->slab_ctype, caller_stack_frame, sp);


    //switch to destination slab page tables
    _XDPRINTF_("%s[%u]: dst mempgtbl base=%x\n", __func__,
               (u16)sp->cpuid, _xmhfhic_common_slab_info_table[sp->dst_slabid].mempgtbl_cr3);
    CASM_FUNCCALL(write_cr3,_xmhfhic_common_slab_info_table[sp->dst_slabid].mempgtbl_cr3);
    _XDPRINTF_("%s[%u]: swiched to dst mempgtbl\n", __func__,
               (u16)sp->cpuid);


    _XDPRINTF_("%s[%u]: entry=%x, dst_sp=%x, proceeding to xfer...\n", __func__,
               (u16)sp->cpuid, _xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub, (u32)dst_sp);


    CASM_FUNCCALL(_geec_sentinel_xfer_vft_prog_to_uvt_uvu_prog,
                _xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub,
                                  dst_sp);


    _XDPRINTF_("%s[%u]: wip. halting!\n", __func__, (u16)sp->cpuid);
    HALT();


}




static void _geec_sentinel_transition_ret_vft_prog_to_uvt_uvu_prog(slab_params_t *sp, void *caller_stack_frame){
    slab_params_t *dst_sp;
    __xmhfhic_safestack_element_t elem;

    _XDPRINTF_("%s[%u]: src=%u, dst=%u\n", __func__, (u16)sp->cpuid, sp->src_slabid, sp->dst_slabid);

    //pop tuple from safe stack
    __xmhfhic_safepop((u16)sp->cpuid, &elem.src_slabid, &elem.dst_slabid, &elem.hic_calltype, &elem.caller_stack_frame,
                        &elem.sp);

    _XDPRINTF_("%s[%u]: safepop: {cpuid: %u, src: %u, dst: %u, ctype: 0x%x, \
               csf=0x%x, sp=0x%x \n",
            __func__, (u16)sp->cpuid,
               (u16)sp->cpuid, elem.src_slabid, elem.dst_slabid, elem.hic_calltype,
               elem.caller_stack_frame, elem.sp);

    //check to ensure this return is paired with a prior call
    if ( !((elem.src_slabid == sp->dst_slabid) && (elem.dst_slabid == sp->src_slabid) &&
           (elem.hic_calltype == XMHFGEEC_SENTINEL_CALL_VfT_PROG_TO_uVT_uVU_PROG)) ){
        _XDPRINTF_("%s[ln:%u]: Fatal: ret does not match prior call. Halting!\n",
            __func__, __LINE__);
        HALT();
    }

    //marshall parameters
    memcpy( (elem.sp)->in_out_params, sp->in_out_params, sizeof(sp->in_out_params) );


    //return back to VfT_PROG slab
    CASM_FUNCCALL(_geec_sentinel_xfer_ret_vft_prog_to_uvt_uvu_prog,
                      elem.caller_stack_frame);


    _XDPRINTF_("%s[%u]: wip. halting!\n", __func__, (u16)sp->cpuid);
    HALT();

}




static void _geec_sentinel_transition_call_uvt_uvu_prog_to_vft_prog(slab_params_t *sp, void *caller_stack_frame){
    slab_params_t *dst_sp;

    _XDPRINTF_("%s[%u]: src=%u, dst=%u\n", __func__, (u16)sp->cpuid, sp->src_slabid, sp->dst_slabid);

    //save caller stack frame address (esp)
    _XDPRINTF_("%s[%u]: src tos before=%x\n", __func__, (u16)sp->cpuid, _xmhfhic_common_slab_info_table[sp->src_slabid].slabtos[(u16)sp->cpuid]);
    _xmhfhic_common_slab_info_table[sp->src_slabid].slabtos[(u16)sp->cpuid] =
        (u32)caller_stack_frame;
    _XDPRINTF_("%s[%u]: src tos after=%x\n", __func__, (u16)sp->cpuid, _xmhfhic_common_slab_info_table[sp->src_slabid].slabtos[(u16)sp->cpuid]);


    //make space on destination slab stack for slab_params_t and copy parameters
    {
        _XDPRINTF_("%s[%u]: dst tos before=%x\n", __func__, (u16)sp->cpuid, _xmhfhic_common_slab_info_table[sp->dst_slabid].slabtos[(u16)sp->cpuid]);
        _xmhfhic_common_slab_info_table[sp->dst_slabid].slabtos[(u16)sp->cpuid] -= sizeof(slab_params_t);
        _XDPRINTF_("%s[%u]: dst tos after=%x\n", __func__, (u16)sp->cpuid, _xmhfhic_common_slab_info_table[sp->dst_slabid].slabtos[(u16)sp->cpuid]);
        dst_sp = (slab_params_t *) _xmhfhic_common_slab_info_table[sp->dst_slabid].slabtos[(u16)sp->cpuid];
        _XDPRINTF_("%s[%u]: copying params to dst_sp=%x from sp=%x\n", __func__, (u16)sp->cpuid,
                   (u32)dst_sp, (u32)sp);
        memcpy(dst_sp, sp, sizeof(slab_params_t));
    }


    //push src_slabid, dst_slabid, hic_calltype, caller_stack_frame and sp
    //tuple to safe stack
    _XDPRINTF_("%s[%u]: safepush: {cpuid: %u, src: %u, dst: %u, ctype: 0x%x, \
               csf=0x%x, sp=0x%x \n",
            __func__, (u16)sp->cpuid,
               (u16)sp->cpuid, sp->src_slabid, sp->dst_slabid, sp->slab_ctype,
               caller_stack_frame, sp);

    __xmhfhic_safepush((u16)sp->cpuid, sp->src_slabid, sp->dst_slabid,
                       sp->slab_ctype, caller_stack_frame, sp);


    _XDPRINTF_("%s[%u]: entry=%x, dst_sp=%x, proceeding to xfer...\n", __func__,
               (u16)sp->cpuid, _xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub, (u32)dst_sp);


    CASM_FUNCCALL(_geec_sentinel_xfer_call_uvt_uvu_prog_to_vft_prog,
                _xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub,
                                  dst_sp);


    _XDPRINTF_("%s[%u]: wip. halting!\n", __func__, (u16)sp->cpuid);
    HALT();
}




static void _geec_sentinel_transition_ret_uvt_uvu_prog_to_vft_prog(slab_params_t *sp, void *caller_stack_frame){
    slab_params_t *dst_sp;
    __xmhfhic_safestack_element_t elem;

    _XDPRINTF_("%s[%u]: src=%u, dst=%u\n", __func__, (u16)sp->cpuid, sp->src_slabid, sp->dst_slabid);

    //pop tuple from safe stack
    __xmhfhic_safepop((u16)sp->cpuid, &elem.src_slabid, &elem.dst_slabid, &elem.hic_calltype, &elem.caller_stack_frame,
                        &elem.sp);

    _XDPRINTF_("%s[%u]: safepop: {cpuid: %u, src: %u, dst: %u, ctype: 0x%x, \
               csf=0x%x, sp=0x%x \n",
            __func__, (u16)sp->cpuid,
               (u16)sp->cpuid, elem.src_slabid, elem.dst_slabid, elem.hic_calltype,
               elem.caller_stack_frame, elem.sp);

    //check to ensure this return is paired with a prior call
    if ( !((elem.src_slabid == sp->dst_slabid) && (elem.dst_slabid == sp->src_slabid) &&
           (elem.hic_calltype == XMHFGEEC_SENTINEL_CALL_uVT_uVU_PROG_TO_VfT_PROG)) ){
        _XDPRINTF_("%s[ln:%u]: Fatal: ret does not match prior call. Halting!\n",
            __func__, __LINE__);
        HALT();
    }

    //marshall parameters
    memcpy( (elem.sp)->in_out_params, sp->in_out_params, sizeof(sp->in_out_params) );


    //return back to uVT/uVU_PROG slab
    CASM_FUNCCALL(_geec_sentinel_xfer_ret_uvt_uvu_prog_to_vft_prog,
                      elem.caller_stack_frame);


    _XDPRINTF_("%s[%u]: wip. halting!\n", __func__, (u16)sp->cpuid);
    HALT();
}




/////
// sentinel hub
/////

static inline void _geec_sentinel_checkandhalt_callcaps(u32 src_slabid, u32 dst_slabid, u32 dst_uapifn){
    //check call capabilities
    if( !(_xmhfhic_common_slab_info_table[dst_slabid].slab_callcaps & XMHFGEEC_SLAB_CALLCAP_MASK(src_slabid)) ){
        _XDPRINTF_("GEEC_SENTINEL: Halt!. callcap check failed for src(%u)-->dst(%u), dst caps=0x%x\n",
                   src_slabid, dst_slabid, _xmhfhic_common_slab_info_table[dst_slabid].slab_callcaps);
        HALT();
    }

    //check uapi capabilities
    if( _xmhfhic_common_slab_info_table[dst_slabid].slab_uapisupported){
        if(!(_xmhfhic_common_slab_info_table[src_slabid].slab_uapicaps[dst_slabid] & XMHFGEEC_SLAB_UAPICAP_MASK(dst_uapifn)))
        {
            _XDPRINTF_("GEEC_SENTINEL: Halt!. uapicap check failed for src(%u)-->dst(%u), dst_uapifn=%u, dst_uapimask=0x%08x\n",
                       src_slabid, dst_slabid, dst_uapifn,
                       (u32)_xmhfhic_common_slab_info_table[src_slabid].slab_uapicaps[dst_slabid]);
            HALT();
        }
    }
}



void geec_sentinel_main(slab_params_t *sp, void *caller_stack_frame){



    switch(sp->slab_ctype){
        case XMHFGEEC_SENTINEL_CALL_FROM_VfT_PROG:{

            switch (_xmhfhic_common_slab_info_table[sp->dst_slabid].slabtype){

                case XMHFGEEC_SLABTYPE_VfT_PROG:{
                    _geec_sentinel_checkandhalt_callcaps(sp->src_slabid, sp->dst_slabid, sp->dst_uapifn);
                    CASM_FUNCCALL(_geec_sentinel_xfer_vft_prog_to_vft_prog,
                                  _xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub,
                                  caller_stack_frame);
                    _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n",
                               __LINE__);
                    HALT();

                }
                break;


                case XMHFGEEC_SLABTYPE_uVT_PROG:
                case XMHFGEEC_SLABTYPE_uVU_PROG:{
                    _geec_sentinel_checkandhalt_callcaps(sp->src_slabid, sp->dst_slabid, sp->dst_uapifn);
                    sp->slab_ctype = XMHFGEEC_SENTINEL_CALL_VfT_PROG_TO_uVT_uVU_PROG;
                    _geec_sentinel_transition_vft_prog_to_uvt_uvu_prog(sp, caller_stack_frame);
                    _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n",
                               __LINE__);
                    HALT();

                }
                break;


                case XMHFGEEC_SLABTYPE_uVT_PROG_GUEST:
                case XMHFGEEC_SLABTYPE_uVU_PROG_GUEST:
                case XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST:{
                    u32 errorcode;
                    _geec_sentinel_checkandhalt_callcaps(sp->src_slabid, sp->dst_slabid, sp->dst_uapifn);
                    sp->slab_ctype = XMHFGEEC_SENTINEL_CALL_VfT_PROG_TO_uVT_uVU_PROG_GUEST;
                    CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VPID, sp->dst_slabid );
                    CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_FULL, (_xmhfhic_common_slab_info_table[sp->dst_slabid].mempgtbl_cr3  | 0x1E) );
                    CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_HIGH, 0);
                    CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RSP, _xmhfhic_common_slab_info_table[sp->dst_slabid].slabtos[(u16)sp->cpuid]);
                    CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RIP, _xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub);

                    errorcode = CASM_FUNCCALL(_geec_sentinel_xfer_vft_prog_to_uvt_uvu_prog_guest, CASM_NOPARAM);

                    switch(errorcode){
                        case 0:	//no error code, VMCS pointer is invalid
                            _XDPRINTF_("GEEC_SENTINEL: VMLAUNCH error; VMCS pointer invalid?\n");
                            break;
                        case 1:{//error code available, so dump it
                            u32 code=xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMINSTR_ERROR);
                            _XDPRINTF_("GEEC_SENTINEL: VMLAUNCH error; code=%x\n", code);
                            break;
                        }
                    }

                    HALT();

                }
                break;

                default:
                    _XDPRINTF_("GEEC_SENTINEL(ln:%u): Unrecognized transition. Halting!\n", __LINE__);
                    HALT();
            }


        }
        break;




        case XMHFGEEC_SENTINEL_RET_VfT_PROG_TO_uVT_uVU_PROG:{
                    _geec_sentinel_transition_ret_vft_prog_to_uvt_uvu_prog(sp, caller_stack_frame);
                    _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n",
                               __LINE__);
                    HALT();
        }
        break;





        case XMHFGEEC_SENTINEL_CALL_uVT_uVU_PROG_TO_VfT_PROG:{
            _geec_sentinel_checkandhalt_callcaps(sp->src_slabid, sp->dst_slabid, sp->dst_uapifn);
            _geec_sentinel_transition_call_uvt_uvu_prog_to_vft_prog(sp, caller_stack_frame);
            _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n", __LINE__);
            HALT();
        }
        break;




        case XMHFGEEC_SENTINEL_RET_uVT_uVU_PROG_TO_VfT_PROG:{
            _geec_sentinel_transition_ret_uvt_uvu_prog_to_vft_prog(sp, caller_stack_frame);
            _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n", __LINE__);
            HALT();
        }
        break;



        case XMHFGEEC_SENTINEL_CALL_EXCEPTION:{
            if(!(_xmhfhic_common_slab_info_table[sp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG)){
                _XDPRINTF_("GEEC_SENTINEL(ln:%u): exception target slab not VfT_PROG. Halting!\n", __LINE__);
                HALT();
            }

            CASM_FUNCCALL(_geec_sentinel_xfer_exception_to_vft_prog,
              _xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub,
              caller_stack_frame);
            _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n",
                       __LINE__);
            HALT();

        }
        break;






        case XMHFGEEC_SENTINEL_RET_EXCEPTION:{
            if(!
               (_xmhfhic_common_slab_info_table[sp->src_slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG &&
                sp->dst_slabid == XMHFGEEC_SLAB_GEEC_SENTINEL)){
                _XDPRINTF_("GEEC_SENTINEL(ln:%u): exception ret source slab not VfT_PROG_EXCEPTION. Halting!\n", __LINE__);
                HALT();
            }

            //_geec_sentinel_dump_exframe(sp->in_out_params);

            CASM_FUNCCALL(_geec_sentinel_xfer_ret_from_exception,
                sp->in_out_params);
            _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n",
                       __LINE__);
            HALT();

        }
        break;







        case XMHFGEEC_SENTINEL_CALL_INTERCEPT:{
            if(!(_xmhfhic_common_slab_info_table[sp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG)){
                _XDPRINTF_("GEEC_SENTINEL(ln:%u): intercept target slab not VfT_PROG_INTERCEPT. Halting!\n", __LINE__);
                HALT();
            }

            CASM_FUNCCALL(_geec_sentinel_xfer_intercept_to_vft_prog,
              _xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub,
              caller_stack_frame);
            _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n",
                       __LINE__);
            HALT();

        }
        break;






        case XMHFGEEC_SENTINEL_RET_INTERCEPT:{
            if(!
               (_xmhfhic_common_slab_info_table[sp->src_slabid].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG &&
                (_xmhfhic_common_slab_info_table[sp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST ||
                 _xmhfhic_common_slab_info_table[sp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST ||
                 _xmhfhic_common_slab_info_table[sp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST
                )
               )){
                _XDPRINTF_("GEEC_SENTINEL(ln:%u): intercept ret source slab not VfT_PROG_INTERCEPT. Halting!\n", __LINE__);
                HALT();
            }

            CASM_FUNCCALL(_geec_sentinel_xfer_ret_from_intercept, sp->in_out_params);
            _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n",
                       __LINE__);
            HALT();

        }
        break;






        default:
            _XDPRINTF_("GEEC_SENTINEL: unkown call type %x. Halting!\n", sp->slab_ctype);
            HALT();

    }

}


