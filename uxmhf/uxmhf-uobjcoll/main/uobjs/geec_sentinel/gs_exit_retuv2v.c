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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
// #include <xmhfgeec.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_sentinel.h>



void gs_exit_retuv2v(slab_params_t *sp, void *caller_stack_frame){
    slab_params_t *dst_sp;
    gs_siss_element_t elem;


    _XDPRINTF_("%s[%u]: src=%u, dst=%u\n", __func__, (uint16_t)sp->cpuid, sp->src_slabid, sp->dst_slabid);

    //pop tuple from safe stack
    //gs_siss_pop((uint16_t)sp->cpuid, &elem.src_slabid, &elem.dst_slabid, &elem.slab_ctype, &elem.caller_stack_frame,
    //                    &elem.sp);
    gs_siss_pop((uint16_t)sp->cpuid, &elem);



    _XDPRINTF_("%s[%u]: safepop: {cpuid: %u, src: %u, dst: %u, ctype: 0x%x, \
               csf=0x%x, sp=0x%x \n",
            __func__, (uint16_t)sp->cpuid,
               (uint16_t)sp->cpuid, elem.src_slabid, elem.dst_slabid, elem.slab_ctype,
               elem.caller_stack_frame, elem.sp);

    //check to ensure this return is paired with a prior call
    if ( !((elem.src_slabid == sp->dst_slabid) && (elem.dst_slabid == sp->src_slabid) &&
           (elem.slab_ctype == XMHFGEEC_SENTINEL_CALL_uVT_uVU_PROG_TO_VfT_PROG)) ){
        _XDPRINTF_("%s[ln:%u]: Fatal: ret does not match prior call. Halting!\n",
            __func__, __LINE__);
        HALT();
    }


    //marshall parameters
    CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmemaccess_copy, (elem.sp)->in_out_params, sp->in_out_params, sizeof(sp->in_out_params));


    //return back to uVT/uVU_PROG slab
    CASM_FUNCCALL(gs_exit_retuv2vstub,
                      elem.caller_stack_frame);


    _XDPRINTF_("%s[%u]: wip. halting!\n", __func__, (uint16_t)sp->cpuid);
    HALT();
}



