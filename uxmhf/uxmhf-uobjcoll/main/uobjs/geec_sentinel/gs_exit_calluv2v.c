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
#include <uberspark/include/uberspark.h>
/*
 * HIC trampoline and stubs
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_sentinel.h>


void gs_exit_calluv2v(slab_params_t *sp, void *caller_stack_frame){
    slab_params_t *dst_sp;
	gs_siss_element_t siss_elem;

    _XDPRINTF_("%s[%u]: src=%u, dst=%u\n", __func__, (uint16_t)sp->cpuid, sp->src_slabid, sp->dst_slabid);

    //save caller stack frame address (esp)
    _XDPRINTF_("%s[%u]: src tos before=%x\n", __func__, (uint16_t)sp->cpuid, xmhfgeec_slab_info_table[sp->src_slabid].slabtos[(uint16_t)sp->cpuid]);
    xmhfgeec_slab_info_table[sp->src_slabid].slabtos[(uint16_t)sp->cpuid] =
        (uint32_t)caller_stack_frame;
    _XDPRINTF_("%s[%u]: src tos after=%x\n", __func__, (uint16_t)sp->cpuid, xmhfgeec_slab_info_table[sp->src_slabid].slabtos[(uint16_t)sp->cpuid]);


    //make space on destination slab stack for slab_params_t and copy parameters
    {
        _XDPRINTF_("%s[%u]: dst tos before=%x\n", __func__, (uint16_t)sp->cpuid, xmhfgeec_slab_info_table[sp->dst_slabid].slabtos[(uint16_t)sp->cpuid]);
        xmhfgeec_slab_info_table[sp->dst_slabid].slabtos[(uint16_t)sp->cpuid] -= sizeof(slab_params_t);
        _XDPRINTF_("%s[%u]: dst tos after=%x\n", __func__, (uint16_t)sp->cpuid, xmhfgeec_slab_info_table[sp->dst_slabid].slabtos[(uint16_t)sp->cpuid]);
        dst_sp = (slab_params_t *) xmhfgeec_slab_info_table[sp->dst_slabid].slabtos[(uint16_t)sp->cpuid];
        _XDPRINTF_("%s[%u]: copying params to dst_sp=%x from sp=%x\n", __func__, (uint16_t)sp->cpuid,
                   (uint32_t)dst_sp, (uint32_t)sp);

        CASM_FUNCCALL(xmhfhw_sysmemaccess_copy, dst_sp, sp, sizeof(slab_params_t));
    }



    //push src_slabid, dst_slabid, hic_calltype, caller_stack_frame and sp
    //tuple to safe stack
    _XDPRINTF_("%s[%u]: safepush: {cpuid: %u, src: %u, dst: %u, ctype: 0x%x, \
               csf=0x%x, sp=0x%x \n",
            __func__, (uint16_t)sp->cpuid,
               (uint16_t)sp->cpuid, sp->src_slabid, sp->dst_slabid, sp->slab_ctype,
               caller_stack_frame, sp);

	siss_elem.src_slabid = sp->src_slabid;
	siss_elem.dst_slabid = sp->dst_slabid;
	siss_elem.slab_ctype = sp->slab_ctype;
	siss_elem.caller_stack_frame = caller_stack_frame;
	siss_elem.sp = sp;

    //gs_siss_push((uint16_t)sp->cpuid, sp->src_slabid, sp->dst_slabid,
    //                   sp->slab_ctype, caller_stack_frame, sp);
    gs_siss_push((uint16_t)sp->cpuid, siss_elem);


    _XDPRINTF_("%s[%u]: entry=%x, dst_sp=%x, proceeding to xfer...\n", __func__,
               (uint16_t)sp->cpuid, xmhfgeec_slab_info_table[sp->dst_slabid].entrystub, (uint32_t)dst_sp);


    CASM_FUNCCALL(gs_exit_calluv2vstub,
                xmhfgeec_slab_info_table[sp->dst_slabid].entrystub,
                                  dst_sp);


    _XDPRINTF_("%s[%u]: wip. halting!\n", __func__, (uint16_t)sp->cpuid);
    HALT();
}

