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
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_exhub.h>


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

void xcexhub_entryexcp(x86vmx_exception_frame_t *exframe){
    slab_params_t spl;

    uberspark_uobjrtl_crt__memset(&spl, 0, sizeof(spl));

    spl.slab_ctype = XMHFGEEC_SENTINEL_CALL_EXCEPTION;
    spl.src_slabid = XMHFGEEC_SLAB_GEEC_SENTINEL; //XXX: TODO: grab src_slabid based on exframe->orig_rip
    spl.dst_slabid = XMHFGEEC_SLAB_XC_EXHUB;
    spl.dst_uapifn = 0;
    spl.cpuid = xmhf_baseplatform_arch_x86_getcpulapicid();
    memcpy(&spl.in_out_params[0], exframe,
           sizeof(x86vmx_exception_frame_t));

    //invoke exception processing
    xcexhub_excpmain(&spl);

    //return from exception
    CASM_FUNCCALL(xcexhub_retexcp,
        &spl.in_out_params[0]);
    _XDPRINTF_("GEEC_SENTINEL[ln:%u]: halting. should never be here!\n",
               __LINE__);
    HALT();
}

