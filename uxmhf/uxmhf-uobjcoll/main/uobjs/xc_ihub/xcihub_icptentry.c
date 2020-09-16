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
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_ihub.h>


////// intercepts

void xcihub_entry_icpt(x86regs_t *r){
    slab_params_t spl;
    uint32_t eflags;

    eflags = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_eflags,CASM_NOPARAM);
    eflags &= ~(EFLAGS_IOPL); //clear out IOPL bits
    eflags |= EFLAGS_IOPL;
    CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__write_eflags,eflags);

    uberspark_uobjrtl_crt__memset(&spl, 0, sizeof(spl));

    spl.slab_ctype = XMHFGEEC_SENTINEL_CALL_INTERCEPT;
    spl.src_slabid = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmread,VMCS_CONTROL_VPID);
    spl.dst_slabid = XMHFGEEC_SLAB_XC_IHUB;
    spl.cpuid = uberspark_uobjrtl_hw__generic_x86_32_intel__getcpulapicid();

    uberspark_uobjrtl_crt__memcpy(&spl.in_out_params[0], r, sizeof(x86regs_t));

    //invoke processing of intercept
    xcihub_icptmain(&spl);

    //exit to guest
    CASM_FUNCCALL(xcihub_reticpt, &spl.in_out_params[0]);
    _XDPRINTF_("XC_IHUB[ln:%u]: halting. should never be here!\n",
               __LINE__);
    HALT();
}

