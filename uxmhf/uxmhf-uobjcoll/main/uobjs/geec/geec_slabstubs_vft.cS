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
 * slab stubs for program slabs
 * author: amit vasudevan (amitvasudevan@acm.org)
*/


#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>

#define xmhfhwm_cpu_insn_jmpxsentinel() \
	__builtin_annot("movl $0x06200000, %eax"); \
	__builtin_annot("jmpl *%eax "); \
	__builtin_annot("hlt "); \
	xmhfhwm_vdriver_sentinel(); \
	_impl_xmhfhwm_cpu_insn_hlt(); \


CASM_FUNCDEF_FULL(.slab_entrystub, 1, void, _slab_entrystub,
{
	xmhfhwm_cpu_insn_pushl_mesp(0x4); //push slab_params_t *
	xmhfhwm_cpu_insn_call_c_1p(slab_main, slab_params_t *);
	xmhfhwm_cpu_insn_addl_imm_esp(0x4); //remove slab_params_t *

	xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
	xmhfhwm_cpu_insn_cmpl_imm_meax(XMHFGEEC_SENTINEL_CALL_uVT_uVU_PROG_TO_VfT_PROG,0x0);
	xmhfhwm_cpu_insn_je(call_uvt_uvu_prog_to_vft_prog);
	xmhfhwm_cpu_insn_cmpl_imm_meax(XMHFGEEC_SENTINEL_CALL_EXCEPTION,0x0);
	xmhfhwm_cpu_insn_je(call_exception);
	xmhfhwm_cpu_insn_cmpl_imm_meax(XMHFGEEC_SENTINEL_CALL_INTERCEPT,0x0);
	xmhfhwm_cpu_insn_je(call_intercept);
	xmhfhwm_cpu_insn_jmplabel(call_vft_to_vft_prog);


	CASM_LABEL(call_uvt_uvu_prog_to_vft_prog)
	xmhfhwm_cpu_insn_movl_imm_meax(XMHFGEEC_SENTINEL_RET_uVT_uVU_PROG_TO_VfT_PROG, 0x0);
	xmhfhwm_cpu_insn_movl_meax_edx(0x4); //edx = src_slabid
	xmhfhwm_cpu_insn_movl_meax_ecx(0x8); //ecx = dst_slabid
	xmhfhwm_cpu_insn_movl_ecx_meax(0x4); //[eax+4] = src_slabid = dst_slabid
	xmhfhwm_cpu_insn_movl_edx_meax(0x8); //[eax+8] = dst_slabid = src_slabid
	xmhfhwm_cpu_insn_jmpxsentinel(); // xfer control to sentinel


	CASM_LABEL(call_exception)
	xmhfhwm_cpu_insn_movl_imm_meax(XMHFGEEC_SENTINEL_RET_EXCEPTION, 0x0);
	xmhfhwm_cpu_insn_movl_meax_edx(0x4); //edx = src_slabid
	xmhfhwm_cpu_insn_movl_meax_ecx(0x8); //ecx = dst_slabid
	xmhfhwm_cpu_insn_movl_ecx_meax(0x4); //[eax+4] = src_slabid = dst_slabid
	xmhfhwm_cpu_insn_movl_edx_meax(0x8); //[eax+8] = dst_slabid = src_slabid
	xmhfhwm_cpu_insn_jmpxsentinel(); // xfer control to sentinel


	CASM_LABEL(call_intercept)
	xmhfhwm_cpu_insn_movl_imm_meax(XMHFGEEC_SENTINEL_RET_INTERCEPT, 0x0);
	xmhfhwm_cpu_insn_movl_meax_edx(0x4); //edx = src_slabid
	xmhfhwm_cpu_insn_movl_meax_ecx(0x8); //ecx = dst_slabid
	xmhfhwm_cpu_insn_movl_ecx_meax(0x4); //[eax+4] = src_slabid = dst_slabid
	xmhfhwm_cpu_insn_movl_edx_meax(0x8); //[eax+8] = dst_slabid = src_slabid
	xmhfhwm_cpu_insn_jmpxsentinel(); // xfer control to sentinel


	CASM_LABEL(call_vft_to_vft_prog)
	xmhfhwm_cpu_insn_ret();
	xmhfhwm_cpu_insn_hlt();

},
slab_params_t *sp)

CASM_FUNCDEF(void, __slab_callsentinel,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_movl_imm_meax(XMHFGEEC_SENTINEL_CALL_FROM_VfT_PROG, 0x0);
    xmhfhwm_cpu_insn_jmpxsentinel();
},
slab_params_t *sp)

