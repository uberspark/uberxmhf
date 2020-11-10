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

//xmhfhw_cpu_vmx: CPU VMX functions
//author: amit vasudevan (amitvasudevan@acm.org)

#include <uberspark.h>
#include <xmhfhw.h>



// VMX instruction INVEPT
//		Invalidate Translations Derived from EPT
//__attribute__((naked)) void __vmx_invept(uint64_t invalidation_type, uint64_t eptp)
CASM_FUNCDEF(uint32_t, __vmx_invept,
{
    xmhfhwm_cpu_insn_subl_imm_esp(0x10);
    xmhfhwm_cpu_insn_movl_mesp_edx(0x14);	//edx = invalidation_type_lo
    xmhfhwm_cpu_insn_movl_mesp_eax(0x1C);	//eax = eptp_lo
    xmhfhwm_cpu_insn_movl_eax_mesp(0x0);	//invept desc[0..31bits] = eptp_lo
    xmhfhwm_cpu_insn_movl_mesp_eax(0x20);	//eax = eptp_hi
    xmhfhwm_cpu_insn_movl_eax_mesp(0x4);	//invept desc[32..64bits] = eptp_hi
    xmhfhwm_cpu_insn_movl_imm_mesp(0x0,0x8);	//invept desc [64-127bits] = 0
    xmhfhwm_cpu_insn_movl_imm_mesp(0x0,0xC);
    xmhfhwm_cpu_insn_invept_mesp_edx(0x0);
    xmhfhwm_cpu_insn_jc(__insnfail);
    xmhfhwm_cpu_insn_jz(__insnfail);
    xmhfhwm_cpu_insn_xorl_eax_eax();		//return 0 as we succeeded
    xmhfhwm_cpu_insn_jmplabel(__epilogue);

CASM_LABEL(__insnfail);
    xmhfhwm_cpu_insn_movl_imm_eax(0x1);		//return 1 for failure

CASM_LABEL(__epilogue);
    xmhfhwm_cpu_insn_addl_imm_esp(0x10);
    xmhfhwm_cpu_insn_retu32();
},
uint32_t invalidation_type_lo,
uint32_t invalidation_type_hi,
uint32_t eptp_lo,
uint32_t eptp_hi)

