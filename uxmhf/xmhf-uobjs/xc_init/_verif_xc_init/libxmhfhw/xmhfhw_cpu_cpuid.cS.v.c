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

//author: amit vasudevan (amitvasudevan@acm.org)

#include <uberspark.h>
#include <xmhfhw.h>


CASM_FUNCDEF(void, xmhfhw_cpu_cpuid,
{
    xmhfhwm_cpu_insn_pushl_esi();
    xmhfhwm_cpu_insn_pushl_ebx();

    xmhfhwm_cpu_insn_movl_mesp_eax(0xc); //eax = op
    xmhfhwm_cpu_insn_movl_mesp_ecx(0x18);
    xmhfhwm_cpu_insn_movl_mecx_ecx(0x0);

    xmhfhwm_cpu_insn_cpuid();

    xmhfhwm_cpu_insn_movl_mesp_esi(0x14);
    xmhfhwm_cpu_insn_movl_ebx_mesi(0x0);
    xmhfhwm_cpu_insn_movl_mesp_esi(0x18);
    xmhfhwm_cpu_insn_movl_ecx_mesi(0x0);
    xmhfhwm_cpu_insn_movl_eax_ecx();
    xmhfhwm_cpu_insn_movl_mesp_esi(0x10);
    xmhfhwm_cpu_insn_movl_ecx_mesi(0x0);
    xmhfhwm_cpu_insn_movl_edx_ecx();
    xmhfhwm_cpu_insn_movl_mesp_esi(0x1c);
    xmhfhwm_cpu_insn_movl_ecx_mesi(0x0);

    xmhfhwm_cpu_insn_popl_ebx();
    xmhfhwm_cpu_insn_popl_esi();
    xmhfhwm_cpu_insn_ret();
},
uint32_t op,
uint32_t *eax,
uint32_t *ebx,
uint32_t *ecx,
uint32_t *edx)


