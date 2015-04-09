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

#include <xmhf.h>
#include <xmhf-hic.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>
#include <geec_primesmp.h>

// GEEC prime SMP assembly language code blobs
// author: amit vasudevan (amitvasudevan@acm.org)

//__attribute__((naked)) void _ap_bootstrap_code(void) {
CASM_FUNCDEF(void, _ap_bootstrap_code,
{
    xmhfhwm_cpu_insn_movw_imm_ax(__DS_CPL0);
    xmhfhwm_cpu_insn_movw_ax_ds();
    xmhfhwm_cpu_insn_movl_imm_eax(((X86SMP_APBOOTSTRAP_DATASEG << 4) + 8));
    xmhfhwm_cpu_insn_movl_meax_eax(0x0);
    xmhfhwm_cpu_insn_movl_imm_ebx(((X86SMP_APBOOTSTRAP_DATASEG << 4) + 0));
    xmhfhwm_cpu_insn_movl_mebx_ebx(0x0);
    xmhfhwm_cpu_insn_movl_imm_edi(((X86SMP_APBOOTSTRAP_DATASEG << 4) + 32))
    xmhfhwm_cpu_insn_movl_medi_edi(0x0);
    xmhfhwm_cpu_insn_jmpl_eax();
    xmhfhwm_cpu_insn_hlt();
    CASM_BALIGN(4096);
},
void *noparam)


//bool __xmhfhic_ap_entry(void) __attribute__((naked)){
CASM_FUNCDEF(bool, __xmhfhic_ap_entry,
{
    xmhfhwm_cpu_insn_movw_ds_ax();
    xmhfhwm_cpu_insn_movw_ax_es();
    xmhfhwm_cpu_insn_movw_ax_fs();
    xmhfhwm_cpu_insn_movw_ax_gs();
    xmhfhwm_cpu_insn_movw_ax_ss();

    xmhfhwm_cpu_insn_movl_cr4_eax();
    xmhfhwm_cpu_insn_orl_imm_eax(0x00000030);
    xmhfhwm_cpu_insn_movl_eax_cr4();

    xmhfhwm_cpu_insn_movl_ebx_cr3();

    xmhfhwm_cpu_insn_movl_imm_ecx(0xc0000080);
    xmhfhwm_cpu_insn_rdmsr();
    xmhfhwm_cpu_insn_orl_imm_eax(0x00000800);
    xmhfhwm_cpu_insn_wrmsr();

    xmhfhwm_cpu_insn_movl_cr0_eax();
    xmhfhwm_cpu_insn_orl_imm_eax(0x80000015);
    xmhfhwm_cpu_insn_movl_eax_cr0();

    //TODO: for non-TXT wakeup we need to reload GDT
    //"movl %1, %esi \r\n");
    //"lgdt (%esi) \r\n");

    xmhfhwm_cpu_insn_movl_imm_ecx(0x0000001B);
    xmhfhwm_cpu_insn_rdmsr();
    xmhfhwm_cpu_insn_andl_imm_ecx(0x00000FFF);
    xmhfhwm_cpu_insn_orl_imm_eax(0xFEE00000);
    xmhfhwm_cpu_insn_wrmsr();

    xmhfhwm_cpu_insn_xorl_eax_eax();
    xmhfhwm_cpu_insn_movl_imm_eax(0xFEE00020);
    xmhfhwm_cpu_insn_movl_meax_eax(0x0);
    xmhfhwm_cpu_insn_shr_imm_eax(24);

    xmhfhwm_cpu_insn_xorl_ebx_ebx();
    xmhfhwm_cpu_insn_movl_edi_ebx();

    xmhfhwm_cpu_insn_movl_mebxeax_eax(4);

    xmhfhwm_cpu_insn_movl_imm_ecx(16384);
    xmhfhwm_cpu_insn_mull_ecx();
    xmhfhwm_cpu_insn_addl_ecx_eax();
    xmhfhwm_cpu_insn_addl_imm_eax(_init_cpustacks);
    xmhfhwm_cpu_insn_movl_eax_esp();

    xmhfhwm_cpu_insn_jmp(__xmhfhic_smp_cpu_x86_smpinitialize_commonstart);
},
void *noparam)



//////////////////////////////////////////////////////////////////////////////
// setup cpu state for hic

//__attribute__((naked)) void __xmhfhic_x86vmx_reloadCS(u32 cs_sel)
CASM_FUNCDEF(void, __xmhfhic_x86vmx_reloadCS,
{
    xmhfhwm_cpu_insn_popl_eax();
    xmhfhwm_cpu_insn_pushl_mesp(0x0);
    xmhfhwm_cpu_insn_pushl_eax();
    xmhfhwm_cpu_insn_lret();
},
u32 cs_sel)

//__attribute__((naked)) void __xmhfhic_x86vmx_reloadsegregs(u32 ds_sel){
CASM_FUNCDEF(void, __xmhfhic_x86vmx_reloadsegregs,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_movw_ax_ds();
    xmhfhwm_cpu_insn_movw_ax_es();
    xmhfhwm_cpu_insn_movw_ax_fs();
    xmhfhwm_cpu_insn_movw_ax_gs();
    xmhfhwm_cpu_insn_movw_ax_ss();
    xmhfhwm_cpu_insn_ret();
},
u32 ds_sel)















