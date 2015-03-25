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

#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfhw.h>
#include <xmhf-debug.h>


//__attribute__((naked)) bool __vmx_vmxon(u64 vmxonregion_paddr)
CASM_FUNCDEF(bool, __vmx_vmxon,
{
    xmhfhwm_cpu_insn_vmxon_mesp(0x4);
	xmhfhwm_cpu_insn_jbe(vo_fail);
    xmhfhwm_cpu_insn_movl_imm_eax(0x1);
	xmhfhwm_cpu_insn_jmp(vo_success);
    CASM_LABEL(vo_fail);
    xmhfhwm_cpu_insn_movl_imm_eax(0x0);
	CASM_LABEL(vo_success);
    xmhfhwm_cpu_insn_ret();
},
u64 vmxonregion_paddr)


//__attribute__((naked)) void xmhfhw_cpu_x86vmx_vmwrite(u32 encoding, u32 value)
CASM_FUNCDEF(void, xmhfhw_cpu_x86vmx_vmwrite,
{
  xmhfhwm_cpu_insn_movl_mesp_ecx(0x4);
  xmhfhwm_cpu_insn_movl_mesp_eax(0x8);
  xmhfhwm_cpu_insn_vmwrite_eax_ecx();
  xmhfhwm_cpu_insn_ret();
},
u32 encoding,
u32 value)


//__attribute__((naked)) u32 xmhfhw_cpu_x86vmx_vmread(u32 encoding)
CASM_FUNCDEF(u32, xmhfhw_cpu_x86vmx_vmread,
{
    xmhfhwm_cpu_insn_movl_mesp_ecx(0x4);
    xmhfhwm_cpu_insn_vmread_ecx_eax();
    xmhfhwm_cpu_insn_ret();
},
u32 encoding)


//__attribute__((naked)) u32 __vmx_vmclear(u64 vmcs)
CASM_FUNCDEF(u32, __vmx_vmclear,
{
    xmhfhwm_cpu_insn_vmclear_mesp(0x4);
    xmhfhwm_cpu_insn_jbe(vmclear_error);
    xmhfhwm_cpu_insn_movl_imm_eax(0x1);
    xmhfhwm_cpu_insn_jmp(vmclear_done);
    CASM_LABEL(vmclear_error);
    xmhfhwm_cpu_insn_movl_imm_eax(0x0);
    CASM_LABEL(vmclear_done);
    xmhfhwm_cpu_insn_ret();
},
u64 vmcs)


//__attribute__((naked)) u32 __vmx_vmptrld(u64 vmcs)
CASM_FUNCDEF(u32, __vmx_vmptrld,
{
    xmhfhwm_cpu_insn_vmptrld_mesp(0x4);
    xmhfhwm_cpu_insn_jbe(vptrld_error);
    xmhfhwm_cpu_insn_movl_imm_eax(0x1);
    xmhfhwm_cpu_insn_jmp(vptrld_done);
    CASM_LABEL(vptrld_error);
    xmhfhwm_cpu_insn_movl_imm_eax(0x0);
    CASM_LABEL(vptrld_done);
    xmhfhwm_cpu_insn_ret();
},
u64 vmcs)


// VMX instruction INVVPID
//		Invalidate Translations Based on VPID
// INVVPID r32, m128
//returns 1 on success, 0 on failure
//__attribute__((naked)) u32 __vmx_invvpid(int invalidation_type, //0x14
//                  u32 vpid,              //0x18
//                  u32 linearaddress){    //0x1C
CASM_FUNCDEF(u32, __vmx_invvpid,
{
    xmhfhwm_cpu_insn_subl_imm_esp(0x10);

    xmhfhwm_cpu_insn_xorl_eax_eax();
    xmhfhwm_cpu_insn_movw_mesp_ax(0x18);
    xmhfhwm_cpu_insn_movl_eax_mesp(0x0);
    xmhfhwm_cpu_insn_movl_imm_mesp(0x0,0x4);
    xmhfhwm_cpu_insn_movl_mesp_eax(0x1C);
    xmhfhwm_cpu_insn_movl_eax_mesp(0x8);
    xmhfhwm_cpu_insn_movl_imm_mesp(0x0, 0xC);

    xmhfhwm_cpu_insn_movl_mesp_ecx(0x14);

    xmhfhwm_cpu_insn_invvpid_mesp_ecx(0x0);

    xmhfhwm_cpu_insn_movl_imm_eax(0x1);
    xmhfhwm_cpu_insn_ja(vinvpid_success);
    xmhfhwm_cpu_insn_movl_imm_eax(0x0);
    CASM_LABEL(vinvpid_success);

    xmhfhwm_cpu_insn_addl_imm_esp(0x10);
    xmhfhwm_cpu_insn_ret();
},
int invalidation_type,
u32 vpid,
u32 linearaddress)



// VMX instruction INVEPT
//		Invalidate Translations Derived from EPT
//__attribute__((naked)) void __vmx_invept(u64 invalidation_type, u64 eptp)
CASM_FUNCDEF(void, __vmx_invept,
{
    xmhfhwm_cpu_insn_subl_imm_esp(0x10);
    xmhfhwm_cpu_insn_movl_mesp_edx(0x14);
    xmhfhwm_cpu_insn_movl_mesp_eax(0x1C);
    xmhfhwm_cpu_insn_movl_eax_mesp(0x0);
    xmhfhwm_cpu_insn_movl_mesp_eax(0x20);
    xmhfhwm_cpu_insn_movl_eax_mesp(0x4);
    xmhfhwm_cpu_insn_movl_imm_mesp(0x0,0x8);
    xmhfhwm_cpu_insn_movl_imm_mesp(0x0,0xC);
    xmhfhwm_cpu_insn_invept_mesp_edx(0x0);
    xmhfhwm_cpu_insn_addl_imm_esp(0x10);
    xmhfhwm_cpu_insn_ret();
},
u64 invalidation_type,
u64 eptp)

