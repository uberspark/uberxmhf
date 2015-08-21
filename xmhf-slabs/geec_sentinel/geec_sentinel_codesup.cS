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
 GEEC sentinel low-level support routines
 author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <geec_sentinel.h>

////
// support CASM functions used by the sentinel
/////


CASM_FUNCDEF(void, _geec_sentinel_xfer_vft_prog_to_vft_prog,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_movl_mesp_edx(0x8);
    xmhfhwm_cpu_insn_movl_edx_esp();
    xmhfhwm_cpu_insn_popl_ebx();
    xmhfhwm_cpu_insn_popl_esi();
    xmhfhwm_cpu_insn_popl_edi();
    xmhfhwm_cpu_insn_popl_ebp();
    xmhfhwm_cpu_insn_jmpl_eax();
    xmhfhwm_cpu_insn_hlt();
},
u32 entry_point, void *caller_stack_frame)



CASM_FUNCDEF(void, _geec_sentinel_xfer_exception_to_vft_prog,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_movl_mesp_edx(0x8);
    xmhfhwm_cpu_insn_movl_edx_esp();
    xmhfhwm_cpu_insn_pushl_esp();
    xmhfhwm_cpu_insn_pushl_imm(0x0);
    xmhfhwm_cpu_insn_jmpl_eax();
    xmhfhwm_cpu_insn_hlt();
},
u32 entry_point, void *caller_stack_frame)

CASM_FUNCDEF(void, _geec_sentinel_xfer_ret_from_exception,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);    //eax = exception frame
    xmhfhwm_cpu_insn_movl_meax_edi(0x0);
    xmhfhwm_cpu_insn_movl_meax_esi(0x4);
    xmhfhwm_cpu_insn_movl_meax_ebp(0x8);
    xmhfhwm_cpu_insn_movl_meax_esp(0xC);
    xmhfhwm_cpu_insn_movl_meax_ebx(0x10);
    xmhfhwm_cpu_insn_movl_meax_edx(0x14);
    xmhfhwm_cpu_insn_movl_meax_ecx(0x18);
    xmhfhwm_cpu_insn_movl_meax_eax(0x1C);
    xmhfhwm_cpu_insn_addl_imm_esp(0x8);
    xmhfhwm_cpu_insn_iretl();
},
x86vmx_exception_frame_t *exframe)


CASM_FUNCDEF(void, _geec_sentinel_xfer_intercept_to_vft_prog,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_movl_mesp_edx(0x8);
    xmhfhwm_cpu_insn_movl_edx_esp();
    xmhfhwm_cpu_insn_pushl_esp();
    xmhfhwm_cpu_insn_pushl_imm(0x0);
    xmhfhwm_cpu_insn_jmpl_eax();
    xmhfhwm_cpu_insn_hlt();
},
u32 entry_point, void *caller_stack_frame)


//if we return, we had an error and we return the
//corresponding error code
CASM_FUNCDEF(u32, _geec_sentinel_xfer_vft_prog_to_uvt_uvu_prog_guest,
{
    xmhfhwm_cpu_insn_vmlaunch();
    xmhfhwm_cpu_insn_jc(__vmx_start_hvm_failinvalid);
    xmhfhwm_cpu_insn_jnz(__vmx_start_hvm_undefinedimplementation);
    xmhfhwm_cpu_insn_movl_imm_eax(0x1);		//VMLAUNCH error, XXX: need to read from VM instruction error field in VMCS
    xmhfhwm_cpu_insn_jmp(__vmx_start_continue);
    CASM_LABEL(__vmx_start_hvm_undefinedimplementation);
    xmhfhwm_cpu_insn_movl_imm_eax(0x2);		//violation of VMLAUNCH specs., handle it anyways
    xmhfhwm_cpu_insn_jmp(__vmx_start_continue);
    CASM_LABEL(__vmx_start_hvm_failinvalid);
    xmhfhwm_cpu_insn_xorl_eax_eax();		//return 0 as we have no error code available
    CASM_LABEL(__vmx_start_continue);
    xmhfhwm_cpu_insn_ret();
},
void *noparam)




CASM_FUNCDEF(void, _geec_sentinel_xfer_ret_from_intercept,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_movl_meax_edi(0x0);
    xmhfhwm_cpu_insn_movl_meax_esi(0x4);
    xmhfhwm_cpu_insn_movl_meax_ebp(0x8);
    xmhfhwm_cpu_insn_movl_meax_esp(0xC);
    xmhfhwm_cpu_insn_movl_meax_ebx(0x10);
    xmhfhwm_cpu_insn_movl_meax_edx(0x14);
    xmhfhwm_cpu_insn_movl_meax_ecx(0x18);
    xmhfhwm_cpu_insn_movl_meax_eax(0x1C);
    xmhfhwm_cpu_insn_vmresume();
    xmhfhwm_cpu_insn_hlt();
},
x86regs_t *r)



CASM_FUNCDEF(void, _geec_sentinel_xfer_vft_prog_to_uvt_uvu_prog,
{
    xmhfhwm_cpu_insn_movl_mesp_edx(0x4);    //edx = entry_point
    xmhfhwm_cpu_insn_movl_mesp_ecx(0x8);    //edx = callee_stack_frame
    xmhfhwm_cpu_insn_sysexit();             //sysexit to ring-3
    xmhfhwm_cpu_insn_hlt();

    //xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    //xmhfhwm_cpu_insn_movl_mesp_edx(0x8);
    //xmhfhwm_cpu_insn_movl_edx_esp();
    //xmhfhwm_cpu_insn_jmpl_eax();
    //xmhfhwm_cpu_insn_hlt();

},
u32 entry_point, void *callee_stack_frame)


CASM_FUNCDEF(void, _geec_sentinel_xfer_ret_vft_prog_to_uvt_uvu_prog,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_movl_eax_esp();
    xmhfhwm_cpu_insn_popl_ebx();
    xmhfhwm_cpu_insn_popl_esi();
    xmhfhwm_cpu_insn_popl_edi();
    xmhfhwm_cpu_insn_popl_ebp();
    xmhfhwm_cpu_insn_ret();
},
void *caller_stack_frame)



CASM_FUNCDEF(void, _geec_sentinel_xfer_call_uvt_uvu_prog_to_vft_prog,
{
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_movl_mesp_edx(0x8);
    xmhfhwm_cpu_insn_movl_edx_esp();
    xmhfhwm_cpu_insn_pushl_esp();
    xmhfhwm_cpu_insn_pushl_imm(0x0);
    xmhfhwm_cpu_insn_jmpl_eax();
    xmhfhwm_cpu_insn_hlt();
},
u32 entry_point, void *callee_stack_frame)


CASM_FUNCDEF(void, _geec_sentinel_xfer_ret_uvt_uvu_prog_to_vft_prog,
{
    //caller_stack_frame:
    // ebx, esi, edi, ebp, return-eip
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_movl_eax_esp();
    xmhfhwm_cpu_insn_popl_ebx();
    xmhfhwm_cpu_insn_popl_esi();
    xmhfhwm_cpu_insn_popl_edi();
    xmhfhwm_cpu_insn_popl_ebp();

    xmhfhwm_cpu_insn_popl_edx(); //edx = return-eip
    xmhfhwm_cpu_insn_movl_esp_ecx(); //ecx = stack pointer
    xmhfhwm_cpu_insn_sysexit();             //sysexit to ring-3
    xmhfhwm_cpu_insn_hlt();
},
void *caller_stack_frame)
