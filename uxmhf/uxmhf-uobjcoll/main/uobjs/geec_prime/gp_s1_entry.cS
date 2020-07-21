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
#include <xmhf-debug.h>
#include <xmhfgeec.h>

#include <geec_prime.h>

//////
// XMHF/GEEC prime state-1 entry
// author: amit vasudevan (amitvasudevan@acm.org)

#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
bool gp_s1_bspstack_called = false;

void xmhfhwm_vdriver_writeesp(uint32_t oldval, uint32_t newval){
	//@assert (newval >= ((uint32_t)&_init_bsp_cpustack + 4)) && (newval <= ((uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
}

void gp_s1_bspstack(void){
	//@assert xmhfhwm_cpu_gprs_esp == (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE - 4;
	//@assert xmhfhwm_cpu_es_selector == xmhfhwm_cpu_ds_selector;
	//@assert xmhfhwm_cpu_fs_selector == xmhfhwm_cpu_ds_selector;
	//@assert xmhfhwm_cpu_gs_selector == xmhfhwm_cpu_ds_selector;
	//@assert xmhfhwm_cpu_ss_selector == xmhfhwm_cpu_ds_selector;
	//@assert xmhfhwm_cpu_state == CPU_STATE_RUNNING;

	//indicate bspstack was invoked from entry
	gp_s1_bspstack_called = true;
	//setup stack back to normal so value can return from the initial call to slab_main
	xmhfhwm_cpu_gprs_esp = (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE - 8;
}

void main(void){
	//populate hardware model stack and program counter
	xmhfhwm_cpu_gprs_esp = (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;

	//execute harness
	xmhfhwm_cpu_ds_selector = 0x8;
	CASM_FUNCCALL(slab_main, CASM_NOPARAM);
	//@assert gp_s1_bspstack_called == true;
}
#endif

CASM_FUNCDEF(void, slab_main,
{
	xmhfhwm_cpu_insn_movw_ds_ax();
	xmhfhwm_cpu_insn_movw_ax_es();
	xmhfhwm_cpu_insn_movw_ax_fs();
	xmhfhwm_cpu_insn_movw_ax_gs();
	xmhfhwm_cpu_insn_movw_ax_ss();
	xmhfhwm_cpu_insn_movl_imm_eax(_init_bsp_cpustack);
	xmhfhwm_cpu_insn_addl_imm_eax(MAX_PLATFORM_CPUSTACK_SIZE);
	xmhfhwm_cpu_insn_movl_eax_esp();
	xmhfhwm_cpu_insn_call_c(gp_s1_bspstack);
	xmhfhwm_cpu_insn_hlt();
	xmhfhwm_cpu_insn_ret()
},
slab_params_t *sp)


