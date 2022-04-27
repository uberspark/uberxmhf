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
#include <xc_init.h>

#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
	uint32_t check_esp, check_eip = CASM_RET_EIP;
	bool gp_s5_entry_invoked = false;

	void xmhfhwm_vdriver_writeesp(uint32_t oldval, uint32_t newval){
		//@assert (newval >= ((uint32_t)&_init_bsp_cpustack + 4)) && (newval <= ((uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
	}

	void xmhfhwm_vdriver_cpu_writecr3(uint32_t oldval, uint32_t newval){
		//@assert (newval ==(uint32_t)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);
	}

	void __slab_callsentinel(slab_params_t *sp){
		//@assert (sp->src_slabid == XMHFGEEC_SLAB_GEEC_PRIME);
		//@assert (sp->dst_slabid == XMHFGEEC_SLAB_XC_INIT);
		//@assert (sp->cpuid >=0 && sp->cpuid <= 255);
		//@assert (xmhfhwm_cpu_state == CPU_STATE_RUNNING);
	}

	void main(void){
		uint32_t cpuid = framac_nondetu32interval(0, 255);
		//populate hardware model stack and program counter
		xmhfhwm_cpu_gprs_esp = (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
		xmhfhwm_cpu_gprs_eip = check_eip;
		check_esp = xmhfhwm_cpu_gprs_esp; // pointing to top-of-stack

		//execute harness
		gp_s5_invokestrt(cpuid);

		//@assert xmhfhwm_cpu_gprs_esp == check_esp;
		//@assert xmhfhwm_cpu_gprs_eip == check_eip;
	}

#endif

void gp_s5_invokestrt(uint32_t cpuid){
	slab_params_t sp;

	memset(&sp, 0, sizeof(sp));
	sp.cpuid = cpuid;
	sp.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
	sp.dst_slabid = XMHFGEEC_SLAB_XC_INIT;
	sp.in_out_params[0] = xcbootinfo->richguest_bootmodule_base;
	sp.in_out_params[1] = xcbootinfo->richguest_bootmodule_size;
	XMHF_SLAB_CALLNEW(&sp);

	_XDPRINTF_("%s[%u]: Should never be here. Halting!\n",
		__func__, (uint16_t)cpuid);
	CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
}
