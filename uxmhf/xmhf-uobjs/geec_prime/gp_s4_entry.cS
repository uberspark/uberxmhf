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


// GEEC prime SMP assembly language code blobs
// author: amit vasudevan (amitvasudevan@acm.org)

#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
	uint32_t check_esp, check_eip = CASM_RET_EIP;
	x86smp_apbootstrapdata_t *apdptr = (x86smp_apbootstrapdata_t *)&xmhfhwm_mem_region_apbootstrap_dataseg;

	void xmhfhwm_vdriver_writeesp(uint32_t oldval, uint32_t newval){
		//@assert (newval >= ((uint32_t)&_init_bsp_cpustack + 4)) && (newval <= ((uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
	}

	void xmhfhwm_vdriver_cpu_writecr3(uint32_t oldval, uint32_t newval){
		//@assert (newval ==(uint32_t)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);
	}

	void xmhfhwm_vdriver_apentry(void){
		//@assert (xmhfhwm_cpu_gprs_eax == (uint32_t)&gp_s4_apstacks);
		//@assert (xmhfhwm_cpu_gprs_ebx == 0xDEADBEEF);
		//@assert (xmhfhwm_cpu_gprs_edi == 0);
	}

	void main(void){
		//populate hardware model stack and program counter
		xmhfhwm_cpu_gprs_esp = (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
		xmhfhwm_cpu_gprs_eip = check_eip;
		check_esp = xmhfhwm_cpu_gprs_esp; // pointing to top-of-stack
	
		//execute harness
		apdptr->ap_cr3 = 0xDEADBEEF;
	    apdptr->ap_entrypoint = (uint32_t)&gp_s4_apstacks;
	    apdptr->cpuidtable = 0;
	
		CASM_FUNCCALL(gp_s4_entry, CASM_NOPARAM);
	
		//@assert xmhfhwm_cpu_gprs_esp == check_esp;
		//@assert xmhfhwm_cpu_gprs_eip == check_eip;
	}

#endif



CASM_FUNCDEF(void, gp_s4_entry,
{
    xmhfhwm_cpu_insn_movw_imm_ax(__DS_CPL0);
    xmhfhwm_cpu_insn_movw_ax_ds();

    xmhfhwm_cpu_insn_movl_imm_esi(((X86SMP_APBOOTSTRAP_DATASEG << 4) + 32))
    xmhfhwm_cpu_insn_movl_mesi_eax(0x0);
    xmhfhwm_cpu_insn_movl_eax_edi();

    xmhfhwm_cpu_insn_movl_imm_esi(((X86SMP_APBOOTSTRAP_DATASEG << 4) + 0));
    xmhfhwm_cpu_insn_movl_mesi_eax(0x0);
    xmhfhwm_cpu_insn_movl_eax_ebx();

    xmhfhwm_cpu_insn_movl_imm_esi(((X86SMP_APBOOTSTRAP_DATASEG << 4) + 8));
    xmhfhwm_cpu_insn_movl_mesi_eax(0x0);

    xmhfhwm_cpu_insn_jmpapentry();

    xmhfhwm_cpu_insn_ret();
    CASM_BALIGN(4096);
},
void *noparam)


