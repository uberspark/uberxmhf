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
	x86smp_apbootstrapdata_t *apdptr = (x86smp_apbootstrapdata_t *)&xmhfhwm_mem_region_apbootstrap_dataseg;
	bool invoked_gp_s5_entry = false;
	
	void xmhfhwm_vdriver_writeesp(uint32_t oldval, uint32_t newval){
	}
	
	void xmhfhwm_vdriver_cpu_writecr3(uint32_t oldval, uint32_t newval){
		//@assert (newval ==(uint32_t)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);
	}

	void xmhfhwm_vdriver_smpcommon(void){
		invoked_gp_s5_entry = true;
		//@assert (xmhfhwm_cpu_es_selector == 0x8);
		//@assert (xmhfhwm_cpu_fs_selector == 0x8);
		//@assert (xmhfhwm_cpu_gs_selector == 0x8);
		//@assert (xmhfhwm_cpu_ss_selector == 0x8);
		//@assert (xmhfhwm_cpu_cr4 == 0x30);
		//@assert (xmhfhwm_cpu_cr3 ==(uint32_t)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);
		//@assert (xmhfhwm_cpu_msr_efer & 0x800);
		//@assert (xmhfhwm_cpu_cr0 == 0x80000015);
		//@assert (xmhfhwm_cpu_msr_apic_base == MMIO_APIC_BASE);
	}

	void main(void){
		uint32_t i;

		//execute harness
		for(i=0; i < (MAX_PLATFORM_CPUS-1); i++){
			xmhfhwm_cpu_gprs_esp = (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
			xmhfhwm_cpu_ds_selector = 0x8;
			xmhfhwm_cpu_cr4 = 0;
			xmhfhwm_cpu_gprs_ebx = (uint32_t)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t;
			xmhfhwm_lapic_reg_id = i << 24;
			CASM_FUNCCALL(gp_s4_apstacks, CASM_NOPARAM);
			//@assert (invoked_gp_s5_entry == true);
			//@assert (xmhfhwm_cpu_gprs_esp == ((uint32_t)&_init_cpustacks[i+1][8]));
		}
	}
#endif


CASM_FUNCDEF(void, gp_s4_apstacks,
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
    xmhfhwm_cpu_insn_andl_imm_eax(0x00000FFF);
    xmhfhwm_cpu_insn_orl_imm_eax(0xFEE00000);
    xmhfhwm_cpu_insn_wrmsr();


    xmhfhwm_cpu_insn_xorl_eax_eax();
    xmhfhwm_cpu_insn_movl_imm_esi(0xFEE00020);
    xmhfhwm_cpu_insn_movl_mesi_eax(0x0);
    xmhfhwm_cpu_insn_shr_imm_eax(24);           //eax = lapic id (0-255)


    xmhfhwm_cpu_insn_movl_imm_ecx(16384);
    xmhfhwm_cpu_insn_xorl_edx_edx();
    xmhfhwm_cpu_insn_mull_ecx();
    xmhfhwm_cpu_insn_addl_ecx_eax();
    xmhfhwm_cpu_insn_movl_imm_esp(_init_cpustacks);
    xmhfhwm_cpu_insn_addl_eax_esp();

    xmhfhwm_cpu_insn_jmpsmpcommon();
    xmhfhwm_cpu_insn_ret();
},
void *noparam)


