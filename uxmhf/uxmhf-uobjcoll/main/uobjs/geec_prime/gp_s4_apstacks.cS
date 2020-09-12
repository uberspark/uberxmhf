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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_prime.h>


// GEEC prime SMP assembly language code blobs
// author: amit vasudevan (amitvasudevan@acm.org)

#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
	x86smp_apbootstrapdata_t *apdptr = (x86smp_apbootstrapdata_t *)&hwm_mem_region_apbootstrap_dataseg;
	bool invoked_gp_s5_entry = false;
	
	void hwm_vdriver_writeesp(uint32_t oldval, uint32_t newval){
	}
	
	void hwm_vdriver_cpu_writecr3(uint32_t oldval, uint32_t newval){
		//@assert (newval ==(uint32_t)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);
	}

	void hwm_vdriver_smpcommon(void){
		invoked_gp_s5_entry = true;
		//@assert (hwm_cpu_es_selector == 0x8);
		//@assert (hwm_cpu_fs_selector == 0x8);
		//@assert (hwm_cpu_gs_selector == 0x8);
		//@assert (hwm_cpu_ss_selector == 0x8);
		//@assert (hwm_cpu_cr4 == 0x30);
		//@assert (hwm_cpu_cr3 ==(uint32_t)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);
		//@assert (hwm_cpu_msr_efer & 0x800);
		//@assert (hwm_cpu_cr0 == 0x80000015);
		//@assert (hwm_cpu_msr_apic_base == MMIO_APIC_BASE);
	}

	void main(void){
		uint32_t i;

		//execute harness
		for(i=0; i < (MAX_PLATFORM_CPUS-1); i++){
			hwm_cpu_gprs_esp = (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
			hwm_cpu_ds_selector = 0x8;
			hwm_cpu_cr4 = 0;
			hwm_cpu_gprs_ebx = (uint32_t)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t;
			hwm_lapic_reg_id = i << 24;
			CASM_FUNCCALL(gp_s4_apstacks, CASM_NOPARAM);
			//@assert (invoked_gp_s5_entry == true);
			//@assert (hwm_cpu_gprs_esp == ((uint32_t)&_init_cpustacks[i+1][8]));
		}
	}
#endif


CASM_FUNCDEF(void, gp_s4_apstacks,
{
    __casm__movw_ds_ax();
    __casm__movw_ax_es();
    __casm__movw_ax_fs();
    __casm__movw_ax_gs();
    __casm__movw_ax_ss();

    __casm__movl_cr4_eax();
    __casm__orl_imm_eax(0x00000030);
    __casm__movl_eax_cr4();


    __casm__movl_ebx_cr3();


    __casm__movl_imm_ecx(0xc0000080);
    __casm__rdmsr();
    __casm__orl_imm_eax(0x00000800);
    __casm__wrmsr();


    __casm__movl_cr0_eax();
    __casm__orl_imm_eax(0x80000015);
    __casm__movl_eax_cr0();

    //TODO: for non-TXT wakeup we need to reload GDT
    //"movl %1, %esi \r\n");
    //"lgdt (%esi) \r\n");

    __casm__movl_imm_ecx(0x0000001B);
    __casm__rdmsr();
    __casm__andl_imm_eax(0x00000FFF);
    __casm__orl_imm_eax(0xFEE00000);
    __casm__wrmsr();


    __casm__xorl_eax_eax();
    __casm__movl_imm_esi(0xFEE00020);
    __casm__movl_mesi_eax(0x0);
    __casm__shr_imm_eax(24);           //eax = lapic id (0-255)


    __casm__movl_imm_ecx(16384);
    __casm__xorl_edx_edx();
    __casm__mull_ecx();
    __casm__addl_ecx_eax();
    __casm__movl_imm_esp(_init_cpustacks);
    __casm__addl_eax_esp();

    __casm__jmpsmpcommon();
    __casm__ret();
},
void *noparam)


