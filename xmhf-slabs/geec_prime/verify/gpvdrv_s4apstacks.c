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
 * prime s3_entry verification driver
 * author: amit vasudevan (amitvasudevan@acm.org)
*/


#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfgeec.h>

#include <geec_prime.h>

u32 cpuid = 0;	//BSP cpu

//////
// frama-c non-determinism functions
//////

u32 Frama_C_entropy_source;

//@ assigns Frama_C_entropy_source \from Frama_C_entropy_source;
void Frama_C_update_entropy(void);

u32 framac_nondetu32(void){
  Frama_C_update_entropy();
  return (u32)Frama_C_entropy_source;
}

u32 framac_nondetu32interval(u32 min, u32 max)
{
  u32 r,aux;
  Frama_C_update_entropy();
  aux = Frama_C_entropy_source;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}


//////
//u32 check_esp, check_eip = CASM_RET_EIP;
x86smp_apbootstrapdata_t *apdptr = (x86smp_apbootstrapdata_t *)&xmhfhwm_mem_region_apbootstrap_dataseg;
bool invoked_gp_s5_entry = false;

void xmhfhwm_vdriver_writeesp(u32 oldval, u32 newval){
	////@assert (newval >= ((u32)&_init_bsp_cpustack + 4)) && (newval <= ((u32)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
}

void xmhfhwm_vdriver_cpu_writecr3(u32 oldval, u32 newval){
	//@assert (newval ==(u32)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);
}

void xmhfhwm_vdriver_smpcommon(void){
	invoked_gp_s5_entry = true;
	//@assert (xmhfhwm_cpu_es_selector == 0x8);
	//@assert (xmhfhwm_cpu_fs_selector == 0x8);
	//@assert (xmhfhwm_cpu_gs_selector == 0x8);
	//@assert (xmhfhwm_cpu_ss_selector == 0x8);
	//@assert (xmhfhwm_cpu_cr4 == 0x30);
	//@assert (xmhfhwm_cpu_cr3 ==(u32)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);
	//@assert (xmhfhwm_cpu_msr_efer & 0x800);
	//@assert (xmhfhwm_cpu_cr0 == 0x80000015);
	//@assert (xmhfhwm_cpu_msr_apic_base == MMIO_APIC_BASE);
}


void main(void){
	//populate hardware model stack and program counter
	xmhfhwm_cpu_gprs_esp = (u32)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
	//xmhfhwm_cpu_gprs_eip = check_eip;
	//check_esp = xmhfhwm_cpu_gprs_esp; // pointing to top-of-stack


	//execute harness
	xmhfhwm_cpu_ds_selector = 0x8;
	xmhfhwm_cpu_cr4 = 0;
	xmhfhwm_cpu_gprs_ebx = (u32)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t;
	xmhfhwm_lapic_reg_id = 1UL << 24;
	CASM_FUNCCALL(gp_s4_apstacks, CASM_NOPARAM);
	//@assert (invoked_gp_s5_entry == true);
	//@assert (xmhfhwm_cpu_gprs_esp == ((u32)&_init_cpustacks[(xmhfhwm_lapic_reg_id >> 24)+1][8]));

	////@assert xmhfhwm_cpu_gprs_esp == check_esp;
	////@assert xmhfhwm_cpu_gprs_eip == check_eip;
}


