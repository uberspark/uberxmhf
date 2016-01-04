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
#include <geec_sentinel.h>

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
u32 check_esp, check_eip = CASM_RET_EIP;
bool gp_s5_entry_invoked = false;

void xmhfhwm_vdriver_writeesp(u32 oldval, u32 newval){
	//@assert (newval >= ((u32)&_init_bsp_cpustack + 4)) && (newval <= ((u32)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
}

void xmhfhwm_vdriver_cpu_writecr3(u32 oldval, u32 newval){
	//@assert (newval ==(u32)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);
}


void main(void){
	//u32 cpuid = framac_nondetu32interval(0, (MAX_PLATFORM_CPUS-1));
	//bool isbsp = framac_nondetu32interval(0, 1);
	u32 cpuid = 0;
	bool isbsp = true;


	//populate hardware model stack and program counter
	xmhfhwm_cpu_gprs_esp = (u32)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
	xmhfhwm_cpu_gprs_eip = check_eip;
	check_esp = xmhfhwm_cpu_gprs_esp; // pointing to top-of-stack

	//execute harness
	xmhfhwm_cpu_cr4 = 0x00000030;
	xmhfhwm_cpu_cr0 = 0x80000015;
	xmhfhwm_cpu_cr3 =(u32)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t;

	gp_s5_setupcpustate(cpuid, isbsp);

	//@assert (xmhfhwm_cpu_gdtr_base == (u32)&__xmhfhic_x86vmx_gdt_start);
	//@assert (xmhfhwm_cpu_cs_selector == __CS_CPL0);
	//@assert (xmhfhwm_cpu_ds_selector == __DS_CPL0);
	//@assert (xmhfhwm_cpu_es_selector == __DS_CPL0);
	//@assert (xmhfhwm_cpu_fs_selector == __DS_CPL0);
	//@assert (xmhfhwm_cpu_gs_selector == __DS_CPL0);
	//@assert (xmhfhwm_cpu_ss_selector == __DS_CPL0);
	//@assert (xmhfhwm_cpu_tr_selector ==(__TRSEL + ((u32)cpuid * 8) ));
	//@assert (xmhfhwm_cpu_idtr_base == (u32)&__xmhfhic_x86vmx_idt_start);
	//@assert (xmhfhwm_cpu_eflags & EFLAGS_IOPL);
	//@assert (xmhfhwm_cpu_msr_apic_base == MMIO_APIC_BASE);
	//@assert (xmhfhwm_cpu_msr_efer & ((1 << EFER_NXE)));
	//@assert (xmhfhwm_cpu_cr4 & CR4_OSXSAVE);
	//@assert (xmhfhwm_cpu_cr0 & 0x20);
	//@assert (xmhfhwm_cpu_msr_sysenter_cs == __CS_CPL0);
        //@assert (xmhfhwm_cpu_msr_sysenter_eip == xmhfgeec_slab_info_table[XMHFGEEC_SLAB_GEEC_SENTINEL].slab_memoffset_entries[GEEC_SENTINEL_MEMOFFSETS_SYSENTERHANDLER_IDX]);
	//@assert (xmhfhwm_cpu_msr_sysenter_esp_lo == (u32)((u32)&_geec_primesmp_sysenter_stack[(u32)cpuid+1]));
	//@assert (xmhfhwm_cpu_msr_sysenter_esp_hi == 0);
	//@assert (xmhfhwm_cpu_vmcs_host_rip == xmhfgeec_slab_info_table[XMHFGEEC_SLAB_GEEC_SENTINEL].slab_memoffset_entries[GEEC_SENTINEL_MEMOFFSETS_INTERCEPTHANDLER_IDX]);
	//@assert (xmhfhwm_cpu_vmcs_host_rsp >= ((u32)&_init_bsp_cpustack + 4)) && (xmhfhwm_cpu_vmcs_host_rsp <= ((u32)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
	//@assert (xmhfhwm_cpu_vmcs_host_cr3 == (u32)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);


	//@assert xmhfhwm_cpu_gprs_esp == check_esp;
	//@assert xmhfhwm_cpu_gprs_eip == check_eip;
}


