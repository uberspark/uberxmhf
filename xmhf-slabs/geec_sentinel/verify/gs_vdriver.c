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
 * libxmhfhw CASM functions verification driver
 * author: amit vasudevan (amitvasudevan@acm.org)
*/


#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfgeec.h>
#include <xmhf-debug.h>

#include <geec_sentinel.h>
#include <xc_init.h>
#include <uapi_gcpustate.h>

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
u32 saved_cpu_gprs_ebx=0;
u32 saved_cpu_gprs_esi=0;
u32 saved_cpu_gprs_edi=0;
u32 saved_cpu_gprs_ebp=0;

void cabi_establish(void){
	xmhfhwm_cpu_gprs_ebx = 5UL;
	xmhfhwm_cpu_gprs_esi = 6UL;
	xmhfhwm_cpu_gprs_edi = 7UL;
	saved_cpu_gprs_ebx = xmhfhwm_cpu_gprs_ebx;
	saved_cpu_gprs_esi = xmhfhwm_cpu_gprs_esi;
	saved_cpu_gprs_edi = xmhfhwm_cpu_gprs_edi;
}

void cabi_check(void){
	//@ assert saved_cpu_gprs_ebx == xmhfhwm_cpu_gprs_ebx;
	//@ assert saved_cpu_gprs_esi == xmhfhwm_cpu_gprs_esi;
	//@ assert saved_cpu_gprs_edi == xmhfhwm_cpu_gprs_edi;
}



u32 check_esp, check_eip = CASM_RET_EIP;







#if defined (DRV_PATH_RETV2UV)
slab_params_t drv_pathretv2uv_sp;
slab_params_t drv_pathretv2uv_callersp;
gs_siss_element_t siss_elem;

void xmhfhwm_vdriver_vhslabretaddr(void){
	//@assert xmhfhwm_cpu_gprs_eip == CASM_RET_EIP;
	//@assert xmhfhwm_cpu_gprs_esp == _slab_tos[cpuid];
	//@assert false;
}

void drv_pathretv2uv(void){
	drv_pathretv2uv_sp.slab_ctype = XMHFGEEC_SENTINEL_RET_VfT_PROG_TO_uVT_uVU_PROG;
        drv_pathretv2uv_sp.src_slabid = XMHFGEEC_SLAB_XC_TESTSLAB;
        drv_pathretv2uv_sp.dst_slabid = XMHFGEEC_SLAB_XC_INIT;
        drv_pathretv2uv_sp.dst_uapifn = 0;
	drv_pathretv2uv_sp.cpuid = 0;




	//inform hardware model to treat slab stack region as valid memory
	xmhfhwm_sysmemaccess_physmem_extents[xmhfhwm_sysmemaccess_physmem_extents_total].addr_start =
		xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_TESTSLAB].slab_physmem_extents[2].addr_start;
	xmhfhwm_sysmemaccess_physmem_extents[xmhfhwm_sysmemaccess_physmem_extents_total].addr_end =
		xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_TESTSLAB].slab_physmem_extents[2].addr_end;
	xmhfhwm_sysmemaccess_physmem_extents_total++;

	//setup verified slab stack frame that this slab is returning to
	xmhfhwm_cpu_gprs_esp -= sizeof(u32);
	*(u32 *)xmhfhwm_cpu_gprs_esp = CASM_RET_EIP;
	xmhfhwm_cpu_gprs_esp -= sizeof(u32);
	*(u32 *)xmhfhwm_cpu_gprs_esp = xmhfhwm_cpu_gprs_ebp;
	xmhfhwm_cpu_gprs_esp -= sizeof(u32);
	*(u32 *)xmhfhwm_cpu_gprs_esp = xmhfhwm_cpu_gprs_edi;
	xmhfhwm_cpu_gprs_esp -= sizeof(u32);
	*(u32 *)xmhfhwm_cpu_gprs_esp = xmhfhwm_cpu_gprs_esi;
	xmhfhwm_cpu_gprs_esp -= sizeof(u32);
	*(u32 *)xmhfhwm_cpu_gprs_esp = xmhfhwm_cpu_gprs_ebx;


	//plug in an entry in the SISS corresponding to this RET
	siss_elem.src_slabid = XMHFGEEC_SLAB_XC_INIT;
	siss_elem.dst_slabid = XMHFGEEC_SLAB_XC_TESTSLAB;
	siss_elem.slab_ctype = XMHFGEEC_SENTINEL_CALL_VfT_PROG_TO_uVT_uVU_PROG;
	siss_elem.caller_stack_frame = xmhfhwm_cpu_gprs_esp;
	siss_elem.sp = &drv_pathretv2uv_callersp;

	gs_siss_push(drv_pathretv2uv_sp.cpuid, siss_elem);

	//invoke syscall sentinel stub
	xmhfhwm_cpu_gprs_edx = 0;
	xmhfhwm_cpu_gprs_ecx = &drv_pathretv2uv_sp;
	CASM_FUNCCALL(gs_syscallstub, CASM_NOPARAM);
	//@assert false;
}
#endif // DRV_PATH_RETV2UV







#if defined (DRV_PATH_CALLUV2V)
slab_params_t drv_path_calluv2v_callersp;

void xmhfhwm_vdriver_slabep(void){
	// //@assert xmhfhwm_cpu_gprs_eip == CASM_RET_EIP;
	// //@assert xmhfhwm_cpu_gprs_esp == _slab_tos[cpuid];
	//@assert false;
}

void drv_path_calluv2v(void){
	drv_path_calluv2v_callersp.slab_ctype = XMHFGEEC_SENTINEL_CALL_uVT_uVU_PROG_TO_VfT_PROG;
        drv_path_calluv2v_callersp.src_slabid = XMHFGEEC_SLAB_XC_TESTSLAB;
        drv_path_calluv2v_callersp.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
        drv_path_calluv2v_callersp.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
	drv_path_calluv2v_callersp.cpuid = 0;


	//inform hardware model to treat slab stack region as valid memory
	xmhfhwm_sysmemaccess_physmem_extents[xmhfhwm_sysmemaccess_physmem_extents_total].addr_start =
		xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_TESTSLAB].slab_physmem_extents[2].addr_start;
	xmhfhwm_sysmemaccess_physmem_extents[xmhfhwm_sysmemaccess_physmem_extents_total].addr_end =
		xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_TESTSLAB].slab_physmem_extents[2].addr_end;
	xmhfhwm_sysmemaccess_physmem_extents_total++;

	//load cr3 for xc_testslab
	xmhfhwm_cpu_cr3 = xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_TESTSLAB].mempgtbl_cr3;

	//setup verified slab stack parameters for parameter marshalling
	xmhfhwm_cpu_gprs_esp -= sizeof(slab_params_t);
	xmhfgeec_slab_info_table[XMHFGEEC_SLAB_UAPI_GCPUSTATE].slabtos[cpuid] = xmhfhwm_cpu_gprs_esp;


	//invoke syscall sentinel stub
	xmhfhwm_cpu_gprs_edx = 0;
	xmhfhwm_cpu_gprs_ecx = &drv_path_calluv2v_callersp;
	CASM_FUNCCALL(gs_syscallstub, CASM_NOPARAM);
	//@assert false;
}
#endif // defined












void main(void){
	//populate hardware model stack and program counter
	xmhfhwm_cpu_gprs_esp = _slab_tos[cpuid];
	xmhfhwm_cpu_gprs_eip = check_eip;
	check_esp = xmhfhwm_cpu_gprs_esp; // pointing to top-of-stack


#if defined (DRV_PATH_RETV2UV)
	drv_pathretv2uv();
#endif // DRV_PATH_RETV2UV

#if defined (DRV_PATH_CALLUV2V)
	drv_path_calluv2v();
#endif // defined





}


