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


//////
#if defined (DRV_SLAB_ENTRYSTUB)

slab_params_t drv_slab_entrystub_sp;

void geec_sentinel_main(slab_params_t *sp,
	void *caller_stack_frame){
	//Pre:
	//	[esp] = CASM_RET_EIP
	//  	[esp+4] = slab_params_t *sp
	//	[esp+8] = &[esp+8]
	//	[esp+12] = ebx
	//	[esp+16] = esi
	//	[esp+20] = edi
	//	[esp+24] = ebp
	//	[esp+28] = return address to resume the (verified,privileged) caller
	//	[esp+32] = slab_params_t *sp
	//@assert sp->src_slabid == 6UL;
	//@assert xmhfhwm_cpu_gprs_esp == (check_esp - (9 * sizeof(u32)));
	//@assert *((u32 *)xmhfhwm_cpu_gprs_esp) == CASM_RET_EIP;
	//@assert *((u32 *)((u32)xmhfhwm_cpu_gprs_esp+4)) == (unsigned int)&drv_slab_entrystub_sp;
	//@assert *((u32 *)((u32)xmhfhwm_cpu_gprs_esp+8)) == (u32)xmhfhwm_cpu_gprs_esp+12;
	//@assert *((u32 *)((u32)xmhfhwm_cpu_gprs_esp+12)) == saved_cpu_gprs_ebx;
	//@assert *((u32 *)((u32)xmhfhwm_cpu_gprs_esp+16)) == saved_cpu_gprs_esi;
	//@assert *((u32 *)((u32)xmhfhwm_cpu_gprs_esp+20)) == saved_cpu_gprs_edi;
	//@assert *((u32 *)((u32)xmhfhwm_cpu_gprs_esp+24)) == saved_cpu_gprs_ebp;
	//@assert *((u32 *)((u32)xmhfhwm_cpu_gprs_esp+28)) == CASM_RET_EIP;
	//@assert *((u32 *)((u32)xmhfhwm_cpu_gprs_esp+32)) == (unsigned int)&drv_slab_entrystub_sp;

	//@assert false;
}


void drv_slab_entrystub(void){
	xmhfhwm_cpu_gprs_ebx = 5UL;
	xmhfhwm_cpu_gprs_esi = 6UL;
	xmhfhwm_cpu_gprs_edi = 7UL;
	xmhfhwm_cpu_gprs_ebp = 8UL;
	saved_cpu_gprs_ebx = xmhfhwm_cpu_gprs_ebx;
	saved_cpu_gprs_esi = xmhfhwm_cpu_gprs_esi;
	saved_cpu_gprs_edi = xmhfhwm_cpu_gprs_edi;
	saved_cpu_gprs_ebp = xmhfhwm_cpu_gprs_ebp;


	drv_slab_entrystub_sp.cpuid = 0;
	drv_slab_entrystub_sp.src_slabid = 6UL;

	CASM_FUNCCALL(_slab_entrystub, &drv_slab_entrystub_sp);
	//@assert false;
}

#endif // DRV_SLAB_ENTRYSTUB


#if defined (DRV_PATHV2V)
slab_params_t drv_pathv2v_sp;

void xmhfhwm_vdriver_slabep(void){
	//@assert xmhfhwm_cpu_gprs_eip == (u32)xmhfgeec_slab_info_table[XMHFGEEC_SLAB_UAPI_GCPUSTATE].entrystub;
	//@assert xmhfhwm_cpu_gprs_esp == check_esp - (2 * sizeof(u32));
	//@assert *((u32 *)xmhfhwm_cpu_gprs_esp) == CASM_RET_EIP;
	//@assert *((u32 *)((u32)xmhfhwm_cpu_gprs_esp+4)) == (unsigned int)&drv_pathv2v_sp;
	//@assert false;
}

void drv_pathv2v(void){
	drv_pathv2v_sp.slab_ctype =XMHFGEEC_SENTINEL_CALL_FROM_VfT_PROG;
        drv_pathv2v_sp.src_slabid = XMHFGEEC_SLAB_XC_INIT;
        drv_pathv2v_sp.dst_slabid =XMHFGEEC_SLAB_UAPI_GCPUSTATE;
        drv_pathv2v_sp.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
	drv_pathv2v_sp.cpuid = 0;

	CASM_FUNCCALL(_slab_entrystub, &drv_pathv2v_sp);
	//@assert false;
}
#endif // DRV_PATHV2V



#if defined (DRV_PATHV2UV)
slab_params_t drv_pathv2uv_sp;

void xmhfhwm_vdriver_slabep(void){
	//@assert xmhfhwm_cpu_gprs_eip == (u32)xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_TESTSLAB].entrystub;
	// //@assert xmhfhwm_cpu_gprs_esp == check_esp - (2 * sizeof(u32));
	// //@assert *((u32 *)xmhfhwm_cpu_gprs_esp) == CASM_RET_EIP;
	// //@assert *((u32 *)((u32)xmhfhwm_cpu_gprs_esp+4)) == (unsigned int)&drv_pathv2v_sp;
	//@assert false;
}

void drv_pathv2uv(void){
	drv_pathv2uv_sp.slab_ctype =XMHFGEEC_SENTINEL_CALL_FROM_VfT_PROG;
        drv_pathv2uv_sp.src_slabid = XMHFGEEC_SLAB_XC_INIT;
        drv_pathv2uv_sp.dst_slabid = XMHFGEEC_SLAB_XC_TESTSLAB;
        drv_pathv2uv_sp.dst_uapifn = 0;
	drv_pathv2uv_sp.cpuid = 0;


	xmhfhwm_sysmemaccess_physmem_extents[xmhfhwm_sysmemaccess_physmem_extents_total].addr_start =
		xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_TESTSLAB].slab_physmem_extents[2].addr_start;
	xmhfhwm_sysmemaccess_physmem_extents[xmhfhwm_sysmemaccess_physmem_extents_total].addr_end =
		xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_TESTSLAB].slab_physmem_extents[2].addr_end;
	xmhfhwm_sysmemaccess_physmem_extents_total++;

	CASM_FUNCCALL(_slab_entrystub, &drv_pathv2uv_sp);
	//@assert false;
}
#endif // defined




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




#if defined (DRV_PATH_RETUV2V)

slab_params_t drv_path_retuv2v_calleesp;
u32 drv_path_retuv2v_callerstackframe[6];
gs_siss_element_t siss_elem;

void xmhfhwm_vdriver_uhslabretaddr(void){
	// //@assert xmhfhwm_cpu_gprs_eip == CASM_RET_EIP;
	// //@assert xmhfhwm_cpu_gprs_esp == _slab_tos[cpuid];
	//@assert false;
}


void drv_path_retuv2v(void){
	drv_path_retuv2v_calleesp.slab_ctype = XMHFGEEC_SENTINEL_RET_uVT_uVU_PROG_TO_VfT_PROG;
        drv_path_retuv2v_calleesp.src_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
        drv_path_retuv2v_calleesp.dst_slabid = XMHFGEEC_SLAB_XC_TESTSLAB;
        drv_path_retuv2v_calleesp.dst_uapifn = 0;
	drv_path_retuv2v_calleesp.cpuid = 0;


	//inform hardware model to treat slab stack region as valid memory
	xmhfhwm_sysmemaccess_physmem_extents[xmhfhwm_sysmemaccess_physmem_extents_total].addr_start =
		xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_TESTSLAB].slab_physmem_extents[2].addr_start;
	xmhfhwm_sysmemaccess_physmem_extents[xmhfhwm_sysmemaccess_physmem_extents_total].addr_end =
		xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_TESTSLAB].slab_physmem_extents[2].addr_end;
	xmhfhwm_sysmemaccess_physmem_extents_total++;


	//plug in an entry in the SISS corresponding to this RET
	siss_elem.src_slabid = XMHFGEEC_SLAB_XC_TESTSLAB;
	siss_elem.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	siss_elem.slab_ctype = XMHFGEEC_SENTINEL_CALL_uVT_uVU_PROG_TO_VfT_PROG;
	siss_elem.caller_stack_frame = &drv_path_retuv2v_callerstackframe[0];
	siss_elem.sp = xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_TESTSLAB].slabtos[cpuid];

	gs_siss_push(cpuid, siss_elem);

	//invoke sentinel
	CASM_FUNCCALL(_slab_entrystub, &drv_path_retuv2v_calleesp);
	//@assert false;
}

#endif // defined



#if defined (DRV_PATH_CALLV2UVG)

slab_params_t drv_path_callv2uvg_sp;

void xmhfhwm_vdriver_slabep(void){
	//@assert xmhfhwm_cpu_gprs_eip == (u32)xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_TESTSLAB].entrystub;
	// //@assert xmhfhwm_cpu_gprs_esp == check_esp - (2 * sizeof(u32));
	// //@assert *((u32 *)xmhfhwm_cpu_gprs_esp) == CASM_RET_EIP;
	// //@assert *((u32 *)((u32)xmhfhwm_cpu_gprs_esp+4)) == (unsigned int)&drv_pathv2v_sp;
	//@assert false;
}

void drv_path_callv2uvg(void){
	drv_path_callv2uvg_sp.slab_ctype =XMHFGEEC_SENTINEL_CALL_FROM_VfT_PROG;
        drv_path_callv2uvg_sp.src_slabid = XMHFGEEC_SLAB_XC_INIT;
        drv_path_callv2uvg_sp.dst_slabid = XMHFGEEC_SLAB_XG_BENCHGUEST;
        drv_path_callv2uvg_sp.dst_uapifn = 0;
	drv_path_callv2uvg_sp.cpuid = 0;


	CASM_FUNCCALL(_slab_entrystub, &drv_path_callv2uvg_sp);
	//@assert false;
}
#endif // defined









#if defined (DRV_PATH_CALLICPT)
void xmhfhwm_vdriver_slabep(void){
	//@assert false;
}


void drv_path_callicpt(void){
	xmhfhwm_cpu_gprs_esp -= sizeof(x86vmx_exception_frame_t);

	//invoke sentinel intercept stub
	CASM_FUNCCALL(gs_entry_icptstub, CASM_NOPARAM);
	//@assert false;
}
#endif // defined


#if defined (DRV_PATH_RETICPT)
slab_params_t drv_path_reticpt_sp;

void xmhfhwm_vdriver_slabep(void){
	//@assert false;
}

void drv_path_reticpt(void){
	drv_path_reticpt_sp.slab_ctype = XMHFGEEC_SENTINEL_RET_INTERCEPT;
        drv_path_reticpt_sp.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
        drv_path_reticpt_sp.dst_slabid = XMHFGEEC_SLAB_XG_BENCHGUEST;
        drv_path_reticpt_sp.dst_uapifn = 0;
	drv_path_reticpt_sp.cpuid = 0;


	CASM_FUNCCALL(_slab_entrystub, &drv_path_reticpt_sp);
	//@assert false;
}
#endif // defined


#if defined (DRV_PATH_CALLEXCP)
x86vmx_exception_frame_t drv_path_callexcp_excpframe;

void xmhfhwm_vdriver_slabep(void){
	//@assert false;
}

void drv_path_callexcp(void){
	xmhfhwm_cpu_gprs_esp -= sizeof(x86vmx_exception_frame_t);

	//invoke sentinel exception stub
	//CASM_FUNCCALL(__xmhf_exception_handler_0, CASM_NOPARAM);
	CASM_FUNCCALL(__xmhf_exception_handler_8, CASM_NOPARAM);
	//@assert false;
}
#endif // defined



slab_params_t drv_path_retexcp_sp;

void xmhfhwm_vdriver_slabep(void){
	//@assert false;
}

void drv_path_retexcp(void){
	drv_path_retexcp_sp.slab_ctype = XMHFGEEC_SENTINEL_RET_EXCEPTION;
        drv_path_retexcp_sp.src_slabid = XMHFGEEC_SLAB_XC_EXHUB;
        drv_path_retexcp_sp.dst_slabid = XMHFGEEC_SLAB_GEEC_SENTINEL; //XXX: TODO: plug in normal slab id after adding support to sentinel
        drv_path_retexcp_sp.dst_uapifn = 0;
	drv_path_retexcp_sp.cpuid = 0;

	CASM_FUNCCALL(_slab_entrystub, &drv_path_retexcp_sp);
	//@assert false;
}



void main(void){
	//populate hardware model stack and program counter
	xmhfhwm_cpu_gprs_esp = _slab_tos[cpuid];
	xmhfhwm_cpu_gprs_eip = check_eip;
	check_esp = xmhfhwm_cpu_gprs_esp; // pointing to top-of-stack

	//execute harness: TODO
#if defined (DRV_SLAB_ENTRYSTUB)
	drv_slab_entrystub();
#endif //DRV_SLAB_ENTRYSTUB


#if defined (DRV_PATHV2V)
	drv_pathv2v();
#endif // DRV_PATHV2V

#if defined (DRV_PATHV2UV)
	drv_pathv2uv();
#endif

#if defined (DRV_PATH_RETV2UV)
	drv_pathretv2uv();
#endif // DRV_PATH_RETV2UV

#if defined (DRV_PATH_CALLUV2V)
	drv_path_calluv2v();
#endif // defined

#if defined (DRV_PATH_RETUV2V)
	drv_path_retuv2v();
#endif // defined

#if defined (DRV_PATH_CALLV2UVG)
	drv_path_callv2uvg();
#endif // defined


#if defined (DRV_PATH_CALLICPT)
	drv_path_callicpt();
#endif // defined

#if defined (DRV_PATH_RETICPT)
	drv_path_reticpt();
#endif // defined


#if defined (DRV_PATH_CALLEXCP)
	drv_path_callexcp();
#endif // defined


	drv_path_retexcp();

	//{
	//	unsigned char *p = (unsigned char *)(0x06c00000+ (1*XMHF_SLAB_STACKSIZE));
	//	*p = 'A';
	//}

	//@assert xmhfhwm_cpu_gprs_esp == check_esp;
	//@assert xmhfhwm_cpu_gprs_eip == check_eip;
}


