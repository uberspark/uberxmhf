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
 sentinel v2x call entry-point
 author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhf-debug.h>
#include <xmhfgeec.h>

#include <geec_sentinel.h>

//////
// sentinel [p_call] entry point
//////


// C invocation of this function is of type _slab_entrystub(slab_params_t *sp)
// Pre: [esp] = return address to resume the (verified,privileged) caller
//	[esp+4] = slab_params_t *sp (pointer to slab_params_t within caller
//					memory area)


#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
#include <xc_init.h>
#include <uapi_gcpustate.h>
#include <xh_aprvexec.h>

uint32_t saved_cpu_gprs_ebx=0;
uint32_t saved_cpu_gprs_esi=0;
uint32_t saved_cpu_gprs_edi=0;
uint32_t saved_cpu_gprs_ebp=0;
uint32_t cpuid = 0;	//cpu

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

uint32_t check_esp, check_eip = CASM_RET_EIP;

	#if defined (DRV_PATHV2V)
	slab_params_t drv_pathv2v_sp;
	
	void xmhfhwm_vdriver_slabep(void){
		cabi_check();
		//@assert xmhfhwm_cpu_gprs_eip == (uint32_t)xmhfgeec_slab_info_table[XMHFGEEC_SLAB_UAPI_GCPUSTATE].entrystub;
		//@assert xmhfhwm_cpu_gprs_esp == check_esp - (2 * sizeof(uint32_t));
		//@assert *((uint32_t *)xmhfhwm_cpu_gprs_esp) == CASM_RET_EIP;
		//@assert *((uint32_t *)((uint32_t)xmhfhwm_cpu_gprs_esp+4)) == (unsigned int)&drv_pathv2v_sp;
		//@assert false;
	}
	
	void drv_pathv2v(void){
		drv_pathv2v_sp.slab_ctype =XMHFGEEC_SENTINEL_CALL_FROM_VfT_PROG;
        drv_pathv2v_sp.src_slabid = XMHFGEEC_SLAB_XC_INIT;
        drv_pathv2v_sp.dst_slabid =XMHFGEEC_SLAB_UAPI_GCPUSTATE;
        drv_pathv2v_sp.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		drv_pathv2v_sp.cpuid = 0;
	
		cabi_establish();
		CASM_FUNCCALL(_slab_entrystub, &drv_pathv2v_sp);
		//@assert false;
	}
	#endif // DRV_PATHV2V

	#if defined (DRV_PATHV2UV)
	slab_params_t drv_pathv2uv_sp;
	
	void xmhfhwm_vdriver_slabep(void){
		cabi_check();
		//@assert xmhfhwm_cpu_gprs_eip == (uint32_t)xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XH_SSTEPTRACE].entrystub;
		//@assert false;
	}
	
	void drv_pathv2uv(void){
		drv_pathv2uv_sp.slab_ctype =XMHFGEEC_SENTINEL_CALL_FROM_VfT_PROG;
        drv_pathv2uv_sp.src_slabid = XMHFGEEC_SLAB_XC_INIT;
        drv_pathv2uv_sp.dst_slabid = XMHFGEEC_SLAB_XH_SSTEPTRACE;
        drv_pathv2uv_sp.dst_uapifn = 0;
		drv_pathv2uv_sp.cpuid = 0;
	
		xmhfhwm_sysmemaccess_physmem_extents[xmhfhwm_sysmemaccess_physmem_extents_total].addr_start =
			xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XH_SSTEPTRACE].slab_physmem_extents[2].addr_start;
		xmhfhwm_sysmemaccess_physmem_extents[xmhfhwm_sysmemaccess_physmem_extents_total].addr_end =
			xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XH_SSTEPTRACE].slab_physmem_extents[2].addr_end;
		xmhfhwm_sysmemaccess_physmem_extents_total++;
	
		cabi_establish();
		CASM_FUNCCALL(_slab_entrystub, &drv_pathv2uv_sp);
		//@assert false;
	}
	#endif // defined


	#if defined (DRV_PATHV2UG)
	slab_params_t drv_path_callv2ug_sp;
	
	void xmhfhwm_vdriver_slabep(void){
		//@assert false;
	}
	
	void drv_path_callv2ug(void){
		drv_path_callv2ug_sp.slab_ctype = XMHFGEEC_SENTINEL_CALL_FROM_VfT_PROG;
        drv_path_callv2ug_sp.src_slabid = XMHFGEEC_SLAB_XC_INIT;
        drv_path_callv2ug_sp.dst_slabid = XMHFGEEC_SLAB_XG_RICHGUEST;
        drv_path_callv2ug_sp.dst_uapifn = 0;
		drv_path_callv2ug_sp.cpuid = 0;
		
		CASM_FUNCCALL(_slab_entrystub, &drv_path_callv2ug_sp);
		//@assert false;
	}
	#endif // defined

	#if defined (DRV_PATH_RETEXCP)
	slab_params_t drv_path_retexcp_sp;

	void xmhfhwm_vdriver_slabep(void){
		//@assert false;
	}

	void drv_path_retexcp(void){
		drv_path_retexcp_sp.slab_ctype = XMHFGEEC_SENTINEL_RET_EXCEPTION;
        drv_path_retexcp_sp.src_slabid = XMHFGEEC_SLAB_XC_EXHUB;
        drv_path_retexcp_sp.dst_slabid = XMHFGEEC_SLAB_GEEC_SENTINEL;
        drv_path_retexcp_sp.dst_uapifn = 0;
		drv_path_retexcp_sp.cpuid = 0;

		CASM_FUNCCALL(_slab_entrystub, &drv_path_retexcp_sp);
		//@assert false;
	}
	#endif //defined

	#if defined (DRV_PATH_RETICPT)
	slab_params_t drv_path_reticpt_sp;
	
	void xmhfhwm_vdriver_slabep(void){
		//@assert false;
	}
	
	void drv_path_reticpt(void){
		drv_path_reticpt_sp.slab_ctype = XMHFGEEC_SENTINEL_RET_INTERCEPT;
        drv_path_reticpt_sp.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
        drv_path_reticpt_sp.dst_slabid = XMHFGEEC_SLAB_XG_RICHGUEST;
        drv_path_reticpt_sp.dst_uapifn = 0;
		drv_path_reticpt_sp.cpuid = 0;
	
		CASM_FUNCCALL(_slab_entrystub, &drv_path_reticpt_sp);
		//@assert false;
	}
	#endif // defined

	#if defined (DRV_PATH_RETUH2VH)
	slab_params_t drv_path_retuh2vh_calleesp;
	uint32_t drv_path_retuh2vh_callerstackframe[6];
	gs_siss_element_t siss_elem;
	
	void xmhfhwm_vdriver_uhslabretaddr(void){
		// //@assert xmhfhwm_cpu_gprs_eip == CASM_RET_EIP;
		// //@assert xmhfhwm_cpu_gprs_esp == _slab_tos[cpuid];
		//@assert false;
	}
	
	void drv_path_retuh2vh(void){
		drv_path_retuh2vh_calleesp.slab_ctype = XMHFGEEC_SENTINEL_RET_uVT_uVU_PROG_TO_VfT_PROG;
        drv_path_retuh2vh_calleesp.src_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
        drv_path_retuh2vh_calleesp.dst_slabid = XMHFGEEC_SLAB_XH_SSTEPTRACE;
        drv_path_retuh2vh_calleesp.dst_uapifn = 0;
		drv_path_retuh2vh_calleesp.cpuid = 0;
	
		//inform hardware model to treat slab stack region as valid memory
		xmhfhwm_sysmemaccess_physmem_extents[xmhfhwm_sysmemaccess_physmem_extents_total].addr_start =
			xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XH_SSTEPTRACE].slab_physmem_extents[2].addr_start;
		xmhfhwm_sysmemaccess_physmem_extents[xmhfhwm_sysmemaccess_physmem_extents_total].addr_end =
			xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XH_SSTEPTRACE].slab_physmem_extents[2].addr_end;
		xmhfhwm_sysmemaccess_physmem_extents_total++;
		
		//plug in an entry in the SISS corresponding to this RET
		siss_elem.src_slabid = XMHFGEEC_SLAB_XH_SSTEPTRACE;
		siss_elem.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
		siss_elem.slab_ctype = XMHFGEEC_SENTINEL_CALL_uVT_uVU_PROG_TO_VfT_PROG;
		siss_elem.caller_stack_frame = &drv_path_retuh2vh_callerstackframe[0];
		siss_elem.sp = xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XH_SSTEPTRACE].slabtos[cpuid];
	
		gs_siss_push(cpuid, siss_elem);
	
		//invoke sentinel
		CASM_FUNCCALL(_slab_entrystub, &drv_path_retuh2vh_calleesp);
		//@assert false;
	}
	#endif // defined



void main(void){
	//populate hardware model stack and program counter
	xmhfhwm_cpu_gprs_esp = _slab_tos[cpuid];
	xmhfhwm_cpu_gprs_eip = check_eip;
	check_esp = xmhfhwm_cpu_gprs_esp; // pointing to top-of-stack

	#if defined (DRV_PATHV2V)
	drv_pathv2v();
	#endif // DRV_PATHV2V
	
	#if defined (DRV_PATHV2UV)
	drv_pathv2uv();
	#endif
	
	#if defined (DRV_PATHV2UG)
	drv_path_callv2ug();
	#endif // defined

	#if defined (DRV_PATH_RETEXCP)
	drv_path_retexcp();
	#endif // DRV_PATH_RETEXCP

	#if defined (DRV_PATH_RETICPT)
	drv_path_reticpt();
	#endif // defined

	#if defined (DRV_PATH_RETUH2VH)
	drv_path_retuh2vh();
	#endif // defined

}
#endif

CASM_FUNCDEF_FULL(.slab_entrystub, 1, void, _slab_entrystub,
{
	xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
	xmhfhwm_cpu_insn_pushl_ebp();
	xmhfhwm_cpu_insn_pushl_edi();
	xmhfhwm_cpu_insn_pushl_esi();
	xmhfhwm_cpu_insn_pushl_ebx();
	xmhfhwm_cpu_insn_movl_esp_edx();
	xmhfhwm_cpu_insn_pushl_edx();
	xmhfhwm_cpu_insn_pushl_eax();
	// stack frame at this point:
	// 	[esp] = slab_params_t *sp
	//	[esp+4] = &[esp+8]
	//	[esp+8] = ebx
	//	[esp+12] = esi
	//	[esp+16] = edi
	//	[esp+20] = ebp
	//	[esp+24] = return address to resume the (verified,privileged) caller
	//	[esp+28] = slab_params_t *sp
	xmhfhwm_cpu_insn_call_c_2p(geec_sentinel_main, slab_params_t *, void *);

	// halt if we ever return back (should never happen)
	xmhfhwm_cpu_insn_hlt();
},
slab_params_t *sp)

