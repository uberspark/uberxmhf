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
 GEEC sentinel low-level support routines
 author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/hwm/arch/x86_32/intel/hwm.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_sentinel.h>

#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_init.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_gcpustate.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xh_aprvexec.h>

uint32_t cpuid = 0;	//cpu
uint32_t check_esp, check_eip = CASM_RET_EIP;

	#if defined (DRV_PATH_CALLUH2VH)
	slab_params_t drv_path_calluh2vh_callersp;
	
	void hwm_vdriver_slabep(void){
		//@assert hwm_cpu_gprs_eip == (uint32_t)xmhfgeec_slab_info_table[XMHFGEEC_SLAB_UAPI_GCPUSTATE].entrystub;
		//@assert false;
	}
	
	void drv_path_calluh2vh(void){
		drv_path_calluh2vh_callersp.slab_ctype = XMHFGEEC_SENTINEL_CALL_uVT_uVU_PROG_TO_VfT_PROG;
        drv_path_calluh2vh_callersp.src_slabid = XMHFGEEC_SLAB_XH_SSTEPTRACE;
        drv_path_calluh2vh_callersp.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
        drv_path_calluh2vh_callersp.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
		drv_path_calluh2vh_callersp.cpuid = 0;
	
		//inform hardware model to treat slab stack region as valid memory
		hwm_sysmemaccess_physmem_extents[hwm_sysmemaccess_physmem_extents_total].addr_start =
			xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XH_SSTEPTRACE].slab_physmem_extents[2].addr_start;
		hwm_sysmemaccess_physmem_extents[hwm_sysmemaccess_physmem_extents_total].addr_end =
			xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XH_SSTEPTRACE].slab_physmem_extents[2].addr_end;
		hwm_sysmemaccess_physmem_extents_total++;
	
		//setup verified slab stack parameters for parameter marshalling
		hwm_cpu_gprs_esp -= sizeof(slab_params_t);
		xmhfgeec_slab_info_table[XMHFGEEC_SLAB_UAPI_GCPUSTATE].slabtos[cpuid] = hwm_cpu_gprs_esp;
	
		//invoke syscall sentinel stub
		hwm_cpu_gprs_edx = 0;
		hwm_cpu_gprs_ecx = &drv_path_calluh2vh_callersp;
		CASM_FUNCCALL(gs_syscallstub, CASM_NOPARAM);
		//@assert false;
	}
	#endif // defined

	#if defined (DRV_PATH_RETVH2UH)
	slab_params_t drv_pathretvh2uh_sp;
	slab_params_t drv_pathretvh2uh_callersp;
	gs_siss_element_t siss_elem;
	
	void hwm_vdriver_vhslabretaddr(void){
		//@assert hwm_cpu_gprs_eip == CASM_RET_EIP;
		//@assert hwm_cpu_gprs_esp == _slab_tos[cpuid];
		//@assert false;
	}
	
	void drv_path_retvh2uh(void){
		drv_pathretvh2uh_sp.slab_ctype = XMHFGEEC_SENTINEL_RET_VfT_PROG_TO_uVT_uVU_PROG;
		drv_pathretvh2uh_sp.src_slabid = XMHFGEEC_SLAB_XH_SSTEPTRACE;
        drv_pathretvh2uh_sp.dst_slabid = XMHFGEEC_SLAB_XC_INIT;
        drv_pathretvh2uh_sp.dst_uapifn = 0;
		drv_pathretvh2uh_sp.cpuid = 0;
	
		//inform hardware model to treat slab stack region as valid memory
		hwm_sysmemaccess_physmem_extents[hwm_sysmemaccess_physmem_extents_total].addr_start =
			xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XH_SSTEPTRACE].slab_physmem_extents[2].addr_start;
		hwm_sysmemaccess_physmem_extents[hwm_sysmemaccess_physmem_extents_total].addr_end =
			xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XH_SSTEPTRACE].slab_physmem_extents[2].addr_end;
		hwm_sysmemaccess_physmem_extents_total++;
	
		//setup verified slab stack frame that this slab is returning to
		hwm_cpu_gprs_esp -= sizeof(uint32_t);
		*(uint32_t *)hwm_cpu_gprs_esp = CASM_RET_EIP;
		hwm_cpu_gprs_esp -= sizeof(uint32_t);
		*(uint32_t *)hwm_cpu_gprs_esp = hwm_cpu_gprs_ebp;
		hwm_cpu_gprs_esp -= sizeof(uint32_t);
		*(uint32_t *)hwm_cpu_gprs_esp = hwm_cpu_gprs_edi;
		hwm_cpu_gprs_esp -= sizeof(uint32_t);
		*(uint32_t *)hwm_cpu_gprs_esp = hwm_cpu_gprs_esi;
		hwm_cpu_gprs_esp -= sizeof(uint32_t);
		*(uint32_t *)hwm_cpu_gprs_esp = hwm_cpu_gprs_ebx;
	
		//plug in an entry in the SISS corresponding to this RET
		siss_elem.src_slabid = XMHFGEEC_SLAB_XC_INIT;
		siss_elem.dst_slabid = XMHFGEEC_SLAB_XH_SSTEPTRACE;
		siss_elem.slab_ctype = XMHFGEEC_SENTINEL_CALL_VfT_PROG_TO_uVT_uVU_PROG;
		siss_elem.caller_stack_frame = hwm_cpu_gprs_esp;
		siss_elem.sp = &drv_pathretvh2uh_callersp;
	
		gs_siss_push(drv_pathretvh2uh_sp.cpuid, siss_elem);
	
		//invoke syscall sentinel stub
		hwm_cpu_gprs_edx = 0;
		hwm_cpu_gprs_ecx = &drv_pathretvh2uh_sp;
		CASM_FUNCCALL(gs_syscallstub, CASM_NOPARAM);
		//@assert false;
	}
	#endif // DRV_PATH_RETVH2UH



void main(void){
	//populate hardware model stack and program counter
	hwm_cpu_gprs_esp = _slab_tos[cpuid];
	hwm_cpu_gprs_eip = check_eip;
	check_esp = hwm_cpu_gprs_esp; // pointing to top-of-stack

	#if defined (DRV_PATH_CALLUH2VH)
	drv_path_calluh2vh();
	#endif // DRV_PATH_CALLUH2VH

	#if defined (DRV_PATH_RETVH2UH)
	drv_path_retvh2uh();
	#endif // DRV_PATH_RETVH2UH

}

#endif

////// syscall entry point
CASM_FUNCDEF(void, gs_syscallstub,
{
    __casm__pushl_edx();   //original caller_stack_frame
    __casm__pushl_ecx();
    __casm__call_c_2p(gs_entry_syscall, slab_params_t *, void *);
    __casm__hlt();
},
void *noparam)





