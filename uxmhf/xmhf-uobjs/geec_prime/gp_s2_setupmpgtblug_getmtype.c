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


//---get memory type for a given physical page address--------------------------
//
//11.11.4.1 MTRR Precedences
//  0. if MTRRs are not enabled --> MTRR_TYPE_UC
//  if enabled then
     //if physaddr < 1MB use fixed MTRR ranges return type
     //else if within a valid variable range MTRR then
        //if a single match, return type
        //if two or more and one is UC, return UC
        //if two or more and WB and WT, return WT
        //else invalid combination
     //else
       // return default memory type
//

#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
uint32_t check_esp, check_eip = CASM_RET_EIP;
uint64_t p_pagebaseaddr;

void xmhfhwm_vdriver_writeesp(uint32_t oldval, uint32_t newval){
	//@assert (newval >= ((uint32_t)&_init_bsp_cpustack + 4)) && (newval <= ((uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
}

void main(void){
	//populate hardware model stack and program counter
	xmhfhwm_cpu_gprs_esp = (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
	xmhfhwm_cpu_gprs_eip = check_eip;
	check_esp = xmhfhwm_cpu_gprs_esp; // pointing to top-of-stack

	//execute harness
	p_pagebaseaddr = framac_nondetu32interval(0, 0xFFFFFFFFUL);
	gp_s2_setupmpgtblug_getmtype(p_pagebaseaddr);

	//@assert xmhfhwm_cpu_state == CPU_STATE_RUNNING || xmhfhwm_cpu_state == CPU_STATE_HALT;
	//@assert xmhfhwm_cpu_gprs_esp == check_esp;
	//@assert xmhfhwm_cpu_gprs_eip == check_eip;
}
#endif

uint32_t gp_s2_setupmpgtblug_getmtype(uint64_t pagebaseaddr){
	int i;
	uint32_t prev_type= MTRR_TYPE_RESV;

	//check if page base address under 1M, if so used FIXED MTRRs
	if(pagebaseaddr < (1024*1024)){
		for(i=0; i < MAX_FIXED_MEMORYTYPE_ENTRIES; i++){
			if( pagebaseaddr >= _vmx_ept_memorytypes[i].startaddr && (pagebaseaddr+PAGE_SIZE_4K-1) <= _vmx_ept_memorytypes[i].endaddr )
				return _vmx_ept_memorytypes[i].type;
		}

		_XDPRINTF_("\n%s: endaddr < 1M and unmatched fixed MTRR. Halt!", __func__);
		CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
	}

	//page base address is above 1M, use VARIABLE MTRRs
	for(i= MAX_FIXED_MEMORYTYPE_ENTRIES; i < MAX_MEMORYTYPE_ENTRIES; i++){
		if( pagebaseaddr >= _vmx_ept_memorytypes[i].startaddr && (pagebaseaddr+PAGE_SIZE_4K-1) <= _vmx_ept_memorytypes[i].endaddr &&
			(!_vmx_ept_memorytypes[i].invalid) ){
			if(_vmx_ept_memorytypes[i].type == MTRR_TYPE_UC){
				prev_type = MTRR_TYPE_UC;
			}else if(_vmx_ept_memorytypes[i].type == MTRR_TYPE_WT && prev_type != MTRR_TYPE_UC){
				prev_type = MTRR_TYPE_WT;
			}else{
				if(prev_type != MTRR_TYPE_UC && prev_type != MTRR_TYPE_WT){
					if(prev_type == MTRR_TYPE_RESV){
						prev_type = _vmx_ept_memorytypes[i].type;
					}else{
						if(!(prev_type == _vmx_ept_memorytypes[i].type)){
							_XDPRINTF_("%s:%u MTRR type/range unhandled. Halting!\n",
									__func__, __LINE__);
							CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
						}
					}
				}
			}
		}
	}

	if(prev_type == MTRR_TYPE_RESV)
		prev_type = MTRR_TYPE_WB; //todo: need to dynamically get the default MTRR (usually WB)

	if(prev_type != MTRR_TYPE_UC)
		prev_type = MTRR_TYPE_WB;

	return prev_type;
}


