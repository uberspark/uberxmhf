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
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-hwm.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
// #include <xmhfgeec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_prime.h>

#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
uint32_t check_esp, check_eip = CASM_RET_EIP;

void hwm_vdriver_writeesp(uint32_t oldval, uint32_t newval){
	//@assert (newval >= ((uint32_t)&_init_bsp_cpustack + 4)) && (newval <= ((uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
}

void main(void){
	//populate hardware model stack and program counter
	hwm_cpu_gprs_esp = (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
	hwm_cpu_gprs_eip = check_eip;
	check_esp = hwm_cpu_gprs_esp; // pointing to top-of-stack

	// //@assert (hwm_txt_heap.biosdatasize == sizeof(bios_data_t));
	// //@assert (hwm_txt_heap.osmledatasize == PAGE_SIZE_4K);
	// //@assert (hwm_txt_heap.ossinitdatasize == sizeof(os_sinit_data_t));
	// //@assert (hwm_txt_heap.sinitmledatasize == sizeof(sinit_mle_data_t));

	//execute harness
	gp_s1_postdrt();

	//@assert hwm_cpu_state == CPU_STATE_RUNNING || hwm_cpu_state == CPU_STATE_HALT;
	//@assert hwm_cpu_gprs_esp == check_esp;
	//@assert hwm_cpu_gprs_eip == check_eip;
}
#endif

void gp_s1_postdrt(void){
	txt_heap_t *txt_heap;
	os_mle_data_t os_mle_data;
	uint32_t txt_heap_size;
	uint32_t os_mle_data_paddr;

	//save SINIT to MLE MTRR mappings
	uberspark_uobjrtl_hw__generic_x86_32_intel__x86_save_mtrrs(&sinit2mle_mtrrs);

	os_mle_data.saved_mtrr_state.num_var_mtrrs=0;

	txt_heap = get_txt_heap();
	_XDPRINTF_("SL: txt_heap = 0x%08x\n", (uint32_t)txt_heap);

	txt_heap_size =  (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE);
	os_mle_data_paddr = get_os_mle_data_start((txt_heap_t*)((uint32_t)txt_heap), txt_heap_size);
	//@assert (os_mle_data_paddr == (hwm_TXT_SYSMEM_HEAPBASE+0x8+sizeof(bios_data_t)+0x8));

	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmem_copy_sys2obj, (uint32_t)&os_mle_data,
		os_mle_data_paddr, sizeof(os_mle_data_t));

	_XDPRINTF_("SL: os_mle_data = 0x%08x, size=%u bytes\n", (uint32_t)&os_mle_data,
			sizeof(os_mle_data));

	if(os_mle_data.saved_mtrr_state.num_var_mtrrs < MAX_VARIABLE_MTRRS){
		// restore pre-SENTER MTRRs that were overwritten for SINIT launch
		if(!validate_mtrrs(&os_mle_data.saved_mtrr_state)) {
			_XDPRINTF_("Error: validate_mtrrs() failed.\n");
			CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
		}

		_XDPRINTF_("SL: Validated MTRRs\n");

		uberspark_uobjrtl_hw__generic_x86_32_intel__x86_restore_mtrrs(&(os_mle_data.saved_mtrr_state));

		_XDPRINTF_("SL: Restored MTRRs\n");

	}else{
		_XDPRINTF_("%s:%u num_var_mtrrs >= MAX_VARIABLE_MTRRS\n",
			__func__, __LINE__);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
	}


}
