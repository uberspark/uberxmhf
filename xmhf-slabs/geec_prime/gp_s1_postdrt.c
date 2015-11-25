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
#include <xmhf-hwm.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <geec_prime.h>
#include <geec_sentinel.h>
#include <uapi_slabmempgtbl.h>
#include <xc_init.h>

void gp_s1_postdrt(void){
	txt_heap_t *txt_heap;
	os_mle_data_t os_mle_data;
	u32 txt_heap_size;
	u32 os_mle_data_paddr;

	os_mle_data.saved_mtrr_state.num_var_mtrrs=0;

	txt_heap = get_txt_heap();
	_XDPRINTF_("SL: txt_heap = 0x%08x\n", (u32)txt_heap);

	txt_heap_size =  (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE);
	os_mle_data_paddr = get_os_mle_data_start((txt_heap_t*)((u32)txt_heap), txt_heap_size);
	//@assert (os_mle_data_paddr == (XMHFHWM_TXT_SYSMEM_HEAPBASE+0x8+sizeof(bios_data_t)+0x8));

	//xmhfhw_sysmemaccess_copy(&os_mle_data, get_os_mle_data_start((txt_heap_t*)((u32)txt_heap), (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE)),
	//				sizeof(os_mle_data_t));
	CASM_FUNCCALL(xmhfhw_sysmem_copy_sys2obj, (u32)&os_mle_data,
		os_mle_data_paddr, sizeof(os_mle_data_t));

	_XDPRINTF_("SL: os_mle_data = 0x%08x, size=%u bytes\n", (u32)&os_mle_data,
			sizeof(os_mle_data));

	if(os_mle_data.saved_mtrr_state.num_var_mtrrs < MAX_VARIABLE_MTRRS){
		// restore pre-SENTER MTRRs that were overwritten for SINIT launch
		if(!validate_mtrrs(&os_mle_data.saved_mtrr_state)) {
			_XDPRINTF_("SECURITY FAILURE: validate_mtrrs() failed.\n");
			CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
		}

		_XDPRINTF_("SL: Validated MTRRs\n");

		xmhfhw_cpu_x86_restore_mtrrs(&(os_mle_data.saved_mtrr_state));

		_XDPRINTF_("SL: Restored MTRRs\n");

	}else{
		_XDPRINTF_("%s:%u num_var_mtrrs >= MAX_VARIABLE_MTRRS\n",
			__func__, __LINE__);
		CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
	}


}
