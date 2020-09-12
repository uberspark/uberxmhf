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
 * uXMHF core exception handling uobj
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

//#include <xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_exhub.h>

bool ihub_exit_status = false;
uint32_t ihub_exit_info = 0;



#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
uint32_t check_esp, check_eip = CASM_RET_EIP;
slab_params_t test_sp;
uint32_t cpuid = 0;	//cpu id

void main(void){
	//populate hardware model stack and program counter
	hwm_cpu_gprs_esp = _slab_tos[cpuid];
	hwm_cpu_gprs_eip = check_eip;
	check_esp = hwm_cpu_gprs_esp; // pointing to top-of-stack

    test_sp.slab_ctype = framac_nondetu32();
    test_sp.src_slabid = framac_nondetu32();
    test_sp.dst_slabid = framac_nondetu32();
    test_sp.dst_uapifn = framac_nondetu32();
    test_sp.cpuid = framac_nondetu32();
	test_sp.in_out_params[0] =  framac_nondetu32(); 	test_sp.in_out_params[1] = framac_nondetu32();
	test_sp.in_out_params[2] = framac_nondetu32(); 	test_sp.in_out_params[3] = framac_nondetu32();
	test_sp.in_out_params[4] = framac_nondetu32(); 	test_sp.in_out_params[5] = framac_nondetu32();
	test_sp.in_out_params[6] = framac_nondetu32(); 	test_sp.in_out_params[7] = framac_nondetu32();
	test_sp.in_out_params[8] = framac_nondetu32(); 	test_sp.in_out_params[9] = framac_nondetu32();
	test_sp.in_out_params[10] = framac_nondetu32(); 	test_sp.in_out_params[11] = framac_nondetu32();
	test_sp.in_out_params[12] = framac_nondetu32(); 	test_sp.in_out_params[13] = framac_nondetu32();
	test_sp.in_out_params[14] = framac_nondetu32(); 	test_sp.in_out_params[15] = framac_nondetu32();

	slab_main(&test_sp);

	/*@assert ((hwm_cpu_state == CPU_STATE_RUNNING && hwm_cpu_gprs_esp == check_esp && hwm_cpu_gprs_eip == check_eip) ||
		(hwm_cpu_state == CPU_STATE_HALT));
	@*/
}
#endif

// void slab_main(slab_params_t *sp){

// 	if( sp->dst_uapifn == UAPI_XCEXHUB_DEBUG){

// 		ihub_exit_status = sp->in_out_params[0];
// 		ihub_exit_info = sp->in_out_params[1];

// 	}else if( sp->dst_uapifn == UAPI_XCEXHUB_SETUPIDT){

// 		xcexhub_setupidt();

// 	}else if( sp->dst_uapifn == UAPI_XCEXHUB_LOADIDT){

// 		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__loadIDT,&xcexhub_idt);
// 		_XDPRINTF_("%s[%u]: IDT loaded\n", __func__, (uint16_t)sp->cpuid);

// 	}else if( sp->dst_uapifn == UAPI_XCEXHUB_LOADHOSTIDTRBASE){

// 		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__x86vmx_vmwrite,VMCS_HOST_IDTR_BASE, CASM_FUNCCALL32(xmhf_baseplatform_arch_x86_getidtbase,CASM_NOPARAM));

// 	}else{
// 		//unknown api ignore and return
// 	    return;
// 	}

// }


