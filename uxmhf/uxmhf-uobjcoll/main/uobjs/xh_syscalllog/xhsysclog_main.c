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
#include <uberspark/include/uberspark.h>
// syscalllog hypapp main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xh_syscalllog.h>


#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
slab_params_t test_sp;
uint32_t cpuid = 0;	//BSP cpu
uint32_t check_esp, check_eip = CASM_RET_EIP;

void main(void){
	//populate hardware model stack and program counter
	xmhfhwm_cpu_gprs_esp = _slab_tos[cpuid];
	xmhfhwm_cpu_gprs_eip = check_eip;
	check_esp = xmhfhwm_cpu_gprs_esp; // pointing to top-of-stack

	test_sp.src_slabid = framac_nondetu32interval(0, XMHFGEEC_TOTAL_SLABS-1);
	test_sp.dst_slabid = XMHFGEEC_SLAB_XH_SYSCALLLOG;
	test_sp.dst_uapifn = framac_nondetu32();
	test_sp.cpuid = cpuid;
	test_sp.in_out_params[0] =  framac_nondetu32(); 	test_sp.in_out_params[1] = framac_nondetu32();
	test_sp.in_out_params[2] = framac_nondetu32(); 	test_sp.in_out_params[3] = framac_nondetu32();
	test_sp.in_out_params[4] = framac_nondetu32(); 	test_sp.in_out_params[5] = framac_nondetu32();
	test_sp.in_out_params[6] = framac_nondetu32(); 	test_sp.in_out_params[7] = framac_nondetu32();
	test_sp.in_out_params[8] = framac_nondetu32(); 	test_sp.in_out_params[9] = framac_nondetu32();
	test_sp.in_out_params[10] = framac_nondetu32(); 	test_sp.in_out_params[11] = framac_nondetu32();
	test_sp.in_out_params[12] = framac_nondetu32(); 	test_sp.in_out_params[13] = framac_nondetu32();
	test_sp.in_out_params[14] = framac_nondetu32(); 	test_sp.in_out_params[15] = framac_nondetu32();

	slab_main(&test_sp);

	/*@assert ((xmhfhwm_cpu_state == CPU_STATE_RUNNING && xmhfhwm_cpu_gprs_esp == check_esp && xmhfhwm_cpu_gprs_eip == check_eip) ||
		(xmhfhwm_cpu_state == CPU_STATE_HALT));
	@*/

	sysclog_register(framac_nondetu32(), framac_nondetu32(), framac_nondetu32(), framac_nondetu32(), framac_nondetu32());

	/*@assert ((xmhfhwm_cpu_state == CPU_STATE_RUNNING && xmhfhwm_cpu_gprs_esp == check_esp && xmhfhwm_cpu_gprs_eip == check_eip) ||
		(xmhfhwm_cpu_state == CPU_STATE_HALT));
	@*/

}
#endif

//@ ghost bool sysclog_methodcall_hcbinit = false;
//@ ghost bool sysclog_methodcall_hcbhypercall = false;
//@ ghost bool sysclog_methodcall_hcbmemfault = false;
//@ ghost bool sysclog_methodcall_invalid = false;
/*@
	requires \valid(sp);

	ensures (sp->in_out_params[0] == XC_HYPAPPCB_INITIALIZE) ==>
		 (sysclog_methodcall_hcbinit == true && (sp->in_out_params[3] == XC_HYPAPPCB_CHAIN));
	ensures (sp->in_out_params[0] == XC_HYPAPPCB_HYPERCALL) ==>
		(sysclog_methodcall_hcbhypercall == true && (sp->in_out_params[3] == XC_HYPAPPCB_CHAIN));
	ensures (sp->in_out_params[0] == XC_HYPAPPCB_MEMORYFAULT) ==>
		(sysclog_methodcall_hcbmemfault == true && (sp->in_out_params[3] == XC_HYPAPPCB_CHAIN || sp->in_out_params[3] == XC_HYPAPPCB_NOCHAIN));

	ensures !(
		(sp->in_out_params[0] == XC_HYPAPPCB_INITIALIZE) ||
		(sp->in_out_params[0] == XC_HYPAPPCB_HYPERCALL) ||
		(sp->in_out_params[0] == XC_HYPAPPCB_MEMORYFAULT)
		) ==> (sysclog_methodcall_invalid == true);
@*/

void slab_main(slab_params_t *sp){

	//_XDPRINTF_("XHSYSCALLLOG[%u]: Got control, cbtype=%x: ESP=%08x\n",
	//	(uint16_t)sp->cpuid, sp->in_out_params[0], CASM_FUNCCALL(read_esp,CASM_NOPARAM));

	if( sp->in_out_params[0] == XC_HYPAPPCB_INITIALIZE){
		sysclog_hcbinit(sp->cpuid);
		//@ghost sysclog_methodcall_hcbinit = true;
		sp->in_out_params[3]= XC_HYPAPPCB_CHAIN;


	}else if (sp->in_out_params[0] == XC_HYPAPPCB_HYPERCALL){
		sysclog_hcbhypercall(sp->cpuid, sp->in_out_params[2]);
		//@ghost sysclog_methodcall_hcbhypercall = true;
		sp->in_out_params[3]= XC_HYPAPPCB_CHAIN;

	}else if (sp->in_out_params[0] == XC_HYPAPPCB_MEMORYFAULT){
		if(sysclog_hcbmemfault(sp->cpuid, sp->in_out_params[2]))
			sp->in_out_params[3] = XC_HYPAPPCB_NOCHAIN;
		else
			sp->in_out_params[3] = XC_HYPAPPCB_CHAIN;
		//@ghost sysclog_methodcall_hcbmemfault = true;

	}else{
		//_XDPRINTF_("%s[%u]: Unknown cbtype. Ignoring!\n",__func__, (uint16_t)sp->cpuid);
		sp->in_out_params[3]= XC_HYPAPPCB_CHAIN;
		//@ghost sysclog_methodcall_invalid = true;
	}

}
