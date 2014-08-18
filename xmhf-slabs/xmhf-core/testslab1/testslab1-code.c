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
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <testslab1.h>

/*
 * slab code
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

 
slab_retval_t entry_0(u32 src_slabid, u32 dst_slabid, u32 fn_id){
	slab_retval_t srval;
	_XDPRINTF_("%s: Got control: nothing to do!\n", __FUNCTION__);
	return srval;	//void
}
	
slab_retval_t entry_1(u32 param1, u32 param2){
	slab_retval_t srval;
	_XDPRINTF_("%s: Huhu we are here\n", __FUNCTION__);
	_XDPRINTF_("%s: param1=%u, param2=%u\n", __FUNCTION__, param1, param2);
	srval.retval_u32 = param1+param2;
	return srval;	//u32
}

slab_retval_t entry_2(u32 cpu_index, bool isbsp, u32 partition_index){
	slab_retval_t srval;

	_XDPRINTF_("\n%s: Got control: cpu_index=%u, isbsp=%u, partition_index=%u", __FUNCTION__, cpu_index, isbsp, partition_index);
	
	srval.retval_context_desc.cpu_desc.cpu_index = cpu_index;
	srval.retval_context_desc.cpu_desc.isbsp = isbsp;
	srval.retval_context_desc.partition_desc.partition_index = partition_index;
	
	return srval;
}	

slab_retval_t entry_3(context_desc_t context_desc, xc_hypapp_arch_param_t archparam){
	slab_retval_t srval;

	_XDPRINTF_("\n%s: Got control: cpu_index=%u, isbsp=%u, partition_index=%u", __FUNCTION__, context_desc.cpu_desc.cpu_index, context_desc.cpu_desc.isbsp, context_desc.partition_desc.partition_index);
	
	srval.retval_xc_hypapp_arch_param.operation = archparam.operation;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_vminstr_error = archparam.param.inforegs.info_vminstr_error;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_vmexit_reason = archparam.param.inforegs.info_vmexit_reason;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_vmexit_interrupt_information = archparam.param.inforegs.info_vmexit_interrupt_information;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_vmexit_interrupt_error_code = archparam.param.inforegs.info_vmexit_interrupt_error_code;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_idt_vectoring_information = archparam.param.inforegs.info_idt_vectoring_information;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_idt_vectoring_error_code = archparam.param.inforegs.info_idt_vectoring_error_code;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_vmexit_instruction_length = archparam.param.inforegs.info_vmexit_instruction_length;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_vmx_instruction_information = archparam.param.inforegs.info_vmx_instruction_information;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_exit_qualification = archparam.param.inforegs.info_exit_qualification;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_io_rcx = archparam.param.inforegs.info_io_rcx;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_io_rsi = archparam.param.inforegs.info_io_rsi;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_io_rdi = archparam.param.inforegs.info_io_rdi;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_io_rip = archparam.param.inforegs.info_io_rip;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_guest_linear_address = archparam.param.inforegs.info_guest_linear_address;
	srval.retval_xc_hypapp_arch_param.param.inforegs.info_guest_paddr_full = archparam.param.inforegs.info_guest_paddr_full;
	
	return srval;
}

///////
XMHF_SLAB("testslab1")

//XMHF_SLAB_DEFINTERFACE(
//	//XMHF_SLAB_DEFEXPORTFN(entry_0, XMHF_SLAB_TESTSLAB1_FNENTRY0, XMHF_SLAB_FN_RETTYPE_AGGREGATE)
//	XMHF_SLAB_DEFEXPORTFN(entry_1, XMHF_SLAB_TESTSLAB1_FNENTRY1, XMHF_SLAB_FN_RETTYPE_AGGREGATE)
//	XMHF_SLAB_DEFEXPORTFN(entry_2, XMHF_SLAB_TESTSLAB1_FNENTRY2, XMHF_SLAB_FN_RETTYPE_AGGREGATE)
//	XMHF_SLAB_DEFEXPORTFN(entry_3, XMHF_SLAB_TESTSLAB1_FNENTRY3, XMHF_SLAB_FN_RETTYPE_AGGREGATE)
//)

XMHF_SLAB_DEFINTERFACE_NEW(
	XMHF_SLAB_P2P_DEFEXPORTFN(entry_0, XMHF_SLAB_TESTSLAB1_FNENTRY0)
)
