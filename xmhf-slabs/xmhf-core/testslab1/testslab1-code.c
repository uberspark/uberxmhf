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

#include <testslab2.h>

/*
 * slab code
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
slab_retval_t testslab1_interface(u32 src_slabid, u32 dst_slabid, u32 fn_id, ...){
	slab_retval_t srval;
	_XDPRINTF_("%s: Got control: src_slabid=%u, dst_slabid=%u, fn_id=%u\n", __FUNCTION__, src_slabid, dst_slabid, fn_id);
	
	_XDPRINTF_("%s: proceeding to invoke testslab2 interface, TOS=%08x\n", __FUNCTION__, read_esp());
	srval = XMHF_SLAB_CALL_P2P(testslab2, XMHF_SLAB_TESTSLAB1_INDEX, XMHF_SLAB_TESTSLAB2_INDEX, 0, 0);
	_XDPRINTF_("%s: came back, TOS=%08x\n", __FUNCTION__, read_esp());

			/*_XDPRINTF_("\n%s: preparing to invoke entry_1, esp=%x", __FUNCTION__, read_esp());
			srval=XMHF_SLAB_CALL(entry_1(5, 3));
			_XDPRINTF_("\n%s: came back from entry_1, esp=%x", __FUNCTION__, read_esp());
			_XDPRINTF_("\n%s: came back from entry_1, value=%u", __FUNCTION__, srval.retval_u32);
						
			_XDPRINTF_("%s: preparing to invoke entry_2, esp=%x\n", __FUNCTION__, read_esp());
			srval= XMHF_SLAB_CALL(entry_2(2048, true, 4096));
			_XDPRINTF_("\n%s: came back from entry_2, esp=%x", __FUNCTION__, read_esp());
			_XDPRINTF_("\n%s: ctx: cpu_index=%u, isbsp=%u, partition_index=%u", __FUNCTION__, srval.retval_context_desc.cpu_desc.cpu_index, srval.retval_context_desc.cpu_desc.isbsp, srval.retval_context_desc.partition_desc.partition_index);
			
			ap_input.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_INFOREGS;
			ap_input.param.inforegs.info_vminstr_error = 0; 
			ap_input.param.inforegs.info_vmexit_reason = 1; 
			ap_input.param.inforegs.info_vmexit_interrupt_information = 2; 
			ap_input.param.inforegs.info_vmexit_interrupt_error_code = 3; 
			ap_input.param.inforegs.info_idt_vectoring_information = 4; 
			ap_input.param.inforegs.info_idt_vectoring_error_code = 5; 
			ap_input.param.inforegs.info_vmexit_instruction_length = 6; 
			ap_input.param.inforegs.info_vmx_instruction_information = 7; 
			ap_input.param.inforegs.info_exit_qualification = 8; 
			ap_input.param.inforegs.info_io_rcx = 9; 
			ap_input.param.inforegs.info_io_rsi = 10; 
			ap_input.param.inforegs.info_io_rdi = 11; 
			ap_input.param.inforegs.info_io_rip = 12; 
			ap_input.param.inforegs.info_guest_linear_address = 13; 
			ap_input.param.inforegs.info_guest_paddr_full = 14; 

			_XDPRINTF_("\n%s: preparing to invoke entry_3, esp=%x", __FUNCTION__, read_esp());
			srval = XMHF_SLAB_CALL(entry_3(srval.retval_context_desc, ap_input));			
			_XDPRINTF_("\n%s: came back from entry_3, esp=%x", __FUNCTION__, read_esp());
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_vminstr_error                  %u",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_vminstr_error                ); 
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_vmexit_reason                  %u",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_vmexit_reason                ); 
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_vmexit_interrupt_information   %u",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_vmexit_interrupt_information ); 
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_vmexit_interrupt_error_code    %u",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_vmexit_interrupt_error_code  ); 
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_idt_vectoring_information      %u",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_idt_vectoring_information    ); 
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_idt_vectoring_error_code       %u",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_idt_vectoring_error_code     ); 
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_vmexit_instruction_length      %u",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_vmexit_instruction_length    ); 
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_vmx_instruction_information    %u",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_vmx_instruction_information  ); 
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_exit_qualification             %llu",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_exit_qualification           ); 
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_io_rcx                         %llu",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_io_rcx                       ); 
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_io_rsi                         %llu",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_io_rsi                       ); 
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_io_rdi                         %llu",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_io_rdi                       ); 
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_io_rip                         %llu",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_io_rip                       ); 
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_guest_linear_address           %llu",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_guest_linear_address         ); 
			_XDPRINTF_("\nsrval.retval_xc_hypapp_arch_param.param.inforegs.info_guest_paddr_full               %llu",  srval.retval_xc_hypapp_arch_param.param.inforegs.info_guest_paddr_full             ); 
			
			
			*/

	_XDPRINTF_("\nXMHF Tester Finished!\n");
	_XDPRINTF_("\n\n");
	HALT();
		
	
	return srval;	
}




///////////////////////////////////////////////////////////////////////////// 
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
//XMHF_SLAB("testslab1")

//XMHF_SLAB_DEFINTERFACE(
//	//XMHF_SLAB_DEFEXPORTFN(entry_0, XMHF_SLAB_TESTSLAB1_FNENTRY0, XMHF_SLAB_FN_RETTYPE_AGGREGATE)
//	XMHF_SLAB_DEFEXPORTFN(entry_1, XMHF_SLAB_TESTSLAB1_FNENTRY1, XMHF_SLAB_FN_RETTYPE_AGGREGATE)
//	XMHF_SLAB_DEFEXPORTFN(entry_2, XMHF_SLAB_TESTSLAB1_FNENTRY2, XMHF_SLAB_FN_RETTYPE_AGGREGATE)
//	XMHF_SLAB_DEFEXPORTFN(entry_3, XMHF_SLAB_TESTSLAB1_FNENTRY3, XMHF_SLAB_FN_RETTYPE_AGGREGATE)
//)

//XMHF_SLAB_DEFINTERFACE_NEW(
//	XMHF_SLAB_P2P_DEFEXPORTFN(entry_0, XMHF_SLAB_TESTSLAB1_FNENTRY0)
//)

XMHF_SLAB_DEF(testslab1)

