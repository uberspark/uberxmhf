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

#include <testslab2.h>

/*
 * slab code
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

slab_retval_t testslab2_interface(u32 src_slabid, u32 dst_slabid, u32 fn_id, u32 fn_paramsize, ...){
	slab_retval_t srval;
	va_list args;
	
	_XDPRINTF_("%s: Got control: src_slabid=%u, dst_slabid=%u, fn_id=%u, fn_paramsize=%u\n", __FUNCTION__, src_slabid, dst_slabid, fn_id, fn_paramsize);
	
	switch(fn_id){
			case XMHF_SLAB_TESTSLAB2_FNENTRY1:
				testslab2_entry1();
				break;
	
			case XMHF_SLAB_TESTSLAB2_FNENTRY2:{
				u32 param1, param2;
				va_start(args, fn_paramsize);
				param1 = va_arg(args, u32);
				param2 = va_arg(args, u32);
				srval.retval_u32 = testslab2_entry2(param1, param2);
				va_end(args);
			}
			break;
				
				
			default:
				_XDPRINTF_("%s: unhandled subinterface %u. Halting\n", __FUNCTION__, fn_id);
				HALT();
	}
	
	return srval;	
}


void testslab2_entry1(void){
	_XDPRINTF_("%s: Got control: nothing to do!\n", __FUNCTION__);
}
	
u32 testslab2_entry2(u32 param1, u32 param2){
	_XDPRINTF_("%s: param1=%u, param2=%u\n", __FUNCTION__, param1, param2);
	return param1+param2;
}

context_desc_t testslab2_entry3(u32 cpu_index, bool isbsp, u32 partition_index){
	context_desc_t ctx;

	_XDPRINTF_("\n%s: Got control: cpu_index=%u, isbsp=%u, partition_index=%u", __FUNCTION__, cpu_index, isbsp, partition_index);
	
	ctx.cpu_desc.cpu_index = cpu_index;
	ctx.cpu_desc.isbsp = isbsp;
	ctx.partition_desc.partition_index = partition_index;
	
	return ctx;
}	

xc_hypapp_arch_param_t testslab2_entry4(context_desc_t context_desc, xc_hypapp_arch_param_t archparam){
	xc_hypapp_arch_param_t srval;

	_XDPRINTF_("\n%s: Got control: cpu_index=%u, isbsp=%u, partition_index=%u", __FUNCTION__, context_desc.cpu_desc.cpu_index, context_desc.cpu_desc.isbsp, context_desc.partition_desc.partition_index);
	
	srval.operation = archparam.operation;
	srval.param.inforegs.info_vminstr_error = archparam.param.inforegs.info_vminstr_error;
	srval.param.inforegs.info_vmexit_reason = archparam.param.inforegs.info_vmexit_reason;
	srval.param.inforegs.info_vmexit_interrupt_information = archparam.param.inforegs.info_vmexit_interrupt_information;
	srval.param.inforegs.info_vmexit_interrupt_error_code = archparam.param.inforegs.info_vmexit_interrupt_error_code;
	srval.param.inforegs.info_idt_vectoring_information = archparam.param.inforegs.info_idt_vectoring_information;
	srval.param.inforegs.info_idt_vectoring_error_code = archparam.param.inforegs.info_idt_vectoring_error_code;
	srval.param.inforegs.info_vmexit_instruction_length = archparam.param.inforegs.info_vmexit_instruction_length;
	srval.param.inforegs.info_vmx_instruction_information = archparam.param.inforegs.info_vmx_instruction_information;
	srval.param.inforegs.info_exit_qualification = archparam.param.inforegs.info_exit_qualification;
	srval.param.inforegs.info_io_rcx = archparam.param.inforegs.info_io_rcx;
	srval.param.inforegs.info_io_rsi = archparam.param.inforegs.info_io_rsi;
	srval.param.inforegs.info_io_rdi = archparam.param.inforegs.info_io_rdi;
	srval.param.inforegs.info_io_rip = archparam.param.inforegs.info_io_rip;
	srval.param.inforegs.info_guest_linear_address = archparam.param.inforegs.info_guest_linear_address;
	srval.param.inforegs.info_guest_paddr_full = archparam.param.inforegs.info_guest_paddr_full;
	
	return srval;
}


XMHF_SLAB_DEF(testslab2)
