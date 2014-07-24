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

#include <xmhf-core.h>

#include <xmhf-slab-implib.h>

/*
 * slab code
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

 
void entry_0(void){
	u32 my_entry_cr3 = _slab_table[0].entry_cr3;
	printf("\n%s: Got control, entry_cr3=%08x", __FUNCTION__, my_entry_cr3);
}
	
u32 entry_1(u32 param1, u32 param2){
	u32 my_entry_cr3 = _slab_table[0].entry_cr3;
	printf("\n%s: Huhu we are here: entry_cr3=%08x", __FUNCTION__, my_entry_cr3);
	printf("\n%s: param1=%u, param2=%u", __FUNCTION__, param1, param2);
	return param1+param2;
}

context_desc_t entry_2(u32 cpu_index, bool isbsp, u32 partition_index){
	context_desc_t ctx;

	printf("\n%s: Got control: cpu_index=%u, isbsp=%u, partition_index=%u", __FUNCTION__, cpu_index, isbsp, partition_index);
	
	ctx.cpu_desc.cpu_index = cpu_index;
	ctx.cpu_desc.isbsp = isbsp;
	ctx.partition_desc.partition_index = partition_index;
	
	return ctx;
}	

xc_hypapp_arch_param_t entry_3(context_desc_t context_desc, xc_hypapp_arch_param_t archparam){
	xc_hypapp_arch_param_t retparam;

	printf("\n%s: Got control: cpu_index=%u, isbsp=%u, partition_index=%u", __FUNCTION__, context_desc.cpu_desc.cpu_index, context_desc.cpu_desc.isbsp, context_desc.partition_desc.partition_index);
	
	retparam.operation = archparam.operation;
	retparam.param.inforegs.info_vminstr_error = archparam.param.inforegs.info_vminstr_error;
	retparam.param.inforegs.info_vmexit_reason = archparam.param.inforegs.info_vmexit_reason;
	retparam.param.inforegs.info_vmexit_interrupt_information = archparam.param.inforegs.info_vmexit_interrupt_information;
	retparam.param.inforegs.info_vmexit_interrupt_error_code = archparam.param.inforegs.info_vmexit_interrupt_error_code;
	retparam.param.inforegs.info_idt_vectoring_information = archparam.param.inforegs.info_idt_vectoring_information;
	retparam.param.inforegs.info_idt_vectoring_error_code = archparam.param.inforegs.info_idt_vectoring_error_code;
	retparam.param.inforegs.info_vmexit_instruction_length = archparam.param.inforegs.info_vmexit_instruction_length;
	retparam.param.inforegs.info_vmx_instruction_information = archparam.param.inforegs.info_vmx_instruction_information;
	retparam.param.inforegs.info_exit_qualification = archparam.param.inforegs.info_exit_qualification;
	retparam.param.inforegs.info_io_rcx = archparam.param.inforegs.info_io_rcx;
	retparam.param.inforegs.info_io_rsi = archparam.param.inforegs.info_io_rsi;
	retparam.param.inforegs.info_io_rdi = archparam.param.inforegs.info_io_rdi;
	retparam.param.inforegs.info_io_rip = archparam.param.inforegs.info_io_rip;
	retparam.param.inforegs.info_guest_linear_address = archparam.param.inforegs.info_guest_linear_address;
	retparam.param.inforegs.info_guest_paddr_full = archparam.param.inforegs.info_guest_paddr_full;
	
	return retparam;
}

///////
XMHF_SLAB("test")

XMHF_SLAB_DEFINTERFACE(
	XMHF_SLAB_DEFEXPORTFN(entry_0, XMHF_SLAB_TEST_FNENTRY0, XMHF_SLAB_FN_RETTYPE_NORMAL)
	XMHF_SLAB_DEFEXPORTFN(entry_1, XMHF_SLAB_TEST_FNENTRY1, XMHF_SLAB_FN_RETTYPE_NORMAL)
	XMHF_SLAB_DEFEXPORTFN(entry_2, XMHF_SLAB_TEST_FNENTRY2, XMHF_SLAB_FN_RETTYPE_AGGREGATE)
	XMHF_SLAB_DEFEXPORTFN(entry_3, XMHF_SLAB_TEST_FNENTRY3, XMHF_SLAB_FN_RETTYPE_AGGREGATE)
)

