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

//////
XMHF_SLAB_DEFENTRYSTUB(testslab1)


/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

slab_retval_t testslab1_interface(u64 src_slabid, u64 dst_slabid, u64 call_type,
                                  u64 rsv0, u64 rsv1, slab_params_t slab_params){
	slab_retval_t srval;

	_XDPRINTF_("%s: Got control: src_slabid=%u, dst_slabid=%u\n",
                __FUNCTION__, src_slabid, dst_slabid);

	_XDPRINTF_("%s: slab_params.input_u64[0]=%016llx\n",
                __FUNCTION__, slab_params.input_u64[0]);


    srval.retval_u64 = 0xAA;
    return srval;
}

/*slab_retval_t testslab1_interface(u32 src_slabid, u32 dst_slabid, u32 fn_id, u32 fn_paramsize, ...){
	slab_retval_t srval;
	xc_hypapp_arch_param_t ap_input;

	_XDPRINTF_("%s: Got control: src_slabid=%u, dst_slabid=%u, fn_id=%u\n", __FUNCTION__, src_slabid, dst_slabid, fn_id);

	_XDPRINTF_("%s: proceeding to invoke testslab2, entry1 subinterface, TOS=%08x\n", __FUNCTION__, read_esp());
	srval = XMHF_SLAB_CALL_P2P(testslab2, XMHF_SLAB_TESTSLAB1_INDEX, XMHF_SLAB_TESTSLAB2_INDEX, XMHF_SLAB_TESTSLAB2_FNENTRY1, XMHF_SLAB_TESTSLAB2_FNENTRY1_SIZE);
	_XDPRINTF_("%s: came back, TOS=%08x\n", __FUNCTION__, read_esp());

	_XDPRINTF_("%s: proceeding to invoke testslab2, entry2 subinterface, TOS=%08x\n", __FUNCTION__, read_esp());
	srval = XMHF_SLAB_CALL_P2P(testslab2, XMHF_SLAB_TESTSLAB1_INDEX, XMHF_SLAB_TESTSLAB2_INDEX, XMHF_SLAB_TESTSLAB2_FNENTRY2, XMHF_SLAB_TESTSLAB2_FNENTRY2_SIZE, 5, 8);
	_XDPRINTF_("%s: came back, result=%u, TOS=%08x\n", __FUNCTION__, srval.retval_u32, read_esp());


	_XDPRINTF_("%s: preparing to invoke testslab2, entry3 subinterface, TOS=%08x\n", __FUNCTION__, read_esp());
	srval= XMHF_SLAB_CALL_P2P(testslab2, XMHF_SLAB_TESTSLAB1_INDEX, XMHF_SLAB_TESTSLAB2_INDEX, XMHF_SLAB_TESTSLAB2_FNENTRY3, XMHF_SLAB_TESTSLAB2_FNENTRY3_SIZE, 2048, true, 4096);
	_XDPRINTF_("%s: came back, ctx: cpu_index=%u, isbsp=%u, partition_index=%u, TOS=%08x", __FUNCTION__, srval.retval_context_desc.cpu_desc.cpu_index, srval.retval_context_desc.cpu_desc.isbsp, srval.retval_context_desc.partition_desc.partition_index, read_esp());


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

	_XDPRINTF_("%s: preparing to invoke testslab2, entry4 subinterface, TOS=%08x\n", __FUNCTION__, read_esp());
	srval= XMHF_SLAB_CALL_P2P(testslab2, XMHF_SLAB_TESTSLAB1_INDEX, XMHF_SLAB_TESTSLAB2_INDEX, XMHF_SLAB_TESTSLAB2_FNENTRY4, XMHF_SLAB_TESTSLAB2_FNENTRY4_SIZE, srval.retval_context_desc, ap_input);
	_XDPRINTF_("%s: came back, TOS=%08x", __FUNCTION__, read_esp());

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

	_XDPRINTF_("\nXMHF Tester Finished!\n");
	_XDPRINTF_("\n\n");
	HALT();

	return srval;
}
*/





