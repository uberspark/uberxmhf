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

// XMHF core initialization boostrap (init-bs) entry module
// author: amit vasudevan (amitvasudevan@acm.org)

//---includes-------------------------------------------------------------------
#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xc-initbs.h>

#define __XMHF_SLAB_CALLER_INDEX__	XMHF_SLAB_INITBS_INDEX
#include <testslab1.h>
#include <testslab2.h>
#include <xc-init.h>
#undef __XMHF_SLAB_CALLER_INDEX__

void xmhf_runtime_entry(void){

	//setup debugging	
	//xmhf_debug_init((char *)&xcbootinfo->debugcontrol_buffer);
	//_XDPRINTF_("\nxmhf-core: starting...");

   
  	//initialize basic platform elements
	//xmhf_baseplatform_initialize();

	//setup XMHF exception handler component
	//xmhf_xcphandler_initialize();

	#if defined (__DMAP__)
	xmhf_dmaprot_reinitialize();
	#endif

	//initialize richguest
	//xmhf_richguest_initialize();




	//setup slab page tables and turn on paging
	//xmhf_apihub_initialize();


/*	//[test] testslab1
	{
			//extern slab_header_t _test_slab_header;
			xc_hypapp_arch_param_t ap_input, ap_output;
			context_desc_t ctx;
			u32 value;
			
			//invoke slab interface
			_XDPRINTF_("\n%s: preparing to invoke entry_0, esp=%x", __FUNCTION__, read_esp());
			XMHF_SLAB_CALL(entry_0());
			_XDPRINTF_("\n%s: came back from entry_0, esp=%x", __FUNCTION__, read_esp());

			_XDPRINTF_("\n%s: preparing to invoke entry_1, esp=%x", __FUNCTION__, read_esp());
			value=XMHF_SLAB_CALL(entry_1(5, 3));
			_XDPRINTF_("\n%s: came back from entry_1, esp=%x", __FUNCTION__, read_esp());
			_XDPRINTF_("\n%s: came back from entry_1, value=%u", __FUNCTION__, value);
						
			//_XDPRINTF_("%s: doing int3\n", __FUNCTION__);
			//asm volatile("int $0x03 \r\n");
			//_XDPRINTF_("%s: doing int3\n", __FUNCTION__);
			//asm volatile("int $0x03 \r\n");
			//_XDPRINTF_("%s: doing int3\n", __FUNCTION__);
			//asm volatile("int $0x03 \r\n");
			//_XDPRINTF_("%s: int3 test done\n", __FUNCTION__);
			
			
			_XDPRINTF_("%s: preparing to invoke entry_2, esp=%x\n", __FUNCTION__, read_esp());
			ctx= XMHF_SLAB_CALL(entry_2(2048, true, 4096));
			_XDPRINTF_("\n%s: came back from entry_2, esp=%x", __FUNCTION__, read_esp());
			_XDPRINTF_("\n%s: ctx: cpu_index=%u, isbsp=%u, partition_index=%u", __FUNCTION__, ctx.cpu_desc.cpu_index, ctx.cpu_desc.isbsp, ctx.partition_desc.partition_index);
			
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
			ap_output = XMHF_SLAB_CALL(entry_3(ctx, ap_input));			
			_XDPRINTF_("\n%s: came back from entry_3, esp=%x", __FUNCTION__, read_esp());
			_XDPRINTF_("\nap_output.param.inforegs.info_vminstr_error                  %u",  ap_output.param.inforegs.info_vminstr_error                ); 
			_XDPRINTF_("\nap_output.param.inforegs.info_vmexit_reason                  %u",  ap_output.param.inforegs.info_vmexit_reason                ); 
			_XDPRINTF_("\nap_output.param.inforegs.info_vmexit_interrupt_information   %u",  ap_output.param.inforegs.info_vmexit_interrupt_information ); 
			_XDPRINTF_("\nap_output.param.inforegs.info_vmexit_interrupt_error_code    %u",  ap_output.param.inforegs.info_vmexit_interrupt_error_code  ); 
			_XDPRINTF_("\nap_output.param.inforegs.info_idt_vectoring_information      %u",  ap_output.param.inforegs.info_idt_vectoring_information    ); 
			_XDPRINTF_("\nap_output.param.inforegs.info_idt_vectoring_error_code       %u",  ap_output.param.inforegs.info_idt_vectoring_error_code     ); 
			_XDPRINTF_("\nap_output.param.inforegs.info_vmexit_instruction_length      %u",  ap_output.param.inforegs.info_vmexit_instruction_length    ); 
			_XDPRINTF_("\nap_output.param.inforegs.info_vmx_instruction_information    %u",  ap_output.param.inforegs.info_vmx_instruction_information  ); 
			_XDPRINTF_("\nap_output.param.inforegs.info_exit_qualification             %llu",  ap_output.param.inforegs.info_exit_qualification           ); 
			_XDPRINTF_("\nap_output.param.inforegs.info_io_rcx                         %llu",  ap_output.param.inforegs.info_io_rcx                       ); 
			_XDPRINTF_("\nap_output.param.inforegs.info_io_rsi                         %llu",  ap_output.param.inforegs.info_io_rsi                       ); 
			_XDPRINTF_("\nap_output.param.inforegs.info_io_rdi                         %llu",  ap_output.param.inforegs.info_io_rdi                       ); 
			_XDPRINTF_("\nap_output.param.inforegs.info_io_rip                         %llu",  ap_output.param.inforegs.info_io_rip                       ); 
			_XDPRINTF_("\nap_output.param.inforegs.info_guest_linear_address           %llu",  ap_output.param.inforegs.info_guest_linear_address         ); 
			_XDPRINTF_("\nap_output.param.inforegs.info_guest_paddr_full               %llu",  ap_output.param.inforegs.info_guest_paddr_full             ); 

	}


	//testslab2
	{
			//invoke testslab 2 interface
			_XDPRINTF_("\n%s: preparing to invoke testslab2_entry_0, esp=%x", __FUNCTION__, read_esp());
			XMHF_SLAB_CALL(testslab2_entry_0());
			_XDPRINTF_("\n%s: came back from testslab2_entry_0, esp=%x", __FUNCTION__, read_esp());
	}

	
	_XDPRINTF_("\nXMHF Tester Finished!\n");
	_XDPRINTF_("\n\n");
	HALT();
*/

	_XDPRINTF_("proceeding to initialize exception handling...\n");
	//setup platform exception handling
	xcinitbs_arch_initialize_exception_handling();
	_XDPRINTF_("exception handling initialized.\n");



	//_XDPRINTF_("\nXMHF Tester Finished!\n\n");
	//HALT();

	//initialize base platform with SMP 
	xmhf_baseplatform_smpinitialize();

	_XDPRINTF_("\nRuntime: We should NEVER get here!");
	HALT_ON_ERRORCOND(0);
}

///////
XMHF_SLAB("initbs")

XMHF_SLAB_DEFINTERFACE(
	XMHF_SLAB_DEFEXPORTFN(xmhf_runtime_entry, XMHF_SLAB_INITBS_FNXMHFRUNTIMEENTRY, XMHF_SLAB_FN_RETTYPE_NORMAL)
)

//XMHF_SLAB_DEFINTERFACEBARE(
//	xmhf_runtime_entry
//)
