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
#include <xmhf-core.h> 

#include <xc-initbs.h>

#define __XMHF_SLAB_CALLER_INDEX__	XMHF_SLAB_INITBS_INDEX
#include <xmhf-slab-implib.h>
#include <xc-init.h>
#undef __XMHF_SLAB_CALLER_INDEX__

void xmhf_runtime_entry(void){

	//setup debugging	
	xmhf_debug_init((char *)&xcbootinfo->debugcontrol_buffer);
	printf("\nxmhf-core: starting...");

    //[debug] dump E820
 	#ifndef __XMHF_VERIFICATION__
 	printf("\nNumber of E820 entries = %u", xcbootinfo->memmapinfo_numentries);
	{
		int i;
		for(i=0; i < (int)xcbootinfo->memmapinfo_numentries; i++){
			printf("\n0x%08x%08x, size=0x%08x%08x (%u)", 
			  xcbootinfo->memmapinfo_buffer[i].baseaddr_high, xcbootinfo->memmapinfo_buffer[i].baseaddr_low,
			  xcbootinfo->memmapinfo_buffer[i].length_high, xcbootinfo->memmapinfo_buffer[i].length_low,
			  xcbootinfo->memmapinfo_buffer[i].type);
		}
  	}
	#endif //__XMHF_VERIFICATION__

  	//initialize basic platform elements
	xmhf_baseplatform_initialize();

	//setup XMHF exception handler component
	//xmhf_xcphandler_initialize();

	#if defined (__DMAP__)
	xmhf_dmaprot_reinitialize();
	#endif

	//initialize richguest
	//xmhf_richguest_initialize();


	//print out slab table
	{
			u32 i;
			
			for(i=0; i < XMHF_SLAB_NUMBEROFSLABS; i++){
				printf("\nslab %u: dumping slab header", i);
				printf("\n	slab_index=%u", _slab_table[i].slab_index);
				printf("\n	slab_macmid=%08x", _slab_table[i].slab_macmid);
				printf("\n	slab_privilegemask=%08x", _slab_table[i].slab_privilegemask);
				printf("\n	slab_tos=%08x", _slab_table[i].slab_tos);
				printf("\n  slab_rodata(%08x-%08x)", _slab_table[i].slab_rodata.start, _slab_table[i].slab_rodata.end);
				printf("\n  slab_rwdata(%08x-%08x)", _slab_table[i].slab_rwdata.start, _slab_table[i].slab_rwdata.end);
				printf("\n  slab_code(%08x-%08x)", _slab_table[i].slab_code.start, _slab_table[i].slab_code.end);
				printf("\n  slab_stack(%08x-%08x)", _slab_table[i].slab_stack.start, _slab_table[i].slab_stack.end);
				//printf("\n  slab_trampoline(%08x-%08x)", _slab_table[i].slab_trampoline.start, _slab_table[i].slab_trampoline.end);
				printf("\n  slab_entrycr3=%08x", _slab_table[i].entry_cr3);
			}
	}


	//setup slab page tables and turn on paging
	xmhf_apihub_initialize();


	/*//[test] slab
	{
			//extern slab_header_t _test_slab_header;
			xc_hypapp_arch_param_t ap_input, ap_output;
			context_desc_t ctx;
			u32 value;
			
			//invoke slab interface
			printf("\n%s: preparing to invoke entry_0, esp=%x", __FUNCTION__, read_esp());
			XMHF_SLAB_CALL(entry_0());
			printf("\n%s: came back from entry_0, esp=%x", __FUNCTION__, read_esp());

			printf("\n%s: preparing to invoke entry_1, esp=%x", __FUNCTION__, read_esp());
			value=XMHF_SLAB_CALL(entry_1(5, 3));
			printf("\n%s: came back from entry_1, esp=%x", __FUNCTION__, read_esp());
			printf("\n%s: came back from entry_1, value=%u", __FUNCTION__, value);
						
			//printf("%s: doing int3\n", __FUNCTION__);
			//asm volatile("int $0x03 \r\n");
			//printf("%s: doing int3\n", __FUNCTION__);
			//asm volatile("int $0x03 \r\n");
			//printf("%s: doing int3\n", __FUNCTION__);
			//asm volatile("int $0x03 \r\n");
			//printf("%s: int3 test done\n", __FUNCTION__);
			
			
			printf("%s: preparing to invoke entry_2, esp=%x\n", __FUNCTION__, read_esp());
			ctx= XMHF_SLAB_CALL(entry_2(2048, true, 4096));
			printf("\n%s: came back from entry_2, esp=%x", __FUNCTION__, read_esp());
			printf("\n%s: ctx: cpu_index=%u, isbsp=%u, partition_index=%u", __FUNCTION__, ctx.cpu_desc.cpu_index, ctx.cpu_desc.isbsp, ctx.partition_desc.partition_index);
			
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

			printf("\n%s: preparing to invoke entry_3, esp=%x", __FUNCTION__, read_esp());
			ap_output = XMHF_SLAB_CALL(entry_3(ctx, ap_input));			
			printf("\n%s: came back from entry_3, esp=%x", __FUNCTION__, read_esp());
			printf("\nap_output.param.inforegs.info_vminstr_error                  %u",  ap_output.param.inforegs.info_vminstr_error                ); 
			printf("\nap_output.param.inforegs.info_vmexit_reason                  %u",  ap_output.param.inforegs.info_vmexit_reason                ); 
			printf("\nap_output.param.inforegs.info_vmexit_interrupt_information   %u",  ap_output.param.inforegs.info_vmexit_interrupt_information ); 
			printf("\nap_output.param.inforegs.info_vmexit_interrupt_error_code    %u",  ap_output.param.inforegs.info_vmexit_interrupt_error_code  ); 
			printf("\nap_output.param.inforegs.info_idt_vectoring_information      %u",  ap_output.param.inforegs.info_idt_vectoring_information    ); 
			printf("\nap_output.param.inforegs.info_idt_vectoring_error_code       %u",  ap_output.param.inforegs.info_idt_vectoring_error_code     ); 
			printf("\nap_output.param.inforegs.info_vmexit_instruction_length      %u",  ap_output.param.inforegs.info_vmexit_instruction_length    ); 
			printf("\nap_output.param.inforegs.info_vmx_instruction_information    %u",  ap_output.param.inforegs.info_vmx_instruction_information  ); 
			printf("\nap_output.param.inforegs.info_exit_qualification             %llu",  ap_output.param.inforegs.info_exit_qualification           ); 
			printf("\nap_output.param.inforegs.info_io_rcx                         %llu",  ap_output.param.inforegs.info_io_rcx                       ); 
			printf("\nap_output.param.inforegs.info_io_rsi                         %llu",  ap_output.param.inforegs.info_io_rsi                       ); 
			printf("\nap_output.param.inforegs.info_io_rdi                         %llu",  ap_output.param.inforegs.info_io_rdi                       ); 
			printf("\nap_output.param.inforegs.info_io_rip                         %llu",  ap_output.param.inforegs.info_io_rip                       ); 
			printf("\nap_output.param.inforegs.info_guest_linear_address           %llu",  ap_output.param.inforegs.info_guest_linear_address         ); 
			printf("\nap_output.param.inforegs.info_guest_paddr_full               %llu",  ap_output.param.inforegs.info_guest_paddr_full             ); 

	}
	
	printf("\nXMHF Tester Finished!\n");
	printf("\n\n");
	HALT();*/


	printf("proceeding to initialize exception handling...\n");
	//setup platform exception handling
	xcinitbs_arch_initialize_exception_handling();
	printf("exception handling initialized.\n");



	//printf("\nXMHF Tester Finished!\n\n");
	//HALT();

	//initialize base platform with SMP 
	xmhf_baseplatform_smpinitialize();

	printf("\nRuntime: We should NEVER get here!");
	HALT_ON_ERRORCOND(0);
}

///////
XMHF_SLAB("initbs")

//TODO: make this normal interface when we move page-table initialization into primeon slab
//primeon slab will then invoke this via its trampoline
//XMHF_SLAB_DEFINTERFACE(
//	XMHF_SLAB_DEFEXPORTFN(xmhf_runtime_entry, XMHF_SLAB_INITBS_FNXMHFRUNTIMEENTRY, XMHF_SLAB_FN_RETTYPE_NORMAL)
//)

XMHF_SLAB_DEFINTERFACEBARE(
	xmhf_runtime_entry
)
