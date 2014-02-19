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

//core/hypapp API/callbacks low-level stubs
//author: amit vasudevan (amitvasudevan@acm.org)

//----------------------------------------------------------------------
//globals referenced
	.extern hypapp_cbhub_pc
	.extern hypapp_tos
	.extern xmhf_apihub_arch_fromhypapp
	.extern core_ptba
	.extern hypapp_ptba

//----------------------------------------------------------------------
// code
// 

.section .text

//void xmhf_apihub_arch_tohypapp(u32 hypappcallnum)
.global xmhf_apihub_arch_tohypapp
xmhf_apihub_arch_tohypapp:
	pushal							//save all GPRs

	pushl $backfromhypapp			//push return EIP on top of stack
	
	movl 40(%esp), %esi				//esi = hypappcallnum
	
	movl $0x0, %edx					//store SYSENTER CS  
	movl $(__CS_CPL0), %eax
	movl $(IA32_SYSENTER_CS_MSR), %ecx
	wrmsr
	
	movl $0x0, %edx					//store SYSENTER ESP 
	movl %esp, %eax
	movl $(IA32_SYSENTER_ESP_MSR), %ecx
	wrmsr
	
	movl $0x0, %edx					//store SYSENTER EIP
	movl $xmhf_apihub_arch_fromhypapp_stub, %eax			
	movl $(IA32_SYSENTER_EIP_MSR), %ecx
	wrmsr

	movl hypapp_tos, %ecx			//store SYSEXIT ESP
								
	movl hypapp_cbhub_pc, %edx		//store SYSEXIT EIP
				
	movl hypapp_ptba, %eax			//load hypapp page tables
	movl %eax, %cr3			
				
	movw $(__DS_CPL3), %ax			//load hypapp DS segment selector
	movw %ax, %ds					//SS and CS loaded by sysexit below
	
	sysexit							//invoke hypapp callback

backfromhypapp:
	popal												// restore all GPRs
	ret


.global xmhf_apihub_arch_fromhypapp_stub
xmhf_apihub_arch_fromhypapp_stub:
	cmpl $(XMHF_APIHUB_COREAPI_HYPAPPCBRETURN), %esi	//check if it is return from hyppapp callback
	jne coreapicall
	
	//return from hypapp callback
	movl core_ptba, %eax								//load core page tables
	movl %eax, %cr3			

	movw	$(__DS_CPL0), %ax							//switch to ring-0 DS
	movw	%ax, %ds

	ret													// this will pop the return EIP from top of stack
														// and resume execution at backfromhypapp above

	int $0x03											// we should never get here
	hlt

coreapicall:											//this is a regular core API call
	pushal												//save all GPRs

	movl core_ptba, %eax								//load core page tables
	movl %eax, %cr3			

	movw	$(__DS_CPL0), %ax							//switch to ring-0 DS
	movw	%ax, %ds
	
	pushl	%esi
	call xmhf_apihub_arch_fromhypapp					//invoke C land core API hub handler
	addl $0x4, %esp
	
	movw $(__DS_CPL3), %ax								//load hypapp DS segment selector
	movw %ax, %ds										//SS and CS loaded by sysexit below

	movl hypapp_ptba, %eax								//load hypapp page tables
	movl %eax, %cr3			

	popal												//restore all GPRS
	sysexit												//exit back to hypapp
	
	int $0x03
	hlt


//----------------------------------------------------------------------
// data
// 

.section .data


//----------------------------------------------------------------------
// stack
// 

.section .stack

