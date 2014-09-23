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

// XMHF core API -- x86vmx arch. backend
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcapi.h>
#include <xcihub.h>





///////////////////////////////////////////////////////////////////////////////
//partition related APIs


//----------------------------------------------------------------------
// start HVM on a given physical core
// on success: this function will not return
// on failure: 1 if a valid error code is present, 0 if no error code,
// 2 if invalid error info. (should never happen)
//----------------------------------------------------------------------
//static u32 __vmx_start_hvm(void) __attribute__ ((naked)) {
static u32 __vmx_start_hvm(struct regs x86cpugprs) {
	u32 errorcode;

	asm volatile (
                        "pushq %%rbp \r\n"
                        "pushq %%rdi \r\n"
                        "pushq %%rsi \r\n"
                        "pushq %%rdx \r\n"
                        "pushq %%rcx \r\n"
                        "pushq %%rbx \r\n"
                        "pushq %%rax \r\n"
                        "pushq %%r15 \r\n"
                        "pushq %%r14 \r\n"
                        "pushq %%r13 \r\n"
                        "pushq %%r12 \r\n"
                        "pushq %%r11 \r\n"
                        "pushq %%r10 \r\n"
                        "pushq %%r9 \r\n"
                        "pushq %%r8 \r\n"

                        "movl %1, %%eax\r\n"
                        "movl %2, %%ebx\r\n"
                        "movl %3, %%ecx\r\n"
                        "movl %4, %%edx\r\n"
                        "movl %5, %%esi\r\n"
                        "movl %6, %%edi\r\n"
                        "movl %7, %%ebp\r\n"
                        "vmlaunch\r\n"

                        "popq %%r8 \r\n"
                        "popq %%r9 \r\n"
                        "popq %%r10 \r\n"
                        "popq %%r11 \r\n"
                        "popq %%r12 \r\n"
                        "popq %%r13 \r\n"
                        "popq %%r14 \r\n"
                        "popq %%r15 \r\n"
                        "popq %%rax \r\n"
                        "popq %%rbx \r\n"
                        "popq %%rcx \r\n"
                        "popq %%rdx \r\n"
                        "popq %%rsi \r\n"
                        "popq %%rdi \r\n"
                        "popq %%rbp \r\n"

					"jc __vmx_start_hvm_failinvalid\r\n"
					"jnz	__vmx_start_hvm_undefinedimplementation	\r\n"
					"movl $0x1, %%eax\r\n"		//VMLAUNCH error, XXX: need to read from VM instruction error field in VMCS
					"movl %%eax, %0 \r\n"
					"jmp __vmx_start_continue \r\n"
					"__vmx_start_hvm_undefinedimplementation:\r\n"
					"movl $0x2, %%eax\r\n"		//violation of VMLAUNCH specs., handle it anyways
					"movl %%eax, %0 \r\n"
					"jmp __vmx_start_continue \r\n"
					"__vmx_start_hvm_failinvalid:\r\n"
					"xorl %%eax, %%eax\r\n"		//return 0 as we have no error code available
					"movl %%eax, %0 \r\n"
					"__vmx_start_continue:\r\n"
					: "=g"(errorcode)
					: "g" (x86cpugprs.eax), "g" (x86cpugprs.ebx), "g" (x86cpugprs.ecx), "g" (x86cpugprs.edx), "g" (x86cpugprs.esi), "g" (x86cpugprs.edi), "g" (x86cpugprs.ebp)
					: "eax", "ebx", "ecx", "edx", "esi", "edi", "ebp"
				);

	return errorcode;
}


bool xc_api_partition_arch_startcpu(context_desc_t context_desc){
	u32 errorcode;
    struct regs x86cpugprs;
    xc_hypapp_arch_param_t ap;

    ap = xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS);

	HALT_ON_ERRORCOND( xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_VMCS_LINK_POINTER_FULL) == 0xFFFFFFFFFFFFFFFFULL );

	errorcode=__vmx_start_hvm(ap.param.cpugprs);
	HALT_ON_ERRORCOND(errorcode != 2);	//this means the VMLAUNCH implementation violated the specs.

	switch(errorcode){
			case 0:	//no error code, VMCS pointer is invalid
				_XDPRINTF_("%s: VMLAUNCH error; VMCS pointer invalid?", __FUNCTION__);
				break;
			case 1:{//error code available, so dump it
				u32 code=xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMINSTR_ERROR);
				_XDPRINTF_("\n%s: VMLAUNCH error; code=%x", __FUNCTION__, code);
				break;
			}
	}

	return false;
}








