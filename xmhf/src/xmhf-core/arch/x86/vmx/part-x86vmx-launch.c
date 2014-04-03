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

// launch a particular partition/CPU within a hardware container
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h> 


//----------------------------------------------------------------------
// start HVM on a given physical core
// on success: this function will not return
// on failure: 1 if a valid error code is present, 0 if no error code, 
// 2 if invalid error info. (should never happen)
//----------------------------------------------------------------------
u32 __vmx_start_hvm(void) __attribute__ ((naked)) {
	//save GPRs
	asm volatile ("pushal\r\n");
   
	//real-mode setup just like the BIOS
	asm volatile ("movl $0x0, %eax\r\n");
	asm volatile ("movl $0x0, %ebx\r\n");
	asm volatile ("movl $0x0, %ecx\r\n");
	asm volatile ("movl $0x80, %edx\r\n");
	asm volatile ("movl $0x0, %ebp\r\n");
	asm volatile ("movl $0x0, %esi\r\n");
	asm volatile ("movl $0x0, %edi\r\n");

	//attempt to instantiate the HVM
	asm volatile ("vmlaunch\r\n");
	 
	//if we get here then some error happened during the launch
	
	//restore stack frame for a return from this procedure
	asm volatile ("popal\r\n");	

	//there are two possible causes of failure, VMFailInvalid or
	//VMFailValid (VM instruction error field contains the error code)
	//check which happened and return appropriate value in eax 
	asm volatile ("jc __vmx_start_hvm_failinvalid\r\n"
				  "jnz	__vmx_start_hvm_undefinedimplementation	\r\n"
				  "movl $0x1, %eax\r\n"
				  "ret\r\n"					//return 1 as we have error code
				  "__vmx_start_hvm_undefinedimplementation:\r\n"
				  "movl $0x2, %eax\r\n"		//violation of VMLAUNCH specs., handle it anyways
				  "ret\r\n"
				  "__vmx_start_hvm_failinvalid:\r\n"
				  "xorl %eax, %eax\r\n"		//return 0 as we have no error code available
				  "ret\r\n"
	);

}
