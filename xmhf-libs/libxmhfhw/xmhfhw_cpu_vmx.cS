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

//xmhfhw_cpu_vmx: CPU VMX functions
//author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfhw.h>
#include <xmhf-debug.h>


__attribute__((naked)) bool __vmx_vmxon(u64 vmxonregion_paddr){
/*		u32 retval=0;

		asm volatile( "vmxon %1 \n"
				 "jbe vmfail \n"
				 "movl $0x1, %%eax \n"
				 "movl %%eax, %0 \n"
				 "jmp vmsuccess \n"
				 "vmfail: \n"
				 "movl $0x0, %%eax \n"
				 "movl %%eax, %0 \n"
				 "vmsuccess: \n"
		   : "=g" (retval)
		   : "m"(vmxonregion_paddr)
		   : "eax");

		if(!retval)
            return false;
        else
            return true;
*/

    asm volatile ("vmxon 0x4(%esp) \r\n");
	asm volatile ("jbe vo_fail \r\n");
    asm volatile ("movl $0x1, %eax \r\n");
	asm volatile ("jmp vo_success \r\n");
    asm volatile ("vo_fail: \r\n");
    asm volatile ("movl $0x0, %eax \r\n");
	asm volatile ("vo_success: \r\n");
    asm volatile ("ret \r\n");


}


/*
x86_64
void xmhfhw_cpu_x86vmx_vmwrite(u64 encoding, u64 value){
  asm volatile ("vmwrite %1, %0 \r\n" :: "r"(encoding  & 0x00000000FFFFFFFFULL), "r"(value) : "cc");
}

u64 xmhfhw_cpu_x86vmx_vmread(u64 encoding){
    u64 __value=0;
    asm volatile("vmread %1, %0 \r\n" : "=r"(__value) : "r"(encoding  & 0x00000000FFFFFFFFULL) : "cc");
    return __value;
}
*/


__attribute__((naked)) void xmhfhw_cpu_x86vmx_vmwrite(u32 encoding, u32 value){
  asm volatile ("movl 0x4(%esp), %ecx \r\n");
  asm volatile ("movl 0x8(%esp), %eax \r\n");
  //asm volatile ("vmwrite %1, %0 \r\n" :: "r"(encoding), "r"(value) : "cc");
  asm volatile ("vmwrite %eax, %ecx \r\n");
  asm volatile ("ret \r\n");
}

__attribute__((naked)) u32 xmhfhw_cpu_x86vmx_vmread(u32 encoding){
/*    u32 __value;
    asm volatile("vmread %1, %0 \r\n" : "=r"(__value) : "r"(encoding) : "cc");
    return __value;*/
    asm volatile ("movl 0x4(%esp), %ecx \r\n");
    asm volatile ("vmread %ecx, %eax\r\n");
    asm volatile ("ret \r\n");
}


__attribute__((naked)) u32 __vmx_vmclear(u64 vmcs){
/*  u32 status;
  __asm__("vmclear %1			\r\n"
	   	"jbe	1f    		\r\n"
      "movl $1, %%eax \r\n"
      "jmp  2f  \r\n"
      "1: movl $0, %%eax \r\n"
      "2: movl %%eax, %0 \r\n"
    : "=m" (status)
    : "m"(vmcs)
    : "%eax"
  );
  return status;
*/

    asm volatile ("vmclear 0x4(%esp) \r\n");
    asm volatile ("jbe vmclear_error \r\n");
    asm volatile ("movl $1, %eax \r\n");
    asm volatile ("jmp vmclear_done \r\n");
    asm volatile ("vmclear_error: \r\n");
    asm volatile ("mov $0, %eax \r\n");
    asm volatile ("vmclear_done: \r\n");
    asm volatile ("ret \r\n");

}

__attribute__((naked)) u32 __vmx_vmptrld(u64 vmcs){
/*  u32 status;
  __asm__("vmptrld %1			\r\n"
	   	"jbe	1f    		\r\n"
      "movl $1, %%eax \r\n"
      "jmp  2f  \r\n"
      "1: movl $0, %%eax \r\n"
      "2: movl %%eax, %0 \r\n"
    : "=m" (status)
    : "m"(vmcs)
    : "%eax"
  );
  return status;*/

  asm volatile ("vmptrld 0x4(%esp) \r\n");
  asm volatile ("jbe vptrld_error \r\n");
asm volatile ("movl $1, %eax \r\n");
asm volatile ("jmp vptrld_done \r\n");
asm volatile ("vptrld_error: \r\n");
asm volatile ("movl $0, %eax \r\n");
asm volatile ("vptrld_done: \r\n");
asm volatile ("ret \r\n");


}

// VMX instruction INVVPID
//		Invalidate Translations Based on VPID
// INVVPID r32, m128
//returns 1 on success, 0 on failure


__attribute__((naked)) u32 __vmx_invvpid(int invalidation_type, //0x14
                  u32 vpid,              //0x18
                  u32 linearaddress){    //0x1C
/*	//return status (1 or 0)
	u32 status;

	//invvpid descriptor
	struct {
		u64 vpid 	 : 16;
		u64 reserved : 48;
		u64 linearaddress;
    } invvpiddescriptor = { vpid, 0, linearaddress };

	//issue invvpid instruction
	//note: GCC does not seem to support this instruction directly
	//so we encode it as hex
	__asm__(".byte 0x66, 0x0f, 0x38, 0x81, 0x08 \r\n"
          "movl $1, %%eax \r\n"
		  "ja	1f    	  \r\n"
		  "movl $0, %%eax \r\n"
		  "1: movl %%eax, %0 \r\n"
    : "=m" (status)
    : "a"(&invvpiddescriptor), "c"(invalidation_type)
	: "cc", "memory");

	return status;*/

    asm volatile ("subl 0x10, %esp \r\n");

    asm volatile ("xorl %eax, %eax \r\n");
    asm volatile ("movw 0x18(%esp), %ax \r\n");
    asm volatile ("movl %eax, (%esp) \r\n");
    asm volatile ("movl $0, 0x4(%esp) \r\n");
    asm volatile ("movl 0x1C(%esp), %eax \r\n");
    asm volatile ("movl %eax, 0x8(%esp) \r\n");
    asm volatile ("movl $0, 0xC(%esp) \r\n");

    asm volatile ("movl 0x14(%esp), %ecx \r\n");

    asm volatile ("invvpid (%esp), %ecx\r\n");

    asm volatile ("movl $1, %eax \r\n");
    asm volatile ("ja vinvpid_success \r\n");
    asm volatile ("movl $0, %eax \r\n");
    asm volatile ("vinvpid_success: \r\n");

    asm volatile ("addl 0x10, %esp \r\n");
    asm volatile ("ret \r\n");

}



// VMX instruction INVEPT
//		Invalidate Translations Derived from EPT


__attribute__((naked)) void __vmx_invept(u64 invalidation_type, u64 eptp){
/*	//invept descriptor
	struct {
		u64 eptp;
		u64 reserved;
    } __attribute__((packed)) __inveptdescriptor = { eptp, 0};

	//issue invept instruction
	asm volatile("invept %0, %1 \r\n" ::"m" (__inveptdescriptor), "r" (invalidation_type):"cc");
*/
    asm volatile ("subl 0x10, %esp \r\n");
    asm volatile ("movl 0x14(%esp), %edx \r\n"); //edx = invalidation_type
    asm volatile ("movl 0x1C(%esp), %eax \r\n");
    asm volatile ("movl %eax, (%esp) \r\n");
    asm volatile ("movl 0x20(%esp), %eax \r\n");
    asm volatile ("movl %eax, 0x4(%esp) \r\n");
    asm volatile ("movl $0, 0x8(%esp) \r\n");
    asm volatile ("movl $0, 0xC(%esp) \r\n");
    asm volatile ("invept (%esp), %edx \r\n");
    asm volatile ("addl 0x10, %esp \r\n");
    asm volatile ("ret \r\n");
}

