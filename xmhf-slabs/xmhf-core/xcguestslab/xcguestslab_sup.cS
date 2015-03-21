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
#include <xmhfhicslab.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <xcguestslab.h>


void xcguestslab_do_vmcall(void){
    u32 magic = 0xAABBCCDDUL;

    _XDPRINTF_("%s: Going for VMCALL, magic=%08x\n",
                __FUNCTION__, magic);

    asm volatile(
        "movl %0, %%eax \r\n"
        "vmcall \r\n"
        "movl %%eax, %0 \r\n"
        :
        : "m" (magic)
        : "eax"
    );

    _XDPRINTF_("%s: Came back from VMCALL, magic=%08x\n",
                __FUNCTION__, magic);


}











//////////////////////////////////////////////////////////////////////////////
// xhapprovexec test

__attribute__((aligned(4096))) void _xcguestslab_do_testxhapprovexec_functoprotect(void){

    asm volatile (
        ".fill 4096, 1, 0x90 \r\n"
    :
    :
    :
    );

}








//////

u32 _xcguestslab_vmcall(u32 eax, u32 ebx, u32 edx){
    u32 result;

    //register syscall handler
    asm volatile(
        "movl %1, %%eax \r\n"
        "movl %2, %%edx \r\n"
        "movl %3, %%ebx \r\n"
        "vmcall \r\n"
        "movl %%eax, %0 \r\n"
        : "=r" (result)
        : "g" (eax),
          "g" (edx),
          "g" (ebx)
        : "eax", "ebx", "edx"
    );

    return result;
}







//////
// syscalllog

void _xcguestslab_do_testxhsyscalllog_sysenterhandler(void){

    asm volatile(
         "sysexit \r\n"
        :
        :
        :
    );

}


void _xcguestslab_do_testxhsyscalllog_loadGDT(u32 addr_gdt, u32 cs_sel, u32 ds_sel){

    //load GDTR
	asm volatile(
		"lgdt  (%0) \r\n"
		"pushl	%1 \r\n"
		"pushl	$reloadsegs \r\n"
		"lret \r\n"
		"reloadsegs: \r\n"
		"movl	%2, %%eax \r\n"
		"movw	%%ax, %%ds \r\n"
		"movw	%%ax, %%es \r\n"
		"movw	%%ax, %%fs \r\n"
		"movw	%%ax, %%gs \r\n"
		"movw   %%ax, %%ss \r\n"
		: //no outputs
		: "r" (addr_gdt), "r" (cs_sel), "r" (ds_sel)
		: "eax"
	);

}

void  _xcguestslab_do_testxhsyscalllog_setIOPL3(void){

    //set IOPL to CPL-3
	asm volatile(
        "pushfl \r\n"
        "popl %%eax \r\n"
		"orl $0x3000, %%eax \r\n"					// clear flags, but set IOPL=3 (CPL-3)
		"pushl %%eax \r\n"
		"popfl \r\n"
		: //no outputs
		: //no inputs
		: "eax", "cc"
	);


}

void _xcguestslab_do_testxhsyscalllog_switchtoring3(void){
    //switch to ring-3
    asm volatile(
         "movl $1f, %%edx \r\n"
         "movl %%esp, %%ecx \r\n"
         "sysexit \r\n"
         "1: \r\n"
        :
        :
        : "edx", "ecx"
    );
}


void _xcguestslab_do_testxhsyscalllog_invokesyscall(void){
    //invoke sysenter
    asm volatile(
         "movl $1f, %%edx \r\n"
         "movl %%esp, %%ecx \r\n"
         "sysenter \r\n"
         "1: \r\n"
        :
        :
        : "edx", "ecx"
    );
}
