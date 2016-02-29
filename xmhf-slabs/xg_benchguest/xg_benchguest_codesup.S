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
//#include <xmhfhicslab.h>
//#include <xmhf-debug.h>

//#include <xc.h>
//#include <xcguestslab.h>


    .section .text

    // xhapprovexec test

    .align 2097152
    .global _xcguestslab_do_testxhapprovexec_functoprotect
    _xcguestslab_do_testxhapprovexec_functoprotect:
    ret
    .balign 2097152, 0x90



//////
.global _xcguestslab_vmcall
_xcguestslab_vmcall:
//__attribute__((naked)) u32 _xcguestslab_vmcall(u32 eax, u32 ebx, u32 edx){
pushl %ebx
movl 0x8(%esp), %eax
movl 0x10(%esp), %edx
movl 0xC(%esp), %ebx
vmcall
popl %ebx
ret








//////
// syscalllog
//__attribute__((naked)) void _xcguestslab_do_testxhsyscalllog_sysenterhandler(void){
    .align 2097152
    .global _xcguestslab_do_testxhsyscalllog_sysenterhandler
    _xcguestslab_do_testxhsyscalllog_sysenterhandler:
    sysexit
    hlt
    .balign 2097152, 0x90


//__attribute__((naked)) void _xcguestslab_do_testxhsyscalllog_loadGDT(u32 addr_gdt, u32 cs_sel, u32 ds_sel){
    .global _xcguestslab_do_testxhsyscalllog_loadGDT
    _xcguestslab_do_testxhsyscalllog_loadGDT:
    movl 0x4(%esp), %eax
    lgdt (%eax)
    pushl 0x8(%esp)
    pushl $reload_sregs
    lret
    reload_sregs:
    movl 0xC(%esp), %eax
    movw	%ax, %ds
	movw	%ax, %es
	movw	%ax, %fs
	movw	%ax, %gs
	movw %ax, %ss
    ret


//__attribute__((naked)) void  _xcguestslab_do_testxhsyscalllog_setIOPL3(void){
    .global _xcguestslab_do_testxhsyscalllog_setIOPL3
    _xcguestslab_do_testxhsyscalllog_setIOPL3:
    pushfl
    popl %eax
    orl $0x3000, %eax
    pushl %eax
    popfl
    ret


//__attribute__((naked)) void _xcguestslab_do_testxhsyscalllog_switchtoring3(void){
    .global _xcguestslab_do_testxhsyscalllog_switchtoring3
    _xcguestslab_do_testxhsyscalllog_switchtoring3:
    movl $land_in_ring3, %edx
    movl %esp, %ecx
    sysexit
    land_in_ring3:
    ret



//__attribute__((naked)) void _xcguestslab_do_testxhsyscalllog_invokesyscall(void){
    .global _xcguestslab_do_testxhsyscalllog_invokesyscall
    _xcguestslab_do_testxhsyscalllog_invokesyscall:
    movl $syscall_return, %edx
    movl %esp, %ecx
    sysenter
    syscall_return:
    ret

