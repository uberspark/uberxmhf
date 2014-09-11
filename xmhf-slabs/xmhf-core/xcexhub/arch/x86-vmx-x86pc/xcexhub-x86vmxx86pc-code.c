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

/*
 * XMHF core exception handling x86-vmx-x86pc arch. backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcapi.h>


__attribute__(( section(".slab_trampoline") )) static void xmhf_xcphandler_arch_unhandled(u64 vector, x86regs64_t *r){
	x86idt64_stackframe_t *exframe = NULL;
    u64 errorcode=0;

    //grab and skip error code on stack if applicable
    //TODO: fixme, this won't hold if we call these exceptions with INT xx since there is no error code pushed
    //in such cases
	if(vector == CPU_EXCEPTION_DF ||
		vector == CPU_EXCEPTION_TS ||
		vector == CPU_EXCEPTION_NP ||
		vector == CPU_EXCEPTION_SS ||
		vector == CPU_EXCEPTION_GP ||
		vector == CPU_EXCEPTION_PF ||
		vector == CPU_EXCEPTION_AC){
		errorcode = *(u64 *)(r->rsp);
		r->rsp += sizeof(u64);
	}

    //get idt stack frame
    exframe = (x86idt64_stackframe_t *)r->rsp;

    //dump relevant info
	_XDPRINTF_("unhandled exception %x, halting!\n", vector);
	_XDPRINTF_("state dump:\n\n");
	_XDPRINTF_("errorcode=0x%016llx\n", errorcode);
	_XDPRINTF_("CS:RIP:RFLAGS = 0x%016llx:0x%016llx:0x%016llx\n", exframe->cs, exframe->rip, exframe->rflags);
	_XDPRINTF_("SS:RSP = 0x%016llx:0x%016llx\n", exframe->ss, exframe->rsp);
	_XDPRINTF_("CR0=0x%016llx, CR2=0x%016llx\n", read_cr0(), read_cr2());
	_XDPRINTF_("CR3=0x%016llx, CR4=0x%016llx\n", read_cr3(), read_cr4());
	_XDPRINTF_("CS=0x%04x, DS=0x%04x, ES=0x%04x, SS=0x%04x\n", (u16)read_segreg_cs(), (u16)read_segreg_ds(), (u16)read_segreg_es(), (u16)read_segreg_ss());
	_XDPRINTF_("FS=0x%04x, GS=0x%04x\n", (u16)read_segreg_fs(), (u16)read_segreg_gs());
	_XDPRINTF_("TR=0x%04x\n", (u16)read_tr_sel());
	_XDPRINTF_("RAX=0x%016llx, RBX=0%016llx\n", r->rax, r->rbx);
	_XDPRINTF_("RCX=0x%016llx, RDX=0%016llx\n", r->rcx, r->rdx);
	_XDPRINTF_("RSI=0x%016llx, RDI=0%016llx\n", r->rsi, r->rdi);
	_XDPRINTF_("RBP=0x%016llx, RSP=0%016llx\n", r->rbp, r->rsp);
	_XDPRINTF_("R8=0x%016llx, R9=0%016llx\n", r->r8, r->r9);
	_XDPRINTF_("R10=0x%016llx, R11=0%016llx\n", r->r10, r->r11);
	_XDPRINTF_("R12=0x%016llx, R13=0%016llx\n", r->r12, r->r13);
	_XDPRINTF_("R14=0x%016llx, R15=0%016llx\n", r->r14, r->r15);

	//do a stack dump in the hopes of getting more info.
	{
		u64 i;
		u64 stack_start = r->rsp;
		_XDPRINTF_("\n-----stack dump (8 entries)-----\n");
		for(i=stack_start; i < stack_start+(8*sizeof(u64)); i+=sizeof(u64)){
			_XDPRINTF_("Stack(0x%016llx) -> 0x%016llx\n", i, *(u64 *)i);
		}
		_XDPRINTF_("\n-----stack dump end-------------\n");
	}
}

//==========================================================================================

//exception handler hub
__attribute__(( section(".slab_trampoline") )) void xmhf_xcphandler_arch_hub(u64 vector, void *exdata){
    x86regs64_t *r = (x86regs64_t *)exdata;

	switch(vector){
			case CPU_EXCEPTION_NMI:{
                _XDPRINTF_("%s: NMI exception, got control...\n", __FUNCTION__);
				XMHF_SLAB_CALL(xc_coreapi_arch_eventhandler_nmiexception(r));
				}
				break;

			case 0x3:{
					xmhf_xcphandler_arch_unhandled(vector, r);
					_XDPRINTF_("\n%s: exception 3, returning", __FUNCTION__);
			}
			break;

			default:{
				xmhf_xcphandler_arch_unhandled(vector, r);
				_XDPRINTF_("\nHalting System!\n");
				HALT();
			}
	}
}


