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
#include <xmhf-debug.h>

#include <xcexhub.h>

//////
XMHF_SLAB_EXCEPTION(xcexhub)



/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


static void _xcexhub_unhandled(x86vmx_exception_frame_errcode_t *exframe){
    //dump relevant info
    _XDPRINTF_("exception %x\n", exframe->vector);
    _XDPRINTF_("state dump:\n\n");
    _XDPRINTF_("errorcode=0x%016llx\n", exframe->errorcode);
    _XDPRINTF_("CS:RIP:RFLAGS = 0x%016llx:0x%016llx:0x%016llx\n", exframe->orig_cs, exframe->orig_rip, exframe->orig_rflags);
    _XDPRINTF_("SS:RSP = 0x%016llx:0x%016llx\n", exframe->orig_ss, exframe->orig_rsp);
    //_XDPRINTF_("CR0=0x%016llx, CR2=0x%016llx\n", read_cr0(), read_cr2());
    //_XDPRINTF_("CR3=0x%016llx, CR4=0x%016llx\n", read_cr3(), read_cr4());
    _XDPRINTF_("CS=0x%04x, DS=0x%04x, ES=0x%04x, SS=0x%04x\n", (u16)read_segreg_cs(), (u16)read_segreg_ds(), (u16)read_segreg_es(), (u16)read_segreg_ss());
    _XDPRINTF_("FS=0x%04x, GS=0x%04x\n", (u16)read_segreg_fs(), (u16)read_segreg_gs());
    //_XDPRINTF_("TR=0x%04x\n", (u16)read_tr_sel());
    _XDPRINTF_("RAX=0x%016llx, RBX=0%016llx\n", exframe->rax, exframe->rbx);
    _XDPRINTF_("RCX=0x%016llx, RDX=0%016llx\n", exframe->rcx, exframe->rdx);
    _XDPRINTF_("RSI=0x%016llx, RDI=0%016llx\n", exframe->rsi, exframe->rdi);
    _XDPRINTF_("RBP=0x%016llx, RSP=0%016llx\n", exframe->rbp, exframe->rsp);
    _XDPRINTF_("R8=0x%016llx, R9=0%016llx\n", exframe->r8, exframe->r9);
    _XDPRINTF_("R10=0x%016llx, R11=0%016llx\n", exframe->r10, exframe->r11);
    _XDPRINTF_("R12=0x%016llx, R13=0%016llx\n", exframe->r12, exframe->r13);
    _XDPRINTF_("R14=0x%016llx, R15=0%016llx\n", exframe->r14, exframe->r15);

    ////do a stack dump in the hopes of getting more info.
    //{
    //    u64 i;
    //    u64 stack_start = exframe->orig_rsp;
    //    _XDPRINTF_("\n-----stack dump (8 entries)-----\n");
    //    for(i=stack_start; i < stack_start+(8*sizeof(u64)); i+=sizeof(u64)){
    //        _XDPRINTF_("Stack(0x%016llx) -> 0x%016llx\n", i, *(u64 *)i);
    //    }
    //    _XDPRINTF_("\n-----stack dump end-------------\n");
    //}

}


void xcexhub_interface(slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 src_slabid, u64 cpuid){
    x86vmx_exception_frame_errcode_t *exframe = (x86vmx_exception_frame_errcode_t *)iparams;

	_XDPRINTF_("%s[%u]: Got control: RSP=%016llx\n",
                __FUNCTION__, (u32)cpuid, read_rsp());


   	switch(exframe->vector){
			case 0x3:{
                _xcexhub_unhandled(exframe);
				_XDPRINTF_("%s: exception 3, returning\n", __FUNCTION__);
			}
			break;

			default:{
				_xcexhub_unhandled(exframe);
				_XDPRINTF_("\nHalting System!\n");
				HALT();
			}
	}

    return;
}


