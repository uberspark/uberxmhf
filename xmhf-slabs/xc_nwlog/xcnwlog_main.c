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
#include <xmhfgeec.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <xc_nwlog.h>

/*
 * xcnwlog_main: main uobj code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


//////
// entry function
//////


//@ ghost bool xcnwlog_methodcall_init = false;
//@ ghost bool xcnwlog_methodcall_logdata = false;
//@ ghost bool xcnwlog_methodcall_invalid = false;
/*@
	requires \valid(sp);
	ensures ( sp->dst_uapifn == XMHFGEEC_SLAB_XC_NWLOG_INITIALIZE) ==> (xcnwlog_methodcall_init == true);
	ensures ( sp->dst_uapifn == XMHFGEEC_SLAB_XC_NWLOG_LOGDATA ) ==> (xcnwlog_methodcall_logdata == true);
	ensures !(
		( sp->dst_uapifn == XMHFGEEC_SLAB_XC_NWLOG_INITIALIZE) ||
		( sp->dst_uapifn == XMHFGEEC_SLAB_XC_NWLOG_LOGDATA )
	) ==> (xcnwlog_methodcall_invalid == true);
@*/
void slab_main(slab_params_t *sp){

	_XDPRINTF_("XCNWLOG[%u]: Got control: src=%u, dst=%u, esp=%08x, eflags=%08x\n",
		(u16)sp->cpuid, sp->src_slabid, sp->dst_slabid, CASM_FUNCCALL(read_esp,CASM_NOPARAM),
			CASM_FUNCCALL(read_eflags, CASM_NOPARAM));

	if(sp->dst_uapifn == XMHFGEEC_SLAB_XC_NWLOG_INITIALIZE){
		xcnwlog_init();
		//@ghost xcnwlog_methodcall_init = true;

	}else if (sp->dst_uapifn == XMHFGEEC_SLAB_XC_NWLOG_LOGDATA){
		xcnwlog_ls_element_t elem;
		elem.logbuf[0] = sp->in_out_params[0]; 		elem.logbuf[1] = sp->in_out_params[0];
		elem.logbuf[2] = sp->in_out_params[0]; 		elem.logbuf[3] = sp->in_out_params[0];
		elem.logbuf[4] = sp->in_out_params[0]; 		elem.logbuf[5] = sp->in_out_params[0];
		elem.logbuf[6] = sp->in_out_params[0]; 		elem.logbuf[7] = sp->in_out_params[0];
		elem.logbuf[8] = sp->in_out_params[0]; 		elem.logbuf[9] = sp->in_out_params[0];
		elem.logbuf[10] = sp->in_out_params[0]; 		elem.logbuf[11] = sp->in_out_params[0];
		elem.logbuf[12] = sp->in_out_params[0]; 		elem.logbuf[13] = sp->in_out_params[0];
		elem.logbuf[14] = sp->in_out_params[0]; 		elem.logbuf[15] = sp->in_out_params[0];
		xcnwlog_logdata(elem);
		//@ghost xcnwlog_methodcall_logdata = true;

        }else {
		_XDPRINTF_("XCNWLOG[%u]: Unknown sub-function %x. Halting!\n",
		    (u16)sp->cpuid, sp->dst_uapifn);
		//@ghost xcnwlog_methodcall_invalid = true;


        }

}







