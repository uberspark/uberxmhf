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
 * sysdata (E820) state uAPI
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>
#include <xmhfgeec.h>

#include <uapi_sysdata.h>



//@ ghost bool usysd_methodcall_e820addentry = false;
//@ ghost bool usysd_methodcall_e820getmaxindex = false;
//@ ghost bool usysd_methodcall_e820getentryforindex = false;
//@ ghost bool usysd_methodcall_invalid = false;
/*@
	requires \valid(sp);
	assigns sp->in_out_params[0..15];
	assigns usysd_methodcall_e820addentry;
	assigns usysd_methodcall_e820getmaxindex;
	assigns usysd_methodcall_e820getentryforindex;
	assigns usysd_methodcall_invalid;
	ensures (sp->dst_uapifn == UXMHF_UAPI_SYSDATA_E820ADDENTRY) ==> (usysd_methodcall_e820addentry == true);
	ensures (sp->dst_uapifn == UXMHF_UAPI_SYSDATA_E820GETMAXINDEX) ==> (usysd_methodcall_e820getmaxindex == true);
	ensures (sp->dst_uapifn == UXMHF_UAPI_SYSDATA_E820GETENTRYFORINDEX) ==> (usysd_methodcall_e820getentryforindex == true);
	ensures !( sp->dst_uapifn == UXMHF_UAPI_SYSDATA_E820ADDENTRY ||
		   sp->dst_uapifn == UXMHF_UAPI_SYSDATA_E820GETMAXINDEX ||
		   sp->dst_uapifn == UXMHF_UAPI_SYSDATA_E820GETENTRYFORINDEX) ==> (usysd_methodcall_invalid == true);
@*/
void slab_main(slab_params_t *sp){

	if( sp->dst_uapifn == UXMHF_UAPI_SYSDATA_E820ADDENTRY){
		usysd_e820addentry((uxmhf_uapi_sysdata_e820addentry_t *)sp->in_out_params);
		//@ghost usysd_methodcall_e820addentry = true;
	}else if( sp->dst_uapifn == UXMHF_UAPI_SYSDATA_E820GETMAXINDEX ){
		usysd_e820getmaxindex((uxmhf_uapi_sysdata_e820getmaxindex_t *)sp->in_out_params);
		//@ghost usysd_methodcall_e820getmaxindex = true;
	}else if( sp->dst_uapifn == UXMHF_UAPI_SYSDATA_E820GETENTRYFORINDEX){
		usysd_e820getentryforindex((uxmhf_uapi_sysdata_e820getentryforindex_t *)sp->in_out_params);
		//@ghost usysd_methodcall_e820getentryforindex = true;
	}else{
		//_XDPRINTF_("UAPI_SYSDATA[%u]: Unknown uAPI function %x. Halting!\n", (uint16_t)sp->cpuid, sp->dst_uapifn);
		//@ghost usysd_methodcall_invalid = true;
	}

}
