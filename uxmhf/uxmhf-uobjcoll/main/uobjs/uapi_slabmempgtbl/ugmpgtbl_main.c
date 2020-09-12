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
 * slab memory pagetable uAPI
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_slabmempgtbl.h>


/////
//@ ghost bool ugmpgtbl_methodcall_inittable = false;
//@ ghost bool ugmpgtbl_methodcall_setentry = false;
//@ ghost bool ugmpgtbl_methodcall_getentry = false;
//@ ghost bool ugmpgtbl_methodcall_flushtlb = false;
//@ ghost bool ugmpgtbl_methodcall_invalid = false;
/*@
	requires \valid(sp);
	assigns sp->in_out_params[0..15];
	assigns ugmpgtbl_methodcall_inittable, ugmpgtbl_methodcall_setentry, ugmpgtbl_methodcall_getentry, ugmpgtbl_methodcall_flushtlb, ugmpgtbl_methodcall_invalid;
	ensures (sp->dst_uapifn == XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL) ==> (ugmpgtbl_methodcall_inittable == true);
	ensures (sp->dst_uapifn == XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR) ==> (ugmpgtbl_methodcall_setentry == true);
	ensures (sp->dst_uapifn == XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR) ==> (ugmpgtbl_methodcall_getentry == true);
	ensures (sp->dst_uapifn == XMHFGEEC_UAPI_SLABMEMPGTBL_FLUSHTLB) ==> (ugmpgtbl_methodcall_flushtlb == true);
	ensures !( sp->dst_uapifn == XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL ||
		   sp->dst_uapifn == XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR ||
		   sp->dst_uapifn == XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR ||
		   sp->dst_uapifn == XMHFGEEC_UAPI_SLABMEMPGTBL_FLUSHTLB) ==> (ugmpgtbl_methodcall_invalid == true);
@*/
// void slab_main(slab_params_t *sp){

// 	if(sp->dst_uapifn == XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL){
// 	    xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *initmempgtblp =
// 		(xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *)sp->in_out_params;

//             //@ ghost ugmpgtbl_methodcall_inittable = true;
// 	    _slabmempgtbl_initmempgtbl(initmempgtblp);

// 	}else if (sp->dst_uapifn == XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR){
//           xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
//             (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)sp->in_out_params;

//             //@ ghost ugmpgtbl_methodcall_setentry = true;
//             _slabmempgtbl_setentryforpaddr(setentryforpaddrp);

// 	}else if (sp->dst_uapifn == XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR){
//             xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *getentryforpaddrp =
//                 (xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *)sp->in_out_params;


//             //@ ghost ugmpgtbl_methodcall_getentry = true;
//             _slabmempgtbl_getentryforpaddr(getentryforpaddrp);


// 	}else if (sp->dst_uapifn == XMHFGEEC_UAPI_SLABMEMPGTBL_FLUSHTLB){
// 		xmhfgeec_uapi_slabmempgtbl_flushtlb_params_t *flushtlbp =
//                 (xmhfgeec_uapi_slabmempgtbl_flushtlb_params_t *)sp->in_out_params;

//             //@ ghost ugmpgtbl_methodcall_flushtlb = true;
//             _slabmempgtbl_flushtlb(flushtlbp);

// 	}else if (sp->dst_uapifn == UAPI_UGMPGTBL_GETMPGTBLBASE){
// 		uapi_ugmpgtbl_getmpgtblbase_params_t *p =
//                 (uapi_ugmpgtbl_getmpgtblbase_params_t *)sp->in_out_params;

//             _ugmpgtbl_getmpgtblbase(p);


// 	}else{

//             //@ ghost ugmpgtbl_methodcall_invalid = true;
//             //_XDPRINTF_("UAPI_SLABMEMPGTBL[%u]: Unknown uAPI function %x. Halting!\n",
//             //        (uint16_t)sp->cpuid, sp->dst_uapifn);
// 	}
// }
