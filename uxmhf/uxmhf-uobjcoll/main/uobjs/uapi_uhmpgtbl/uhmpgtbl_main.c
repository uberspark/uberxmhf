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
 * untrusted hypervisoe memory pagetable uAPI
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_uhmpgtbl.h>


void uhmpgtbl_slab_main(slab_params_t *sp){

	if(sp->dst_uapifn == UAPI_UHMPGTBL_INITMEMPGTBL){
		uapi_uhmpgtbl_initmempgtbl_params_t *initmempgtblp =
		(uapi_uhmpgtbl_initmempgtbl_params_t *)sp->in_out_params;

	    _uhmpgtbl_initmempgtbl(initmempgtblp);

	}else if (sp->dst_uapifn == UAPI_UHMPGTBL_SETENTRYFORPADDR){
		uapi_uhmpgtbl_setentryforpaddr_params_t *setentryforpaddrp =
            (uapi_uhmpgtbl_setentryforpaddr_params_t *)sp->in_out_params;

            _uhmpgtbl_setentryforpaddr(setentryforpaddrp);

	}else if (sp->dst_uapifn == UAPI_UHMPGTBL_GETMPGTBLBASE){
		uapi_uhmpgtbl_getmpgtblbase_params_t *p =
            (uapi_uhmpgtbl_getmpgtblbase_params_t *)sp->in_out_params;

		_XDPRINTF_("uapi_uhmpgtbl[%u]: GETMPGTBLBASE\n",
                (uint16_t)sp->cpuid);

        _uhmpgtbl_getmpgtblbase(p);

	}else if (sp->dst_uapifn == UAPI_UHMPGTBL_GETIDXFORMPGTBLBASE){
		uapi_uhmpgtbl_getidxformpgtblbase_params_t *p =
            (uapi_uhmpgtbl_getidxformpgtblbase_params_t *)sp->in_out_params;

        _uhmpgtbl_getidxformpgtblbase(p);

	}else{
            //_XDPRINTF_("uapi_uhmpgtbl[%u]: Unknown uAPI function %x. Halting!\n",
            //        (uint16_t)sp->cpuid, sp->dst_uapifn);
	}
}
