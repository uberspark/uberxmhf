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

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

//#include <xc.h>
//#include <geec_sentinel.h>
#include <uapi_slabmempgtbl.h>


/////
void slab_main(slab_params_t *sp){

    switch(sp->dst_uapifn){

       case XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL:{
            xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *initmempgtblp =
                (xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *)sp->in_out_params;

            _slabmempgtbl_initmempgtbl(initmempgtblp->dst_slabid);
       }
       break;


       case XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR:{
            xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
                (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)sp->in_out_params;

            _slabmempgtbl_setentryforpaddr(setentryforpaddrp->dst_slabid,
                                           setentryforpaddrp->gpa,
                                           setentryforpaddrp->entry);

       }
        break;

       case XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR:{
            xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *getentryforpaddrp =
                (xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *)sp->in_out_params;

            getentryforpaddrp->result_entry = _slabmempgtbl_getentryforpaddr(getentryforpaddrp->dst_slabid,
                                           getentryforpaddrp->gpa);

       }
        break;


        default:
            _XDPRINTF_("UAPI_SLABMEMPGTBL[%u]: Unknown uAPI function %x. Halting!\n",
                    (u16)sp->cpuid, sp->dst_uapifn);
            HALT();
            return;
    }


}
