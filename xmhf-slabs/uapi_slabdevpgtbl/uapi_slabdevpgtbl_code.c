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
 * slab device pagetable uAPI
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <uapi_slabdevpgtbl.h>


__attribute__((section(".data"))) __attribute__((aligned(4096))) static vtd_ret_entry_t _slabdevpgtbl_vtd_ret[VTD_RET_MAXPTRS];
__attribute__((section(".data"))) __attribute__((aligned(4096))) static vtd_cet_entry_t _slabdevpgtbl_vtd_cet[VTD_RET_MAXPTRS][VTD_CET_MAXPTRS];
__attribute__((section(".data"))) static bool _slabdevpgtbl_initretcet_done = false;


static void _slabdevpgtbl_initretcet(void){
    u32 i, j;

    for(i=0; i< VTD_RET_MAXPTRS; i++){
        _slabdevpgtbl_vtd_ret[i].qwords[0] =
            vtd_make_rete((u64)&_slabdevpgtbl_vtd_cet[i], VTD_RET_PRESENT);
        _slabdevpgtbl_vtd_ret[i].qwords[1] = 0ULL;

        for(j=0; j < VTD_CET_MAXPTRS; j++){
            _slabdevpgtbl_vtd_cet[i][j].qwords[0] =
                _slabdevpgtbl_vtd_cet[i][j].qwords[1] = 0ULL;
        }
    }
}



/////
void slab_main(slab_params_t *sp){

    xmhf_uapi_params_hdr_t *uapiphdr = (xmhf_uapi_params_hdr_t *)sp->in_out_params;

    switch(uapiphdr->uapifn){
        case XMHFGEEC_UAPI_SDEVPGTBL_INITRETCET:{
            xmhfgeec_uapi_slabdevpgtbl_initretcet_params_t *initretcetp =
                (xmhfgeec_uapi_slabdevpgtbl_initretcet_params_t *)sp->in_out_params;

            if(!_slabdevpgtbl_initretcet_done){
                _slabdevpgtbl_initretcet();
                _slabdevpgtbl_initretcet_done = true;
            }

            initretcetp->result_retpaddr = (u32)&_slabdevpgtbl_vtd_ret;
        }
        break;

        default:
            _XDPRINTF_("UAPI_SLABDEVPGTBL[%u]: Unknown uAPI function %x. Halting!\n",
                    (u16)sp->cpuid, uapiphdr->uapifn);
            HALT();
            return;
    }


}
