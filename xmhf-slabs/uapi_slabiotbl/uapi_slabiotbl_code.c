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

#include <geec_sentinel.h>
#include <uapi_slabiotbl.h>

//I/O perms table for 64K legacy I/O addressing space
__attribute__((section(".rwdatahdr"))) __attribute__((aligned(4096))) u8 _slabiotbl_perms[XMHFGEEC_TOTAL_UGSLABS][3*PAGE_SIZE_4K] = { 0 };

static inline u32 _slabiotbl_sanitycheckhalt_slabid(u32 slabid){
    //if(slabid < XMHF_MAX_IOTBL_SETS)
    //    return; //I/O perm table is only for slab ids 0..XMHF_MAX_IOTBL_SETS-1

	if(slabid >= XMHFGEEC_UGSLAB_BASE_IDX && slabid <= XMHFGEEC_UGSLAB_MAX_IDX)
		return (slabid - XMHFGEEC_UGSLAB_BASE_IDX);

    _XDPRINTF_("%s: Halting!. Invalid slab index %u \n", __func__, slabid);
    HALT();
}


static void _slabiotbl_init(u32 dst_slabid){
    u32 slabtype;
    u32 slabiotbl_idx;

    slabiotbl_idx = _slabiotbl_sanitycheckhalt_slabid(dst_slabid);
    slabtype = xmhfgeec_slab_info_table[dst_slabid].slabtype;

    switch(slabtype){

        case XMHFGEEC_SLABTYPE_uVT_PROG_GUEST:
        case XMHFGEEC_SLABTYPE_uVU_PROG_GUEST:
        case XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST:{
            memset(&_slabiotbl_perms[slabiotbl_idx], 0xFFFFFFFFUL, sizeof(_slabiotbl_perms[0]));
            _XDPRINTF_("%s: setup slab %u with VMCS I/O perms, size=%u bytes\n", __func__, dst_slabid, sizeof(_slabiotbl_perms[0]));
        }
        break;

        default:
            _XDPRINTF_("%s: Halting. Unknown slab type %u\n", __func__, slabtype);
            HALT();
            break;
    }
}


static void _slabiotbl_allowaccesstoport(u32 dst_slabid, u16 port, u16 port_size){
    u32 i;
    u32 slabiotbl_idx;

    slabiotbl_idx = _slabiotbl_sanitycheckhalt_slabid(dst_slabid);

    for(i=0; i < port_size; i++){
        u32 idx = (port+i)/8;
        u8 bit = ((port+i) % 8);
        u8 bitmask = ~((u8)1 << bit);
        _slabiotbl_perms[slabiotbl_idx][idx] &= bitmask;
    }

}



static void _slabiotbl_denyaccesstoport(u32 dst_slabid, u16 port, u16 port_size){
    u32 i;
    u32 slabiotbl_idx;

    slabiotbl_idx = _slabiotbl_sanitycheckhalt_slabid(dst_slabid);

    for(i=0; i < port_size; i++){
        u32 idx = (port+i)/8;
        u8 bit = ((port+i) % 8);
        u8 bitmask = ((u8)1 << bit);
        _slabiotbl_perms[slabiotbl_idx][idx] |= bitmask;
    }

}



/////
void slab_main(slab_params_t *sp){

    switch(sp->dst_uapifn){

       case XMHFGEEC_UAPI_SLABIOTBL_INIT:{
            xmhfgeec_uapi_slabiotbl_init_params_t *initp =
                (xmhfgeec_uapi_slabiotbl_init_params_t *)sp->in_out_params;

            _slabiotbl_init(initp->dst_slabid);
       }
       break;


       case XMHFGEEC_UAPI_SLABIOTBL_ALLOWACCESSTOPORT:{
            xmhfgeec_uapi_slabiotbl_allowaccesstoport_params_t *allowaccesstoportp =
                (xmhfgeec_uapi_slabiotbl_allowaccesstoport_params_t *)sp->in_out_params;

            _slabiotbl_allowaccesstoport(allowaccesstoportp->dst_slabid,
                                           allowaccesstoportp->port,
                                           allowaccesstoportp->port_size);

       }
        break;

       case XMHFGEEC_UAPI_SLABIOTBL_DENYACCESSTOPORT:{
            xmhfgeec_uapi_slabiotbl_denyaccesstoport_params_t *denyaccesstoportp =
                (xmhfgeec_uapi_slabiotbl_denyaccesstoport_params_t *)sp->in_out_params;

            _slabiotbl_denyaccesstoport(denyaccesstoportp->dst_slabid,
                                           denyaccesstoportp->port,
                                           denyaccesstoportp->port_size);

       }
        break;



        default:
            _XDPRINTF_("UAPI_SLABIOTBL[%u]: Unknown uAPI function %x. Halting!\n",
                    (u16)sp->cpuid, sp->dst_uapifn);
            HALT();
            return;
    }

}
