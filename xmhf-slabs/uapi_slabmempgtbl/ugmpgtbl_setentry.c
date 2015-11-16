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

#include <xc.h>
#include <geec_sentinel.h>
#include <uapi_slabmempgtbl.h>



static inline u32 _slabmempgtbl_sanitycheckhalt_slabid(u32 slabid){
    //if(slabid >= XMHFGEEC_UHSLAB_BASE_IDX && slabid <= XMHFGEEC_UHSLAB_MAX_IDX)
    //    return (slabid - XMHFGEEC_UHSLAB_BASE_IDX)+2;


    if(slabid >= XMHFGEEC_UGSLAB_BASE_IDX && slabid <= XMHFGEEC_UGSLAB_MAX_IDX)
        return (slabid - XMHFGEEC_UGSLAB_BASE_IDX);


    _XDPRINTF_("%s: Halting!. Invalid slab index %u \n", __func__, slabid);
    HALT();
}



void _slabmempgtbl_setentryforpaddr(u32 slabid, u64 gpa, u64 entry){

    u64 pdpt_index = pae_get_pdpt_index(gpa);
    u64 pdt_index = pae_get_pdt_index(gpa);
    u64 pt_index = pae_get_pt_index(gpa);
    u32 slabtype;
    u32 uslabid;


    slabtype = xmhfgeec_slab_info_table[slabid].slabtype;
	uslabid  = _slabmempgtbl_sanitycheckhalt_slabid(slabid);

    switch(slabtype){
        /*case XMHFGEEC_SLABTYPE_VfT_PROG:
        case XMHFGEEC_SLABTYPE_uVT_PROG:
        case XMHFGEEC_SLABTYPE_uVU_PROG:*/
        case XMHFGEEC_SLABTYPE_uVT_PROG_GUEST:
        case XMHFGEEC_SLABTYPE_uVU_PROG_GUEST:
        case XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST:{
            _slabmempgtbl_lvl1t[uslabid][pdpt_index][pdt_index][pt_index] =
                entry & (~0x80);
        }
        break;

        default:
            _XDPRINTF_("%s: Halting!. unknown slab type %u\n", __func__, slabtype);
            HALT();
            break;

    }

}

