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


//page table data structures for a 4GB system address mapping
__attribute__((section(".rwdatahdr"))) __attribute__((aligned(4096))) u64 _slabmempgtbl_lvl4t[XMHFGEEC_TOTAL_UGSLABS][PAE_MAXPTRS_PER_PML4T];
__attribute__((section(".data"))) __attribute__((aligned(4096))) u64 _slabmempgtbl_lvl3t[XMHFGEEC_TOTAL_UGSLABS][PAE_MAXPTRS_PER_PDPT];
__attribute__((section(".data"))) __attribute__((aligned(4096))) u64 _slabmempgtbl_lvl2t[XMHFGEEC_TOTAL_UGSLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
__attribute__((section(".data"))) __attribute__((aligned(4096)))  u64 _slabmempgtbl_lvl1t[XMHFGEEC_TOTAL_UGSLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT][PAE_PTRS_PER_PT];

/*
static void _slabmempgtbl_initmempgtbl_pae4K(u32 slabid){
    //pdpt = _slabmempgtbl_lvl4t[slabid];
    //pdt = _slabmempgtbl_lvl2t[slabid];
    //pt = _slabmempgtbl_lvl1t[slabid];
    u32 i, j;
    u64 default_flags = (u64)(_PAGE_PRESENT);

    //pdpt
    memset(&_slabmempgtbl_lvl4t[slabid], 0, PAGE_SIZE_4K);
    for(i=0; i < PAE_PTRS_PER_PDPT; i++){
        _slabmempgtbl_lvl4t[slabid][i] =
            pae_make_pdpe(&_slabmempgtbl_lvl2t[slabid][i], default_flags);
    }

    //pdt
    default_flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER);
	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		for(j=0; j < PAE_PTRS_PER_PDT; j++){
			_slabmempgtbl_lvl2t[slabid][i][j] =
                pae_make_pde(&_slabmempgtbl_lvl1t[slabid][i][j], default_flags);
		}
	}
}
*/


static void _slabmempgtbl_initmempgtbl_ept4K(u32 slabid){
    //pml4t = _slabmempgtbl_lvl4t[slabid];
    //pdpt = _slabmempgtbl_lvl3t[slabid];
    //pdt = _slabmempgtbl_lvl2t[slabid];
    //pt = _slabmempgtbl_lvl1t[slabid];
    u32 i, j;

    //pml4t
    memset(&_slabmempgtbl_lvl4t[slabid], 0, PAGE_SIZE_4K);
    for(i=0; i < PAE_PTRS_PER_PML4T; i++)
        _slabmempgtbl_lvl4t[slabid][i] =
            ((u64)&_slabmempgtbl_lvl3t[slabid] | 0x7);

    //pdpt
    memset(&_slabmempgtbl_lvl3t[slabid], 0, PAGE_SIZE_4K);
    for(i=0; i < PAE_PTRS_PER_PDPT; i++)
		_slabmempgtbl_lvl3t[slabid][i] =
            ((u64)&_slabmempgtbl_lvl2t[slabid][i] | 0x7 );

    //pdt
	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		for(j=0; j < PAE_PTRS_PER_PDT; j++){
			_slabmempgtbl_lvl2t[slabid][i][j] =
                ((u64)&_slabmempgtbl_lvl1t[slabid][i][j] | 0x7 );
		}
	}
}



static inline u32 _slabmempgtbl_sanitycheckhalt_slabid(u32 slabid){
    //if(slabid >= XMHFGEEC_UHSLAB_BASE_IDX && slabid <= XMHFGEEC_UHSLAB_MAX_IDX)
    //    return (slabid - XMHFGEEC_UHSLAB_BASE_IDX)+2;


    if(slabid >= XMHFGEEC_UGSLAB_BASE_IDX && slabid <= XMHFGEEC_UGSLAB_MAX_IDX)
        return (slabid - XMHFGEEC_UGSLAB_BASE_IDX);


    _XDPRINTF_("%s: Halting!. Invalid slab index %u \n", __func__, slabid);
    HALT();
}


static void _slabmempgtbl_initmempgtbl(u32 slabid){
    u32 slabtype;
    u32 uslabid;

    slabtype = xmhfgeec_slab_info_table[slabid].slabtype;
	uslabid  = _slabmempgtbl_sanitycheckhalt_slabid(slabid);


    switch(slabtype){
        /*case XMHFGEEC_SLABTYPE_VfT_PROG:
        case XMHFGEEC_SLABTYPE_uVT_PROG:
        case XMHFGEEC_SLABTYPE_uVU_PROG:{
            _slabmempgtbl_initmempgtbl_pae4K(uslabid);
            _XDPRINTF_("%s: setup slab %u with pae4K\n", __func__, slabid);
        }
        break;
*/

        case XMHFGEEC_SLABTYPE_uVT_PROG_GUEST:
        case XMHFGEEC_SLABTYPE_uVU_PROG_GUEST:
        case XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST:{
            _XDPRINTF_("%s: proceeding to setup slab %u with ept4K...\n", __func__, slabid);
            _slabmempgtbl_initmempgtbl_ept4K(uslabid);
            _XDPRINTF_("%s: setup slab %u with ept4K\n", __func__, slabid);
        }
        break;

        default:
            _XDPRINTF_("%s: Halting. Unknown slab type %u\n", __func__, slabtype);
            HALT();
            break;
    }

}


static void _slabmempgtbl_setentryforpaddr(u32 slabid, u64 gpa, u64 entry){

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


static u64 _slabmempgtbl_getentryforpaddr(u32 slabid, u64 gpa){
    u64 result_entry=0;
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
            result_entry = _slabmempgtbl_lvl1t[uslabid][pdpt_index][pdt_index][pt_index];
        }
        break;

        default:
            _XDPRINTF_("%s: Halting!. unknown slab type %u\n", __func__, slabtype);
            HALT();
            break;

    }

    return result_entry;
}





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
