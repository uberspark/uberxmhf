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
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/uapi_slabmempgtbl.h>


/*@
	requires \valid(getentryforpaddrp);
	assigns getentryforpaddrp->result_entry;
	ensures ( (getentryforpaddrp->dst_slabid < XMHFGEEC_TOTAL_SLABS) &&
		  (pae_get_pdpt_index(getentryforpaddrp->gpa) < PAE_PTRS_PER_PDPT && pae_get_pdt_index(getentryforpaddrp->gpa) < PAE_PTRS_PER_PDT && pae_get_pt_index(getentryforpaddrp->gpa) < PAE_PTRS_PER_PT) &&
		( (getentryforpaddrp->dst_slabid >= XMHFGEEC_UGSLAB_BASE_IDX && getentryforpaddrp->dst_slabid <= XMHFGEEC_UGSLAB_MAX_IDX) &&
			(xmhfgeec_slab_info_table[getentryforpaddrp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST ||
			 xmhfgeec_slab_info_table[getentryforpaddrp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST ||
			 xmhfgeec_slab_info_table[getentryforpaddrp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST)
			)
		) ==> (getentryforpaddrp->result_entry == _slabmempgtbl_lvl1t[(getentryforpaddrp->dst_slabid - XMHFGEEC_UGSLAB_BASE_IDX)][pae_get_pdpt_index(getentryforpaddrp->gpa)][pae_get_pdt_index(getentryforpaddrp->gpa)][pae_get_pt_index(getentryforpaddrp->gpa)]);
	ensures !( (getentryforpaddrp->dst_slabid < XMHFGEEC_TOTAL_SLABS))
		 ==> (getentryforpaddrp->result_entry == 0);
@*/
void _slabmempgtbl_getentryforpaddr(xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *getentryforpaddrp){

    if( (getentryforpaddrp->dst_slabid < XMHFGEEC_TOTAL_SLABS)){
		if(pae_get_pdpt_index(getentryforpaddrp->gpa) < PAE_PTRS_PER_PDPT && pae_get_pdt_index(getentryforpaddrp->gpa) < PAE_PTRS_PER_PDT && pae_get_pt_index(getentryforpaddrp->gpa) < PAE_PTRS_PER_PT){
			if( (getentryforpaddrp->dst_slabid >= XMHFGEEC_UGSLAB_BASE_IDX && getentryforpaddrp->dst_slabid <= XMHFGEEC_UGSLAB_MAX_IDX) &&
				(xmhfgeec_slab_info_table[getentryforpaddrp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST ||
				 xmhfgeec_slab_info_table[getentryforpaddrp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST ||
				 xmhfgeec_slab_info_table[getentryforpaddrp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST)
				){
				getentryforpaddrp->result_entry = _slabmempgtbl_lvl1t[(getentryforpaddrp->dst_slabid - XMHFGEEC_UGSLAB_BASE_IDX)][pae_get_pdpt_index(getentryforpaddrp->gpa)][pae_get_pdt_index(getentryforpaddrp->gpa)][pae_get_pt_index(getentryforpaddrp->gpa)];
			}
		}
    }else{
    	getentryforpaddrp->result_entry = 0;
    }

}




