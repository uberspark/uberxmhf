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

#if 0

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

#endif // 0


//@ghost bool inittable_invokeept4K=false;
/*@
	requires \valid(initmempgtblp);

	behavior inittable_do:
		assumes (
			 (initmempgtblp->dst_slabid < XMHFGEEC_TOTAL_SLABS) &&
			(xmhfgeec_slab_info_table[initmempgtblp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST ||
			 xmhfgeec_slab_info_table[initmempgtblp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST ||
			 xmhfgeec_slab_info_table[initmempgtblp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST)
			);
		assigns inittable_invokeept4K;
		ensures (inittable_invokeept4K == true);

	behavior inittable_invalid:
		assumes !(
			 (initmempgtblp->dst_slabid < XMHFGEEC_TOTAL_SLABS) &&
			(xmhfgeec_slab_info_table[initmempgtblp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST ||
			 xmhfgeec_slab_info_table[initmempgtblp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST ||
			 xmhfgeec_slab_info_table[initmempgtblp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST)
			);

		assigns inittable_invokeept4K;
		ensures (inittable_invokeept4K == false);

	complete behaviors;
	disjoint behaviors;

@*/
void _slabmempgtbl_initmempgtbl(xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *initmempgtblp){

    if( (initmempgtblp->dst_slabid < XMHFGEEC_TOTAL_SLABS) &&
	(xmhfgeec_slab_info_table[initmempgtblp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST ||
	 xmhfgeec_slab_info_table[initmempgtblp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST ||
	 xmhfgeec_slab_info_table[initmempgtblp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST)
      ){

            //_slabmempgtbl_initmempgtbl_ept4K((initmempgtblp->dst_slabid - XMHFGEEC_UGSLAB_BASE_IDX));
		//@ghost inittable_invokeept4K = true;
            _XDPRINTF_("%s: setup slab %u with ept4K\n", __func__, slabid);

	}else{
		//_XDPRINTF_("%s: Halting. Unknown slab type %u\n", __func__, slabtype);
		//@ghost inittable_invokeept4K = false;
	}
}


