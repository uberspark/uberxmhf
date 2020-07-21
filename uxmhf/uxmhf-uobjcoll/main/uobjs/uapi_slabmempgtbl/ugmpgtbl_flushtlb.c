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
#include <uberspark/include/uberspark.h>
/*
 * slab memory pagetable uAPI
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_slabmempgtbl.h>

//@ghost bool flushtlb_invoke_invept = false;
/*@
	requires \valid(flushtlbp);

	behavior flush:
		assumes ( (flushtlbp->dst_slabid < XMHFGEEC_TOTAL_SLABS) &&
		    	  (flushtlbp->dst_slabid >= XMHFGEEC_UGSLAB_BASE_IDX && flushtlbp->dst_slabid <= XMHFGEEC_UGSLAB_MAX_IDX) &&
					(xmhfgeec_slab_info_table[flushtlbp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST ||
					 xmhfgeec_slab_info_table[flushtlbp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST ||
					 xmhfgeec_slab_info_table[flushtlbp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST)
				);
		assigns flushtlb_invoke_invept;
		ensures (flushtlb_invoke_invept == true);

	behavior invalid:
		assumes !( (flushtlbp->dst_slabid < XMHFGEEC_TOTAL_SLABS) &&
		    	  (flushtlbp->dst_slabid >= XMHFGEEC_UGSLAB_BASE_IDX && flushtlbp->dst_slabid <= XMHFGEEC_UGSLAB_MAX_IDX) &&
					(xmhfgeec_slab_info_table[flushtlbp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST ||
					 xmhfgeec_slab_info_table[flushtlbp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST ||
					 xmhfgeec_slab_info_table[flushtlbp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST)
				);
		assigns flushtlb_invoke_invept;
		ensures (flushtlb_invoke_invept == false);

	complete behaviors;
	disjoint behaviors;
@*/
void _slabmempgtbl_flushtlb(xmhfgeec_uapi_slabmempgtbl_flushtlb_params_t *flushtlbp){
	uint32_t status;

	if( (flushtlbp->dst_slabid < XMHFGEEC_TOTAL_SLABS) &&
		    ( (flushtlbp->dst_slabid >= XMHFGEEC_UGSLAB_BASE_IDX && flushtlbp->dst_slabid <= XMHFGEEC_UGSLAB_MAX_IDX) &&
			(xmhfgeec_slab_info_table[flushtlbp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST ||
			 xmhfgeec_slab_info_table[flushtlbp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST ||
			 xmhfgeec_slab_info_table[flushtlbp->dst_slabid].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST)
			)
	      ) {
		status = CASM_FUNCCALL(__vmx_invept, VMX_INVEPT_SINGLECONTEXT, 0, ((uint32_t)&_slabmempgtbl_lvl4t[(flushtlbp->dst_slabid - XMHFGEEC_UGSLAB_BASE_IDX)] | 0x1E), 0);
		//@ghost flushtlb_invoke_invept = true;
	}else{
		//@ghost flushtlb_invoke_invept = false;
	}
}
