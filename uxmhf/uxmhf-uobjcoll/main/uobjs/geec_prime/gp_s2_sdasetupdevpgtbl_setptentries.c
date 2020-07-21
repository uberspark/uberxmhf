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
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_prime.h>


//setup PT entries for a 2M range
/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
	requires 0 <= pd_index < MAX_SLAB_DMADATA_PDT_ENTRIES;
	requires (startpaddr < (0xFFFFFFFFUL - PAGE_SIZE_2M));

	assigns _slabdevpgtbl_pdt[slabid][(startpaddr/PAGE_SIZE_2M)];
	assigns _slabdevpgtbl_pt[slabid][pd_index][0..(VTD_PTRS_PER_PT-1)];

	ensures ( _slabdevpgtbl_pdt[slabid][(startpaddr/PAGE_SIZE_2M)] ==
	    (vtd_make_pdte((uint64_t)&_slabdevpgtbl_pt[slabid][pd_index], (VTD_PAGE_READ | VTD_PAGE_WRITE)))
		);
	ensures \forall integer x; 0 <= x < VTD_PTRS_PER_PT ==> (
			    _slabdevpgtbl_pt[slabid][pd_index][x] ==
				(vtd_make_pte((startpaddr+(x * PAGE_SIZE_4K)), (VTD_PAGE_READ | VTD_PAGE_WRITE)))
			);
@*/
void gp_s2_sdasetupdevpgtbl_setptentries(uint32_t slabid, uint32_t pd_index, uint32_t startpaddr){
	uint32_t i;

	//stick a pt for the pdt entry
	_slabdevpgtbl_pdt[slabid][(startpaddr/PAGE_SIZE_2M)] =
	    vtd_make_pdte((uint64_t)&_slabdevpgtbl_pt[slabid][pd_index], (VTD_PAGE_READ | VTD_PAGE_WRITE));

 	/*@
		loop invariant a1: 0 <= i <= VTD_PTRS_PER_PT;
		loop invariant a2: \forall integer x; 0 <= x < i ==> (
			    _slabdevpgtbl_pt[slabid][pd_index][x] ==
				(vtd_make_pte((startpaddr+(x * PAGE_SIZE_4K)), (VTD_PAGE_READ | VTD_PAGE_WRITE)))
			);
		loop assigns i;
		loop assigns _slabdevpgtbl_pt[slabid][pd_index][0..(VTD_PTRS_PER_PT-1)];
		loop variant VTD_PTRS_PER_PT-i;
	@*/
	for(i=0; i < VTD_PTRS_PER_PT; i++){
	    _slabdevpgtbl_pt[slabid][pd_index][i] =
	    	vtd_make_pte((startpaddr+(i * PAGE_SIZE_4K)), (VTD_PAGE_READ | VTD_PAGE_WRITE));
	}
}

