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


//@ghost uint64_t gflags[PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT];
/*@
	assigns gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[0..(PAGE_SIZE_4K-1)];
	assigns gp_vhslabmempgtbl_lvl2t[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT)-1];
	assigns gp_vhslabmempgtbl_lvl1t[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT)-1];
	assigns gflags[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT)-1];


	ensures (\forall uint32_t x; PAE_PTRS_PER_PDPT <= x < PAE_MAXPTRS_PER_PDPT ==>
		 ( ((uint64_t)gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[x] ) == 0 )
		);

	ensures (\forall uint32_t x; 0 <= x < PAE_PTRS_PER_PDPT ==>
		 ( ((uint64_t)gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[x] ) == ( ((uint64_t)(&gp_vhslabmempgtbl_lvl2t[x * PAE_PTRS_PER_PDT]) & 0x7FFFFFFFFFFFF000ULL ) | (uint64_t)(_PAGE_PRESENT)) )
		);
	ensures (\forall uint32_t x; 0 <= x < PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT ==>
		 ( ( (uint64_t)gp_vhslabmempgtbl_lvl2t[x] ) == ( ((uint64_t)(&gp_vhslabmempgtbl_lvl1t[(x * PAE_PTRS_PER_PT)]) & 0x7FFFFFFFFFFFF000ULL ) | (uint64_t)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER))  )
		);
	ensures (\forall uint32_t x; 0 <= x < (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT) ==>
		 ( (uint64_t)gp_vhslabmempgtbl_lvl1t[x] == ( ((uint64_t)(x * PAGE_SIZE_4K) & 0x7FFFFFFFFFFFF000ULL ) | (uint64_t)(gflags[x]) )   )
		);
@*/
void gp_s2_setupmpgtblv(void){
	uint32_t i;
	uint64_t flags=0;
	uint32_t spatype=0;
	uint32_t slabid = XMHFGEEC_SLAB_GEEC_PRIME;


	//zero out pdpt
	/*@
		loop invariant a0: 0 <= i <= PAE_MAXPTRS_PER_PDPT;
		loop invariant a01: \forall integer x; 0 <= x < i ==> (
			gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[x] == 0
			);
		loop assigns gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[0..(PAE_MAXPTRS_PER_PDPT-1)];
		loop assigns i;
		loop variant PAE_MAXPTRS_PER_PDPT - i;
	@*/
	for(i=0; i < PAE_MAXPTRS_PER_PDPT; i++){
		gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[i] = 0;
	}


	/*@
		loop invariant a1: 0 <= i <= PAE_PTRS_PER_PDPT;
		loop invariant a2: \forall integer x; 0 <= x < i ==> ( (uint64_t)gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[x] ) == ( ((uint64_t)(&gp_vhslabmempgtbl_lvl2t[x * PAE_PTRS_PER_PDT]) & 0x7FFFFFFFFFFFF000ULL ) | ((uint64_t)(_PAGE_PRESENT)));
		loop assigns gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[0..(PAE_PTRS_PER_PDPT-1)], i;
		loop variant PAE_PTRS_PER_PDPT - i;
	@*/
	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t[i] =
			pae_make_pdpe(&gp_vhslabmempgtbl_lvl2t[i * PAE_PTRS_PER_PDT], (uint64_t)(_PAGE_PRESENT));
	}



	//pdt setup
    	/*@
		loop invariant a3: 0 <= i <= (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT);
		loop invariant a4: \forall integer x; 0 <= x < i ==> (( (uint64_t)gp_vhslabmempgtbl_lvl2t[x] ) == ( ((uint64_t)(&gp_vhslabmempgtbl_lvl1t[(x * PAE_PTRS_PER_PT)]) & 0x7FFFFFFFFFFFF000ULL ) | ((uint64_t)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER))));
		loop assigns i, gp_vhslabmempgtbl_lvl2t[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT)];
		loop variant (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT) - i;
	@*/
	for(i=0; i < PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT; i++){
			gp_vhslabmempgtbl_lvl2t[i] =
				pae_make_pde(&gp_vhslabmempgtbl_lvl1t[(i * PAE_PTRS_PER_PT)], (uint64_t)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER));
	}



	//pt setup
	/*@	loop invariant a5: 0 <= i <= (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT);
		loop assigns gflags[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT)], spatype, flags, i, gp_vhslabmempgtbl_lvl1t[0..(PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT)];
		loop invariant a6: \forall integer x; 0 <= x < i ==> ( (uint64_t)gp_vhslabmempgtbl_lvl1t[x]) == ( ((uint64_t)(x * PAGE_SIZE_4K) & 0x7FFFFFFFFFFFF000ULL ) | (uint64_t)(gflags[x]) );
		loop variant (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT) - i;
	@*/
	for(i=0; i < (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT); ++i){
		spatype =  gp_s2_setupmpgtbl_getspatype(slabid, (uint32_t)(i * PAGE_SIZE_4K));

		flags = gp_s2_setupmpgtblv_getflags(slabid, (uint32_t)(i * PAGE_SIZE_4K), spatype);
		//@ghost gflags[i] = flags;

		gp_vhslabmempgtbl_lvl1t[i] = pae_make_pte( (i*PAGE_SIZE_4K), flags);
	}


   	_XDPRINTF_("%s: populated verified slabs' memory page tables\n", __func__);

}


