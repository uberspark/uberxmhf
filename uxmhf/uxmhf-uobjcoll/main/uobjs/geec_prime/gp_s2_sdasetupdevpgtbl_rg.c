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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

// #include <xmhfgeec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_prime.h>

/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;

	assigns _slabdevpgtbl_pml4t[slabid][0..(VTD_MAXPTRS_PER_PML4T-1)];
	assigns _slabdevpgtbl_pdpt[slabid][0..(VTD_MAXPTRS_PER_PDPT-1)];
	assigns _slabdevpgtbl_pdt[slabid][0..((VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT)-1)];
	assigns _slabdevpgtbl_pt_rg[0..((VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT * VTD_PTRS_PER_PT)-1)];
	assigns _slabdevpgtbl_infotable[slabid].devpgtbl_initialized;

	ensures (_slabdevpgtbl_pml4t[slabid][0] ==
		(vtd_make_pml4te((uint64_t)&_slabdevpgtbl_pdpt[slabid], (VTD_PAGE_READ | VTD_PAGE_WRITE))) );

	ensures \forall integer x; 1 <= x < VTD_MAXPTRS_PER_PML4T ==> (
		(_slabdevpgtbl_pml4t[slabid][x] == 0)
	);

	ensures \forall integer x; 0 <= x < VTD_PTRS_PER_PDPT ==> (
			_slabdevpgtbl_pdpt[slabid][x] ==
			 (vtd_make_pdpte((uint64_t)&_slabdevpgtbl_pdt[slabid][x*VTD_PTRS_PER_PDT], (VTD_PAGE_READ | VTD_PAGE_WRITE)))
			);

	ensures \forall integer x; VTD_PTRS_PER_PDPT <= x < VTD_MAXPTRS_PER_PDPT ==> (
		(_slabdevpgtbl_pdpt[slabid][x] == 0)
	);

	ensures \forall integer x; 0 <= x < (VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT) ==> (
			_slabdevpgtbl_pdt[slabid][x] ==
			 (vtd_make_pdte((uint64_t)&_slabdevpgtbl_pt_rg[x*VTD_PTRS_PER_PT], (VTD_PAGE_READ | VTD_PAGE_WRITE)))
			);

	ensures \forall integer x; 0 <= x < (VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT * VTD_PTRS_PER_PT) &&
		( ( ((x*PAGE_SIZE_4K) >= xmhfgeec_slab_info_table[slabid].slab_physmem_extents[0].addr_start) &&
		  ((x*PAGE_SIZE_4K) < xmhfgeec_slab_info_table[slabid].slab_physmem_extents[0].addr_end) ) ||
			( ((x*PAGE_SIZE_4K) >= xmhfgeec_slab_info_table[slabid].slab_physmem_extents[1].addr_start) &&
			  ((x*PAGE_SIZE_4K) < xmhfgeec_slab_info_table[slabid].slab_physmem_extents[1].addr_end) )
		) ==> (_slabdevpgtbl_pt_rg[x] == (vtd_make_pte((x * PAGE_SIZE_4K), (VTD_PAGE_READ | VTD_PAGE_WRITE))));

	ensures \forall integer x; 0 <= x < (VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT * VTD_PTRS_PER_PT) &&
		!( ( ((x*PAGE_SIZE_4K) >= xmhfgeec_slab_info_table[slabid].slab_physmem_extents[0].addr_start) &&
		  ((x*PAGE_SIZE_4K) < xmhfgeec_slab_info_table[slabid].slab_physmem_extents[0].addr_end) ) ||
			( ((x*PAGE_SIZE_4K) >= xmhfgeec_slab_info_table[slabid].slab_physmem_extents[1].addr_start) &&
			  ((x*PAGE_SIZE_4K) < xmhfgeec_slab_info_table[slabid].slab_physmem_extents[1].addr_end) )
		) ==> (_slabdevpgtbl_pt_rg[x] == 0);


	ensures (_slabdevpgtbl_infotable[slabid].devpgtbl_initialized == true);
@*/
void gp_s2_sdasetupdevpgtbl_rg(uint32_t slabid){
	uint32_t i,j;

	_XDPRINTF_("%s: _slabdevpgtbl_pml4t[%u] at 0x%08x\n", __func__, slabid, &_slabdevpgtbl_pml4t[slabid]);

	//initialize lvl1 page table (pml4t)
	/*@
		loop invariant a1: 0 <= i <= VTD_MAXPTRS_PER_PML4T;
		loop invariant a2: \forall integer x; 0 <= x < i ==> (
			(_slabdevpgtbl_pml4t[slabid][x] == 0)
			);
		loop assigns i;
		loop assigns _slabdevpgtbl_pml4t[slabid][0..(VTD_MAXPTRS_PER_PML4T-1)];
		loop variant VTD_MAXPTRS_PER_PML4T - i;
	@*/
	for(i=0; i < VTD_MAXPTRS_PER_PML4T; i++)
		_slabdevpgtbl_pml4t[slabid][i] = 0;

	_slabdevpgtbl_pml4t[slabid][0] =
		vtd_make_pml4te((uint64_t)&_slabdevpgtbl_pdpt[slabid], (VTD_PAGE_READ | VTD_PAGE_WRITE));


	//initialize lvl2 page table (pdpt)
	/*@
		loop invariant a3: 0 <= i <= VTD_MAXPTRS_PER_PDPT;
		loop invariant a4: \forall integer x; 0 <= x < i ==> (
			(_slabdevpgtbl_pdpt[slabid][x] == 0)
			);
		loop assigns i;
		loop assigns _slabdevpgtbl_pdpt[slabid][0..(VTD_MAXPTRS_PER_PDPT-1)];
		loop variant VTD_MAXPTRS_PER_PDPT - i;
	@*/
	for(i=0; i < VTD_MAXPTRS_PER_PDPT; i++)
		_slabdevpgtbl_pdpt[slabid][i] = 0;


	/*@
		loop invariant a5: 0 <= i <= VTD_PTRS_PER_PDPT;
		loop invariant a6: \forall integer x; 0 <= x < i ==> (
			_slabdevpgtbl_pdpt[slabid][x] ==
			 (vtd_make_pdpte((uint64_t)&_slabdevpgtbl_pdt[slabid][x*VTD_PTRS_PER_PDT], (VTD_PAGE_READ | VTD_PAGE_WRITE)))
			);
		loop assigns i;
		loop assigns _slabdevpgtbl_pdpt[slabid][0..(VTD_PTRS_PER_PDPT-1)];
		loop variant VTD_PTRS_PER_PDPT - i;
	@*/
	for(i=0; i < VTD_PTRS_PER_PDPT; i++){
		_slabdevpgtbl_pdpt[slabid][i] =
			vtd_make_pdpte((uint64_t)&_slabdevpgtbl_pdt[slabid][i*VTD_PTRS_PER_PDT], (VTD_PAGE_READ | VTD_PAGE_WRITE));
	}




	//setup PDTs
	/*@
		loop invariant a7: 0 <= i <= (VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT);
		loop invariant a8: \forall integer x; 0 <= x < i ==> (
			_slabdevpgtbl_pdt[slabid][x] ==
			 (vtd_make_pdte((uint64_t)&_slabdevpgtbl_pt_rg[x*VTD_PTRS_PER_PT], (VTD_PAGE_READ | VTD_PAGE_WRITE)))
			);
		loop assigns i;
		loop assigns _slabdevpgtbl_pdt[slabid][0..((VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT)-1)];
		loop variant (VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT) - i;
	@*/
	for(i=0; i < (VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT); i++){
			_slabdevpgtbl_pdt[slabid][i] =
				vtd_make_pdte((uint64_t)&_slabdevpgtbl_pt_rg[i*VTD_PTRS_PER_PT], (VTD_PAGE_READ | VTD_PAGE_WRITE));
	}


	/*@
		loop invariant a9: 0 <= i <= (VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT * VTD_PTRS_PER_PT);
		loop assigns i;
		loop assigns _slabdevpgtbl_pt_rg[0..((VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT * VTD_PTRS_PER_PT)-1)];
		loop invariant a10: \forall integer x; 0 <= x < i &&
			( ( ((x*PAGE_SIZE_4K) >= xmhfgeec_slab_info_table[slabid].slab_physmem_extents[0].addr_start) &&
			  ((x*PAGE_SIZE_4K) < xmhfgeec_slab_info_table[slabid].slab_physmem_extents[0].addr_end) ) ||
				( ((x*PAGE_SIZE_4K) >= xmhfgeec_slab_info_table[slabid].slab_physmem_extents[1].addr_start) &&
			  	  ((x*PAGE_SIZE_4K) < xmhfgeec_slab_info_table[slabid].slab_physmem_extents[1].addr_end) )
			) ==> (_slabdevpgtbl_pt_rg[x] == (vtd_make_pte((x * PAGE_SIZE_4K), (VTD_PAGE_READ | VTD_PAGE_WRITE))));
		loop invariant a11: \forall integer x; 0 <= x < i &&
			!( ( ((x*PAGE_SIZE_4K) >= xmhfgeec_slab_info_table[slabid].slab_physmem_extents[0].addr_start) &&
			  ((x*PAGE_SIZE_4K) < xmhfgeec_slab_info_table[slabid].slab_physmem_extents[0].addr_end) ) ||
				( ((x*PAGE_SIZE_4K) >= xmhfgeec_slab_info_table[slabid].slab_physmem_extents[1].addr_start) &&
			  	  ((x*PAGE_SIZE_4K) < xmhfgeec_slab_info_table[slabid].slab_physmem_extents[1].addr_end) )
			) ==> (_slabdevpgtbl_pt_rg[x] == 0);
		loop variant (VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT * VTD_PTRS_PER_PT) - i;
	@*/
	//setup DMA access for rich-guest address space
	for(i=0; i < (VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT * VTD_PTRS_PER_PT); i++){
		if( ( ((i*PAGE_SIZE_4K) >= xmhfgeec_slab_info_table[slabid].slab_physmem_extents[0].addr_start) &&
			  ((i*PAGE_SIZE_4K) < xmhfgeec_slab_info_table[slabid].slab_physmem_extents[0].addr_end) ) ||
			( ((i*PAGE_SIZE_4K) >= xmhfgeec_slab_info_table[slabid].slab_physmem_extents[1].addr_start) &&
			  ((i*PAGE_SIZE_4K) < xmhfgeec_slab_info_table[slabid].slab_physmem_extents[1].addr_end) )
		){
		    _slabdevpgtbl_pt_rg[i] = vtd_make_pte((i * PAGE_SIZE_4K), (VTD_PAGE_READ | VTD_PAGE_WRITE));
		}else{
		   _slabdevpgtbl_pt_rg[i] = 0;
		}
	}

	_slabdevpgtbl_infotable[slabid].devpgtbl_initialized = true;

}
