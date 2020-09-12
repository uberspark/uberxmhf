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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_prime.h>

//@ghost bool invokedsetptentries[MAX_SLAB_DMADATA_PDT_ENTRIES];
/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
	requires (paddr_end >= paddr_start);
	requires (paddr_end < (0xFFFFFFFFUL - PAGE_SIZE_2M));
	requires (paddr_end - paddr_start) <= MAX_SLAB_DMADATA_SIZE;

	assigns invokedsetptentries[0..(((paddr_end - paddr_start)/PAGE_SIZE_2M)-1)];

	ensures \forall integer x; 0 <= x < ((paddr_end - paddr_start)/PAGE_SIZE_2M) ==> (
		 ( invokedsetptentries[x] == true)
		);
@*/
void gp_s2_sdasetupdevpgtbl_splintpdt(uint32_t slabid, uint32_t paddr_start, uint32_t paddr_end){
	uint32_t pd_index=0;

	/*@
		loop invariant a1: 0 <= pd_index <= ((paddr_end - paddr_start)/PAGE_SIZE_2M);
		loop invariant a2: \forall integer x; 0 <= x < pd_index ==> (
		 	 ( invokedsetptentries[x] == true)
			);
		loop assigns pd_index;
		loop assigns invokedsetptentries[0..(((paddr_end - paddr_start)/PAGE_SIZE_2M)-1)];
		loop variant ((paddr_end - paddr_start)/PAGE_SIZE_2M)-pd_index;
	@*/
	for(pd_index=0; pd_index < ((paddr_end - paddr_start)/PAGE_SIZE_2M); pd_index++){
			//populate pt entries for this 2M range
			gp_s2_sdasetupdevpgtbl_setptentries(slabid, pd_index, (paddr_start + (pd_index * PAGE_SIZE_2M)) );
			//@ghost invokedsetptentries[pd_index] = true;
	}
}

