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

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <geec_prime.h>

//@ghost bool invokedsetptentries[MAX_SLAB_DMADATA_PDT_ENTRIES];
/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
	requires (paddr_end >= paddr_start);
	requires (paddr_end < (0xFFFFFFFFUL - PAGE_SIZE_2M));
	requires (paddr_end - paddr_start) <= MAX_SLAB_DMADATA_SIZE;
	assigns invokedsetptentries[0..(MAX_SLAB_DMADATA_PDT_ENTRIES-1)];
@*/
void gp_s2_sdasetupdevpgtbl_splintpdt(u32 slabid, u32 paddr_start, u32 paddr_end){
	u32 paddr;
	u32 pd_index=0;


    	/*@
		loop invariant a1: paddr_start <= paddr <= (paddr_end+PAGE_SIZE_2M);
		loop invariant a2: pd_index <= VTD_PTRS_PER_PDT;
		loop invariant a3: \forall integer x; 0 <= x < pd_index ==> (
			(x < MAX_SLAB_DMADATA_PDT_ENTRIES) ==> ( invokedsetptentries[x] == true)
			);
		loop assigns paddr;
		loop assigns pd_index;
		loop assigns invokedsetptentries[0..(MAX_SLAB_DMADATA_PDT_ENTRIES-1)];
		loop variant (paddr_end+PAGE_SIZE_2M)-paddr;
	@*/
	for(paddr = paddr_start; paddr < paddr_end; paddr+= PAGE_SIZE_2M){
		if(pd_index >= MAX_SLAB_DMADATA_PDT_ENTRIES){
			CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
		}else{
			//populate pt entries for this 2M range
			gp_s2_sdasetupdevpgtbl_setptentries(slabid, pd_index, paddr);
			//@ghost invokedsetptentries[pd_index] = true;
			pd_index++;
		}
	}


}

