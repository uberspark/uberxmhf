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
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec_prime.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/uapi_uhmpgtbl.h>

//setup unverified hypervisor (uh) slab memory page tables
/*@
	requires XMHFGEEC_UHSLAB_BASE_IDX <= slabid <= XMHFGEEC_UHSLAB_MAX_IDX;

	assigns gp_rwdatahdr.gp_uhslabmempgtbl_lvl4t[(slabid - XMHFGEEC_UHSLAB_BASE_IDX)][0..(PAE_MAXPTRS_PER_PDPT-1)];
	assigns gp_uhslabmempgtbl_lvl2t[(slabid - XMHFGEEC_UHSLAB_BASE_IDX)][0..((PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT)-1)];

	ensures \forall integer x; PAE_PTRS_PER_PDPT <= x < PAE_MAXPTRS_PER_PDPT ==> (
			gp_rwdatahdr.gp_uhslabmempgtbl_lvl4t[(slabid - XMHFGEEC_UHSLAB_BASE_IDX)][x] == 0
			);

	ensures \forall integer x; 0 <= x < PAE_PTRS_PER_PDPT ==> (
			gp_rwdatahdr.gp_uhslabmempgtbl_lvl4t[(slabid - XMHFGEEC_UHSLAB_BASE_IDX)][x] ==
			(pae_make_pdpe(&gp_uhslabmempgtbl_lvl2t[(slabid - XMHFGEEC_UHSLAB_BASE_IDX)][x * PAE_PTRS_PER_PDT], (uint64_t)(_PAGE_PRESENT)))
			);


	ensures \forall integer x; 0 <= x < PAE_PTRS_PER_PDT ==> (
			gp_uhslabmempgtbl_lvl2t[(slabid - XMHFGEEC_UHSLAB_BASE_IDX)][x] ==
			(pae_make_pde(&gp_uhslabmempgtbl_lvl1t[(slabid - XMHFGEEC_UHSLAB_BASE_IDX)][(x * PAE_PTRS_PER_PT)], (uint64_t)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER)))
			);
@*/
void gp_s2_setupmpgtbluh(uint32_t slabid){
	uint64_t flags;
	uint32_t spatype;
	uint32_t i, j;
	slab_params_t spl;


	spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
	spl.dst_slabid = UOBJ_UAPI_UHMPGTBL;
	spl.cpuid = 0; //XXX: fixme, need to plug in BSP cpuid
	spl.dst_uapifn = UAPI_UHMPGTBL_INITMEMPGTBL;
	spl.in_out_params[0] = slabid;

	uhmpgtbl_slab_main(&spl);


	//pts
	/*@
		loop invariant a6: 0 <= i <= ((PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT)+0x2);
		loop assigns i;
		loop assigns spatype;
		loop assigns flags;
		loop variant ((PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT)+0x2) - i;
	@*/
	for(i=0; i < (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT); i++){
		spatype =  gp_s2_setupmpgtbl_getspatype(slabid, (uint32_t)(i*PAGE_SIZE_4K));
		flags = gp_s2_setupmpgtbluh_getflags(slabid, (uint32_t)(i*PAGE_SIZE_4K), spatype);

		if(!gp_s2_setupmpgtbluh_setentry(slabid, (slabid - XMHFGEEC_UHSLAB_BASE_IDX), spatype, i, flags))
			i+=2;
	}
}
