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


//setup unverified hypervisor (uh) slab memory page tables
void gp_s2_setupmpgtbluh(u32 slabid){
	u64 flags;
	u32 spatype;
	u32 uhslabmempgtbl_idx;
	u32 i, j;


	uhslabmempgtbl_idx = slabid - XMHFGEEC_UHSLAB_BASE_IDX;

	//pdpt
	memset(&gp_rwdatahdr.gp_uhslabmempgtbl_lvl4t[uhslabmempgtbl_idx], 0, PAGE_SIZE_4K);
	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		gp_rwdatahdr.gp_uhslabmempgtbl_lvl4t[uhslabmempgtbl_idx][i] =
		    pae_make_pdpe(&gp_uhslabmempgtbl_lvl2t[uhslabmempgtbl_idx][i], (u64)(_PAGE_PRESENT));
	}

	//pdt
	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		for(j=0; j < PAE_PTRS_PER_PDT; j++){
			gp_uhslabmempgtbl_lvl2t[uhslabmempgtbl_idx][i][j] =
				pae_make_pde(&gp_uhslabmempgtbl_lvl1t[uhslabmempgtbl_idx][(i*PAE_PTRS_PER_PDT*PAE_PTRS_PER_PT)+(j*PAE_PTRS_PER_PT)], (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER));
		}
	}


	//pts
	for(i=0; i < (PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT); i++){
		spatype =  gp_s2_setupmpgtbl_getspatype(slabid, (u32)(i*PAGE_SIZE_4K));
		flags = gp_s2_setupmpgtbluh_getflags(slabid, (u32)(i*PAGE_SIZE_4K), spatype);

		if((spatype & 0x0000000FUL) == _SLAB_SPATYPE_GEEC_PRIME_IOTBL &&
		   xmhfgeec_slab_info_table[slabid].slabtype != XMHFGEEC_SLABTYPE_VfT_PROG &&
		   xmhfgeec_slab_info_table[slabid].slabtype != XMHFGEEC_SLABTYPE_VfT_SENTINEL){
			//map unverified slab iotbl instead (12K)
			gp_uhslabmempgtbl_lvl1t[uhslabmempgtbl_idx][i] =
				pae_make_pte(xmhfgeec_slab_info_table[slabid].iotbl_base, flags) & (~0x80);
			i++;

			gp_uhslabmempgtbl_lvl1t[uhslabmempgtbl_idx][i] =
				pae_make_pte(xmhfgeec_slab_info_table[slabid].iotbl_base+PAGE_SIZE_4K, flags) & (~0x80);
			i++;

			gp_uhslabmempgtbl_lvl1t[uhslabmempgtbl_idx][i] =
				pae_make_pte(xmhfgeec_slab_info_table[slabid].iotbl_base+(2*PAGE_SIZE_4K), flags) & (~0x80);
		}else{
			gp_uhslabmempgtbl_lvl1t[uhslabmempgtbl_idx][i] =
				pae_make_pte((i*PAGE_SIZE_4K), flags) & (~0x80);
		}
	}
}
