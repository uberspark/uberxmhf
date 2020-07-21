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
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_slabmempgtbl.h>


//setup unverified guest (ug) slab memory page tables
//@ghost bool gp_s2_setupmpgtblug_invokedmemorytype[1024*1024];
//@ghost uint64_t gp_s2_setupmpgtblug_invokedflags[1024*1024];
/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
	assigns gp_s2_setupmpgtblug_invokedmemorytype[0..((1024*1024)-1)];
	assigns gp_s2_setupmpgtblug_invokedflags[0..((1024*1024)-1)];
@*/
void gp_s2_setupmpgtblug(uint32_t slabid){
	uint64_t flags;
	uint32_t spatype;
	uint32_t memorytype;
	uint32_t i;
	slab_params_t spl;

	spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
	spl.cpuid = 0; //XXX: fixme, need to plug in BSP cpuid
	spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL;
	spl.in_out_params[0] = slabid;

	//@assert (spl.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME);
	//@assert (spl.dst_slabid == XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL);
	//@assert (spl.dst_uapifn == XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL);
	//@assert (spl.in_out_params[0] == slabid);
        XMHF_SLAB_CALLNEW(&spl);




	/*@
		loop invariant d1: 0 <= i <= (1024*1024);
		loop invariant d2: \forall integer x; 0 <= x < i ==> (gp_s2_setupmpgtblug_invokedmemorytype[x] == true);
		loop invariant d3: \forall integer x; 0 <= x < i ==> (gp_s2_setupmpgtblug_invokedflags[x] == true);
		loop assigns i;
		loop assigns memorytype;
		loop assigns spatype;
		loop assigns flags;
		loop assigns gp_s2_setupmpgtblug_invokedmemorytype[0..((1024*1024)-1)];
		loop assigns gp_s2_setupmpgtblug_invokedflags[0..((1024*1024)-1)];
		loop assigns spl.in_out_params[0..4];
		loop assigns spl.dst_uapifn;
		//loop assigns memorytype_mask;
		loop variant (1024*1024) - i;
	@*/
	for(i=0; i < (1024*1024); i++){
		memorytype = gp_s2_setupmpgtblug_getmtype((uint64_t)(i*PAGE_SIZE_4K));
		//@ghost gp_s2_setupmpgtblug_invokedmemorytype[i] = true;

		spatype = gp_s2_setupmpgtbl_getspatype(slabid, (uint32_t)(i*PAGE_SIZE_4K));

		flags = gp_s2_setupmpgtblug_getflags(slabid, (uint32_t)(i*PAGE_SIZE_4K), spatype);
		//@ghost gp_s2_setupmpgtblug_invokedflags[i] = true;


		spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
		spl.in_out_params[0] = slabid;
		spl.in_out_params[1] = (i*PAGE_SIZE_4K);
		spl.in_out_params[2] = 0;
		spl.in_out_params[3] = (uint32_t) ((i*PAGE_SIZE_4K))  | ((uint32_t)memorytype * 8) |  (uint32_t)flags ;	//present, UC
                spl.in_out_params[4] = 0;

		//@assert (spl.src_slabid == XMHFGEEC_SLAB_GEEC_PRIME);
		//@assert (spl.dst_slabid == XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL);
		//@assert (spl.dst_uapifn == XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR);
		//@assert (spl.in_out_params[0] == slabid);
		//@assert (spl.in_out_params[1] == (i*PAGE_SIZE_4K));
		//@assert (spl.in_out_params[2] == 0);
		//@assert (spl.in_out_params[3] == ((uint32_t) ((i*PAGE_SIZE_4K))  | ((uint32_t)memorytype * 8) |  (uint32_t)flags)) ;
		//@assert (spl.in_out_params[4] == 0);
		XMHF_SLAB_CALLNEW(&spl);
	}
}



