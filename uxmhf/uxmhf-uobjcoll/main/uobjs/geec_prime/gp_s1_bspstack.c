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
//#include <geec_sentinel.h>
//#include <uapi_slabmempgtbl.h>
//#include <xc_init.h>


//@ghost bool gp_s1_bspstack_invoke_bspstkactivate = false;
//@ghost uint64_t gflags[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
/*@
	assigns _xcprimeon_init_pdpt[0..(PAE_MAXPTRS_PER_PDPT-1)];
	assigns _xcprimeon_init_pdt[0..(PAE_PTRS_PER_PDPT-1)][0..(PAE_PTRS_PER_PDT-1)];
	assigns gflags[0..(PAE_PTRS_PER_PDPT-1)][0..(PAE_PTRS_PER_PDT-1)];
	assigns gp_s1_bspstack_invoke_bspstkactivate;
	ensures gp_s1_bspstack_invoke_bspstkactivate == true;
	ensures \forall integer x; 0 <= x < PAE_PTRS_PER_PDPT ==> ( _xcprimeon_init_pdpt[x] == (pae_make_pdpe((uint32_t)&_xcprimeon_init_pdt[x][0], (_PAGE_PRESENT))) );
	ensures \forall integer x; PAE_PTRS_PER_PDPT <= x < PAE_MAXPTRS_PER_PDPT ==> ( _xcprimeon_init_pdpt[x] == 0 );
	ensures \forall integer x, y; 0 <= x < PAE_PTRS_PER_PDPT && 0 <= y < PAE_PTRS_PER_PDT ==> ( _xcprimeon_init_pdt[x][y] == (pae_make_pde_big((uint32_t)((x*(PAGE_SIZE_2M * PAE_PTRS_PER_PDT)) + (PAGE_SIZE_2M * y)), gflags[x][y])) );
@*/
void gp_s1_bspstack(void){
	uint32_t i, j;
	uint64_t flags;

	//clear PDPT
	/*@
		loop invariant a1: 0 <= i <= PAE_MAXPTRS_PER_PDPT;
		loop invariant a2: \forall integer x; 0 <= x < i ==> ( _xcprimeon_init_pdpt[x] == 0);
		loop assigns _xcprimeon_init_pdpt[0..(PAE_MAXPTRS_PER_PDPT-1)];
		loop assigns i;
		loop variant PAE_MAXPTRS_PER_PDPT - i;
	@*/
	for(i=0; i < PAE_MAXPTRS_PER_PDPT; i++)
		_xcprimeon_init_pdpt[i] = 0;

    	/*@
		loop invariant a3: 0 <= i <= PAE_PTRS_PER_PDPT;
		loop invariant a4: \forall integer x; 0 <= x < i ==> ( _xcprimeon_init_pdpt[x] == (pae_make_pdpe((uint32_t)&_xcprimeon_init_pdt[x][0], (_PAGE_PRESENT))) );
		loop invariant a41: \forall integer x, y; 0 <= x < i && 0 <= y < PAE_PTRS_PER_PDT ==> ( _xcprimeon_init_pdt[x][y] == (pae_make_pde_big((uint32_t)((x*(PAGE_SIZE_2M * PAE_PTRS_PER_PDT)) + (PAGE_SIZE_2M * y)), gflags[x][y])) );
		loop assigns _xcprimeon_init_pdpt[0..(PAE_PTRS_PER_PDPT-1)];
		loop assigns _xcprimeon_init_pdt[0..(PAE_PTRS_PER_PDPT-1)][0..(PAE_PTRS_PER_PDT-1)];
		loop assigns gflags[0..(PAE_PTRS_PER_PDPT-1)][0..(PAE_PTRS_PER_PDT-1)];
		loop assigns i;
		loop assigns j;
		loop assigns flags;
		loop variant PAE_PTRS_PER_PDPT - i;
	@*/
	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		_xcprimeon_init_pdpt[i] = pae_make_pdpe((uint32_t)&_xcprimeon_init_pdt[i][0], (_PAGE_PRESENT));

		/*@
			loop invariant a5: 0 <= j <= PAE_PTRS_PER_PDT;
			loop invariant a6: \forall integer y; 0 <= y < j ==> ( _xcprimeon_init_pdt[i][y] == (pae_make_pde_big((uint32_t)((i*(PAGE_SIZE_2M * PAE_PTRS_PER_PDT)) + (PAGE_SIZE_2M * y)), gflags[i][y])) );
			loop assigns _xcprimeon_init_pdt[i][0..(PAE_PTRS_PER_PDT-1)];
			loop assigns gflags[i][0..(PAE_PTRS_PER_PDT-1)];
			loop assigns j;
			loop assigns flags;
			loop variant PAE_PTRS_PER_PDT - j;
		@*/
		for(j=0; j < PAE_PTRS_PER_PDT; j++){
			flags = _gp_s1_bspstack_getflagsforspa((i*(PAGE_SIZE_2M * PAE_PTRS_PER_PDT)) + (PAGE_SIZE_2M * j));
			//@ghost gflags[i][j] = flags;

			_xcprimeon_init_pdt[i][j] = pae_make_pde_big(((i*(PAGE_SIZE_2M * PAE_PTRS_PER_PDT)) + (PAGE_SIZE_2M * j)), flags);
		}
	}

	gp_s1_bspstkactivate();
	//@ghost gp_s1_bspstack_invoke_bspstkactivate = true;
}

