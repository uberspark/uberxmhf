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

//@ghost bool gp_s2_setupmpgtblu_invokeduh[XMHFGEEC_TOTAL_SLABS];
//@ghost bool gp_s2_setupmpgtblu_invokedug[XMHFGEEC_TOTAL_SLABS];
//@ghost bool gp_s2_setupmpgtblu_invokedug_rg[XMHFGEEC_TOTAL_SLABS];
//@ghost bool gp_s2_setupmpgtblu_handlevfobjs[XMHFGEEC_TOTAL_SLABS];
//@ghost bool gp_s2_setupmpgtblu_invokedinvalidobjs[XMHFGEEC_TOTAL_SLABS];
/*@
	assigns gp_s2_setupmpgtblu_invokeduh[0..(XMHFGEEC_TOTAL_SLABS-1)];
	assigns gp_s2_setupmpgtblu_invokedug[0..(XMHFGEEC_TOTAL_SLABS-1)];
	assigns gp_s2_setupmpgtblu_invokedug_rg[0..(XMHFGEEC_TOTAL_SLABS-1)];
	assigns gp_s2_setupmpgtblu_handlevfobjs[0..(XMHFGEEC_TOTAL_SLABS-1)];
	assigns gp_s2_setupmpgtblu_invokedinvalidobjs[0..(XMHFGEEC_TOTAL_SLABS-1)];
	ensures \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==> (
		( (xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG ||
		xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG) &&
		(x >= XMHFGEEC_UHSLAB_BASE_IDX && x <= XMHFGEEC_UHSLAB_MAX_IDX)) ==>
		(gp_s2_setupmpgtblu_invokeduh[x] == true) );
	ensures \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==> (
			(xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST ||
			xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST) ==>
			(gp_s2_setupmpgtblu_invokedug[x] == true) );
	ensures \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==> (
			(xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST) ==>
			(gp_s2_setupmpgtblu_invokedug_rg[x] == true) );
	ensures \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==> (
			 ( ((xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_VfT_SENTINEL) ||
			   (xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG))
			) ==>	(gp_s2_setupmpgtblu_handlevfobjs[x] == true) );
	ensures \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==> (
			(
			 !( (xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG ||
			    xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG) &&
			    (x >= XMHFGEEC_UHSLAB_BASE_IDX && x <= XMHFGEEC_UHSLAB_MAX_IDX)
			  ) &&
			  !(xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST ||
			   xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST
			  ) &&
			  !(xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST
			  ) &&
			   !( ((xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_VfT_SENTINEL) ||
			   (xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG))
			   )
			  ) ==> (gp_s2_setupmpgtblu_invokedinvalidobjs[x] == true) );
@*/
void gp_s2_setupmpgtblu(void){
    uint32_t i;


    	/*@
		loop invariant a1: 0 <= i <= XMHFGEEC_TOTAL_SLABS;
		loop invariant a2: \forall integer x; 0 <= x < i ==> (
			( (xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG ||
			xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG) &&
			(x >= XMHFGEEC_UHSLAB_BASE_IDX && x <= XMHFGEEC_UHSLAB_MAX_IDX)) ==>
			(gp_s2_setupmpgtblu_invokeduh[x] == true) );
		loop invariant a3: \forall integer x; 0 <= x < i ==> (
			(xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST ||
			xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST) ==>
			(gp_s2_setupmpgtblu_invokedug[x] == true) );
		loop invariant a31: \forall integer x; 0 <= x < i ==> (
			(xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST) ==>
			(gp_s2_setupmpgtblu_invokedug_rg[x] == true) );
		loop invariant a4: \forall integer x; 0 <= x < i ==> (
			 ( ((xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_VfT_SENTINEL) ||
			   (xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG))
			) ==>	(gp_s2_setupmpgtblu_handlevfobjs[x] == true) );
		loop invariant a5: \forall integer x; 0 <= x < i ==> (
			(
			 !( (xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG ||
			    xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG) &&
			    (x >= XMHFGEEC_UHSLAB_BASE_IDX && x <= XMHFGEEC_UHSLAB_MAX_IDX)
			  ) &&
			  !(xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST ||
			   xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST
			  ) &&
			  !(xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST
			  ) &&
			   !( ((xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_VfT_SENTINEL) ||
			   (xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG))
			   )
			  ) ==> (gp_s2_setupmpgtblu_invokedinvalidobjs[x] == true) );
		loop assigns i;
		loop assigns gp_s2_setupmpgtblu_invokeduh[0..(XMHFGEEC_TOTAL_SLABS-1)];
		loop assigns gp_s2_setupmpgtblu_invokedug[0..(XMHFGEEC_TOTAL_SLABS-1)];
		loop assigns gp_s2_setupmpgtblu_invokedug_rg[0..(XMHFGEEC_TOTAL_SLABS-1)];
		loop assigns gp_s2_setupmpgtblu_handlevfobjs[0..(XMHFGEEC_TOTAL_SLABS-1)];
		loop assigns gp_s2_setupmpgtblu_invokedinvalidobjs[0..(XMHFGEEC_TOTAL_SLABS-1)];
		loop variant XMHFGEEC_TOTAL_SLABS - i;
	@*/
	for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){

		if( (xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG ||
			xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG) &&
			(i >= XMHFGEEC_UHSLAB_BASE_IDX && i <= XMHFGEEC_UHSLAB_MAX_IDX)){

			_XDPRINTF_("%s: slab %u --> ppopulating uV{T,U} page-tables...\n", __func__, i);
			gp_s2_setupmpgtbluh(i);
			//@ghost gp_s2_setupmpgtblu_invokeduh[i] = true;
			_XDPRINTF_("%s: slab %u --> uV{T,U}_prog page-tables populated\n", __func__, i);


		}else if (xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_uVT_PROG_GUEST ||
			xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_GUEST){

			_XDPRINTF_("%s: slab %u --> ppopulating uV{T,U}_prog_guest page-tables...\n", __func__, i);
			gp_s2_setupmpgtblug(i);
			//@ghost gp_s2_setupmpgtblu_invokedug[i] = true;
			_XDPRINTF_("%s: slab %u --> uV{T,U}_prog_guest page-tables populated\n", __func__, i);

		}else if (xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST){

			_XDPRINTF_("%s: slab %u --> ppopulating rich-guest page-tables...\n", __func__, i);
			gp_s2_setupmpgtblug_rg(i);
			//@ghost gp_s2_setupmpgtblu_invokedug_rg[i] = true;
			_XDPRINTF_("%s: slab %u --> rich-guest page-tables populated\n", __func__, i);


		}else if ( ((xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_VfT_SENTINEL) ||
			   (xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_VfT_PROG))
			){
			//do nothing for verified slabs
			//@ghost gp_s2_setupmpgtblu_handlevfobjs[i] = true;

		}else{
			//we have no idea what type of slab this is, halt!
			_XDPRINTF_("%s:%u no idea of slab %u of type %u. Halting!\n",
				__func__, __LINE__, i, xmhfgeec_slab_info_table[i].slabtype);
			CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
			//@ghost gp_s2_setupmpgtblu_invokedinvalidobjs[i] = true;

		}
	}
}

