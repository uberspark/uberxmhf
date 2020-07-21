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

//@ ghost uint32_t gretval;
/*@
	requires 0 <= slab_index < XMHFGEEC_TOTAL_SLABS ;
	assigns gretval;
	ensures (\forall uint32_t x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==> (gretval == _SLAB_SPATYPE_OTHER)) ==> (\result == _SLAB_SPATYPE_OTHER);
	ensures (\exists uint32_t x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==> ( !(gretval == _SLAB_SPATYPE_OTHER) &&
		(( (x == slab_index) || ((xmhfgeec_slab_info_table[x].slab_memgrantreadcaps & XMHFGEEC_SLAB_MEMGRANTREADCAP_MASK(slab_index)) ||
			(xmhfgeec_slab_info_table[x].slab_memgrantwritecaps & XMHFGEEC_SLAB_MEMGRANTWRITECAP_MASK(slab_index))) )) )
		==> (\result == (gretval | xmhfgeec_slab_info_table[x].slabtype | _SLAB_SPATYPE_MASK_SAMESLAB)) );
	ensures (\exists uint32_t x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==> ( !(gretval == _SLAB_SPATYPE_OTHER) &&
		!(( (x == slab_index) || ((xmhfgeec_slab_info_table[x].slab_memgrantreadcaps & XMHFGEEC_SLAB_MEMGRANTREADCAP_MASK(slab_index)) ||
			(xmhfgeec_slab_info_table[x].slab_memgrantwritecaps & XMHFGEEC_SLAB_MEMGRANTWRITECAP_MASK(slab_index))) )) )
		==> (\result == (gretval | xmhfgeec_slab_info_table[x].slabtype) ) );
@*/
uint32_t gp_s2_setupmpgtbl_getspatype(uint32_t slab_index, uint32_t spa){
	uint32_t i;
	uint32_t retval;


	//slab memory regions

	/*@
		loop invariant b1: 0 <= i <= XMHFGEEC_TOTAL_SLABS;
		loop invariant b2: \forall uint32_t x; 0 <= x < i ==> (gretval == _SLAB_SPATYPE_OTHER);
		loop assigns i, retval, gretval;
		loop variant XMHFGEEC_TOTAL_SLABS - i;
	@*/
	for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
		retval = gp_s2_setupmpgtbl_getspatypeuobj(i, spa);
		//@ghost gretval = retval;

		if(retval != _SLAB_SPATYPE_OTHER){
                        if ( (i == slab_index) || ((xmhfgeec_slab_info_table[i].slab_memgrantreadcaps & XMHFGEEC_SLAB_MEMGRANTREADCAP_MASK(slab_index)) ||
			(xmhfgeec_slab_info_table[i].slab_memgrantwritecaps & XMHFGEEC_SLAB_MEMGRANTWRITECAP_MASK(slab_index))) )
				return retval | xmhfgeec_slab_info_table[i].slabtype | _SLAB_SPATYPE_MASK_SAMESLAB;
			else
				return retval | xmhfgeec_slab_info_table[i].slabtype;
		}

	}

	return _SLAB_SPATYPE_OTHER;
}
