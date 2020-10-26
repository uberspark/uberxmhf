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


//@ghost bool invoked_clearcet[VTD_RET_MAXPTRS];
/*@
	assigns _slabdevpgtbl_vtd_ret[0..(VTD_RET_MAXPTRS-1)].qwords[0];
	assigns _slabdevpgtbl_vtd_ret[0..(VTD_RET_MAXPTRS-1)].qwords[1];
	assigns invoked_clearcet[0..(VTD_RET_MAXPTRS-1)];
	assigns vtd_ret_address;
	ensures \forall integer x; 0 <= x < VTD_RET_MAXPTRS ==> ( _slabdevpgtbl_vtd_ret[x].qwords[0] == (vtd_make_rete((uint64_t)&_slabdevpgtbl_vtd_cet[x], VTD_RET_PRESENT)) );
	ensures \forall integer x; 0 <= x < VTD_RET_MAXPTRS ==> ( _slabdevpgtbl_vtd_ret[x].qwords[1] == 0 );
	ensures \forall integer x; 0 <= x < VTD_RET_MAXPTRS ==> ( invoked_clearcet[x] == true );
	ensures vtd_ret_address == (uint32_t)&_slabdevpgtbl_vtd_ret;
@*/
void gp_s1_iommuinittbl(void){
    uint32_t i, j;

	/*@
		loop invariant a1: 0 <= i <= VTD_RET_MAXPTRS;
		loop invariant a2: \forall integer x; 0 <= x < i ==> ( _slabdevpgtbl_vtd_ret[x].qwords[0] == (vtd_make_rete((uint64_t)&_slabdevpgtbl_vtd_cet[x], VTD_RET_PRESENT)) );
		loop invariant a3: \forall integer x; 0 <= x < i ==> ( _slabdevpgtbl_vtd_ret[x].qwords[1] == 0 );
		loop invariant a4: \forall integer x; 0 <= x < i ==> ( invoked_clearcet[x] == true );
		loop assigns _slabdevpgtbl_vtd_ret[0..(VTD_RET_MAXPTRS-1)].qwords[0];
		loop assigns _slabdevpgtbl_vtd_ret[0..(VTD_RET_MAXPTRS-1)].qwords[1];
		loop assigns i;
		loop assigns invoked_clearcet[0..(VTD_RET_MAXPTRS-1)];
		loop variant VTD_RET_MAXPTRS - i;
	@*/
    for(i=0; i< VTD_RET_MAXPTRS; i++){
        _slabdevpgtbl_vtd_ret[i].qwords[0] =
            vtd_make_rete((uint64_t)&_slabdevpgtbl_vtd_cet[i], VTD_RET_PRESENT);
        _slabdevpgtbl_vtd_ret[i].qwords[1] = 0ULL;

	gp_s1_iommuinittbl_clearcet(i);
	//@ghost invoked_clearcet[i] = true;
    }

    vtd_ret_address = (uint32_t)&_slabdevpgtbl_vtd_ret;
}

