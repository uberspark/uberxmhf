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

/*@
	requires 0 <= retindex < VTD_RET_MAXPTRS;
	assigns _slabdevpgtbl_vtd_cet[retindex][0..(VTD_CET_MAXPTRS-1)].qwords[0];
	assigns _slabdevpgtbl_vtd_cet[retindex][0..(VTD_CET_MAXPTRS-1)].qwords[1];
	ensures \forall integer y; 0 <= y < VTD_CET_MAXPTRS ==> ( _slabdevpgtbl_vtd_cet[retindex][y].qwords[0] == 0 );
	ensures \forall integer y; 0 <= y < VTD_CET_MAXPTRS ==> ( _slabdevpgtbl_vtd_cet[retindex][y].qwords[1] == 0 );

@*/
void gp_s1_iommuinittbl_clearcet(uint32_t retindex){
	uint32_t j;

	/*@
		loop invariant b1: 0 <= j <= VTD_CET_MAXPTRS;
		loop invariant b2: \forall integer y; 0 <= y < j ==> ( _slabdevpgtbl_vtd_cet[retindex][y].qwords[0] == 0 );
		loop invariant b3: \forall integer y; 0 <= y < j ==> ( _slabdevpgtbl_vtd_cet[retindex][y].qwords[1] == 0 );
		loop assigns _slabdevpgtbl_vtd_cet[retindex][0..(VTD_CET_MAXPTRS-1)].qwords[0];
		loop assigns _slabdevpgtbl_vtd_cet[retindex][0..(VTD_CET_MAXPTRS-1)].qwords[1];
		loop assigns j;
		loop variant VTD_CET_MAXPTRS - j;
	@*/
        for(j=0; j < VTD_CET_MAXPTRS; j++){
            _slabdevpgtbl_vtd_cet[retindex][j].qwords[0] = 0ULL;
            _slabdevpgtbl_vtd_cet[retindex][j].qwords[1] = 0ULL;
        }
}

