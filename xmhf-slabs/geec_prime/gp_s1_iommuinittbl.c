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
#include <geec_sentinel.h>
#include <uapi_slabmempgtbl.h>
#include <xc_init.h>

/*@
	assigns _slabdevpgtbl_vtd_ret[0..(VTD_RET_MAXPTRS-1)].qwords[0];
	assigns _slabdevpgtbl_vtd_ret[0..(VTD_RET_MAXPTRS-1)].qwords[1];
	ensures \forall integer x; 0 <= x < VTD_RET_MAXPTRS ==> ( _slabdevpgtbl_vtd_ret[x].qwords[0] == (vtd_make_rete((u64)&_slabdevpgtbl_vtd_cet[x], VTD_RET_PRESENT)) );
	ensures \forall integer x; 0 <= x < VTD_RET_MAXPTRS ==> ( _slabdevpgtbl_vtd_ret[x].qwords[1] == 0 );
@*/
void gp_s1_iommuinittbl(void){
    u32 i, j;

	/*@
		loop invariant a1: 0 <= i <= VTD_RET_MAXPTRS;
		loop invariant a2: \forall integer x; 0 <= x < i ==> ( _slabdevpgtbl_vtd_ret[x].qwords[0] == (vtd_make_rete((u64)&_slabdevpgtbl_vtd_cet[x], VTD_RET_PRESENT)) );
		loop invariant a3: \forall integer x; 0 <= x < i ==> ( _slabdevpgtbl_vtd_ret[x].qwords[1] == 0 );
		loop assigns _slabdevpgtbl_vtd_ret[0..(VTD_RET_MAXPTRS-1)].qwords[0];
		loop assigns _slabdevpgtbl_vtd_ret[0..(VTD_RET_MAXPTRS-1)].qwords[1];
		loop assigns i;
		loop variant VTD_RET_MAXPTRS - i;
	@*/
    for(i=0; i< VTD_RET_MAXPTRS; i++){
        _slabdevpgtbl_vtd_ret[i].qwords[0] =
            vtd_make_rete((u64)&_slabdevpgtbl_vtd_cet[i], VTD_RET_PRESENT);
        _slabdevpgtbl_vtd_ret[i].qwords[1] = 0ULL;

	/*
        for(j=0; j < VTD_CET_MAXPTRS; j++){
            _slabdevpgtbl_vtd_cet[i][j].qwords[0] =
                _slabdevpgtbl_vtd_cet[i][j].qwords[1] = 0ULL;
        }*/
    }
}

