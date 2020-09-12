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
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS ;
	assigns \nothing;
	behavior isiotbl:
		assumes (\forall uint32_t x; 0 <= x < MAX_PLATFORM_CPUS ==> (!(spa >= (uint32_t)&__xmhfhic_x86vmx_tss[x].tss_iobitmap &&
			spa < ((uint32_t)&__xmhfhic_x86vmx_tss[x].tss_iobitmap[3*PAGE_SIZE_4K]) )) );
		ensures	(\result == false);
	behavior isnotiotbl:
		assumes !(\forall uint32_t x; 0 <= x < MAX_PLATFORM_CPUS ==> (!(spa >= (uint32_t)&__xmhfhic_x86vmx_tss[x].tss_iobitmap &&
			spa < ((uint32_t)&__xmhfhic_x86vmx_tss[x].tss_iobitmap[3*PAGE_SIZE_4K]) )) );
		ensures	(\result == true);
	complete  behaviors;
	disjoint behaviors;
	//ensures (\result == true) || (\result == false);
	//ensures (\forall uint32_t x; 0 <= x < MAX_PLATFORM_CPUS ==> (!(spa >= (uint32_t)&__xmhfhic_x86vmx_tss[x].tss_iobitmap &&
	//  spa < ((uint32_t)&__xmhfhic_x86vmx_tss[x].tss_iobitmap[3*PAGE_SIZE_4K]) )) ) ==> 	(\result == false);
	//ensures !(\forall uint32_t x; 0 <= x < MAX_PLATFORM_CPUS ==> (!(spa >= (uint32_t)&__xmhfhic_x86vmx_tss[x].tss_iobitmap &&
	//  spa < ((uint32_t)&__xmhfhic_x86vmx_tss[x].tss_iobitmap[3*PAGE_SIZE_4K]) )) ) ==> 	(\result == true);
@*/
bool gp_s2_setupmpgtbl_getspatypeuobj_isiotbl(uint32_t slabid, uint32_t spa){
	uint32_t i;

	/*@
		loop invariant b1: 0 <= i <= MAX_PLATFORM_CPUS;
		loop invariant b2: \forall integer x; 0 <= x < i ==> (!(spa >= (uint32_t)&__xmhfhic_x86vmx_tss[x].tss_iobitmap &&
		  spa < ((uint32_t)&__xmhfhic_x86vmx_tss[x].tss_iobitmap[3*PAGE_SIZE_4K]) ));
		loop assigns i;
		loop variant MAX_PLATFORM_CPUS - i;
	@*/
	for(i=0; i < MAX_PLATFORM_CPUS; i++){
		if (spa >= (uint32_t)&__xmhfhic_x86vmx_tss[i].tss_iobitmap &&
		  spa < ((uint32_t)&__xmhfhic_x86vmx_tss[i].tss_iobitmap[3*PAGE_SIZE_4K]) ){
		    return true;
		}
	}

	return false;

}

