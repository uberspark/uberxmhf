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

//@ghost bool invokedsdasetupdevpgtbl[XMHFGEEC_TOTAL_SLABS];
//@ghost bool invokedsdasetupdevpgtbl_rg[XMHFGEEC_TOTAL_SLABS];
//@ghost bool invokedsdadoalloc = true;
/*@
	requires 0 <= numentries_sysdev_memioregions < MAX_PLATFORM_DEVICES;
	assigns invokedsdasetupdevpgtbl[0..(XMHFGEEC_TOTAL_SLABS-1)];
	assigns invokedsdasetupdevpgtbl_rg[0..(XMHFGEEC_TOTAL_SLABS-1)];
	assigns _slabdevpgtbl_infotable[0..(XMHFGEEC_TOTAL_SLABS-1)].devpgtbl_initialized;
	assigns invokedsdadoalloc;
	ensures \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==> (
			(xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST) ==> (invokedsdasetupdevpgtbl_rg[x] == true)
			);
	ensures \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==> (
			!(xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST) ==> (invokedsdasetupdevpgtbl[x] == true)
			);
	ensures \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==> (
			(_slabdevpgtbl_infotable[x].devpgtbl_initialized == false)
			);
	ensures (invokedsdadoalloc == true);
@*/
void gp_s2_sda(void){
	uint32_t i;

	/*@
		loop invariant a1: 0 <= i <= XMHFGEEC_TOTAL_SLABS;
		loop invariant a2: \forall integer x; 0 <= x < i ==> (
			(_slabdevpgtbl_infotable[x].devpgtbl_initialized == false)
			);
		loop assigns i;
		loop assigns _slabdevpgtbl_infotable[0..(XMHFGEEC_TOTAL_SLABS-1)].devpgtbl_initialized;
		loop variant XMHFGEEC_TOTAL_SLABS - i;
	@*/
	for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
		_slabdevpgtbl_infotable[i].devpgtbl_initialized=false;
	}


	//initialize all slab device page tables
	/*@
		loop invariant a3: 0 <= i <= XMHFGEEC_TOTAL_SLABS;
		loop invariant a4: \forall integer x; 0 <= x < i ==> (
			(xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST) ==> (invokedsdasetupdevpgtbl_rg[x] == true)
			);
		loop invariant a5: \forall integer x; 0 <= x < i ==> (
			!(xmhfgeec_slab_info_table[x].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST) ==> (invokedsdasetupdevpgtbl[x] == true)
			);
		loop assigns i;
		loop assigns invokedsdasetupdevpgtbl[0..(XMHFGEEC_TOTAL_SLABS-1)];
		loop assigns invokedsdasetupdevpgtbl_rg[0..(XMHFGEEC_TOTAL_SLABS-1)];
		loop variant XMHFGEEC_TOTAL_SLABS - i;
	@*/
	for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
		if (xmhfgeec_slab_info_table[i].slabtype == XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST){
			_XDPRINTF_("%s: proceeding to setup rich-guest DMA tables for uobj %u...\n", __func__, i);
			gp_s2_sdasetupdevpgtbl_rg(i);
			//@ghost invokedsdasetupdevpgtbl_rg[i] = true;
			_XDPRINTF_("%s: rich-guest DMA tables setup for uobj %u\n", __func__, i);
		}else{
			gp_s2_sdasetupdevpgtbl(i);
			//@ghost invokedsdasetupdevpgtbl[i] = true;
		}

	}

	_XDPRINTF_("%s: initialized slab device page tables\n", __func__);

	gp_s2_sdadoalloc();
	//@ghost invokedsdadoalloc = true;

}


