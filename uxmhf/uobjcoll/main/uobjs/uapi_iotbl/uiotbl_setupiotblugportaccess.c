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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/uapi_iotbl.h>

/*@
	requires 0 <= objidx < XMHFGEEC_TOTAL_UGSLABS;
	requires 0 <= bitmapidx < (3*PAGE_SIZE_4K);
	assigns uiotbl_ugslab_iobitmap[objidx][bitmapidx];
	ensures (uiotbl_ugslab_iobitmap[objidx][bitmapidx] == (\at(uiotbl_ugslab_iobitmap[objidx][bitmapidx], Pre) & mask));
@*/
static inline void uiotbl_setupiotblug_allowaccesstoport_setmask(uint32_t objidx, uint32_t bitmapidx, uint8_t mask){
	uiotbl_ugslab_iobitmap[objidx][bitmapidx] = uiotbl_ugslab_iobitmap[objidx][bitmapidx] & mask;
}


//@ghost uint8_t gp_s2_setupiotblug_allowaccesstoport_invokedsetmask[4];
/*@
	requires 0 <= ugslabiobitmap_idx < XMHFGEEC_TOTAL_UGSLABS;
	requires 0 <= port < 65536;
	requires 0 <= port_size <= 4;
	assigns uiotbl_ugslab_iobitmap[ugslabiobitmap_idx][((port+0)/8)..((port+(port_size-1))/8)];
	assigns gp_s2_setupiotblug_allowaccesstoport_invokedsetmask[0..(port_size-1)];
@*/
void uiotbl_setupiotblug_allowaccesstoport(uint32_t ugslabiobitmap_idx, uint16_t port, uint16_t port_size){
	uint32_t i;
	uint8_t bitmask;
	uint32_t bitmapidx;

	/*@
		loop invariant d1: 0 <= i <= port_size;
		loop invariant d2: \forall integer x; 0 <= x < i ==> (gp_s2_setupiotblug_allowaccesstoport_invokedsetmask[x] == true);
		loop assigns gp_s2_setupiotblug_allowaccesstoport_invokedsetmask[0..(port_size-1)];
		loop assigns i;
		loop assigns bitmask;
		loop assigns bitmapidx;
		loop assigns uiotbl_ugslab_iobitmap[ugslabiobitmap_idx][((port+0)/8)..((port+(port_size-1))/8)];
		loop variant port_size - i;
	@*/
	for(i=0; i < port_size; i++){
		bitmask =  ((uint8_t)1 << ((port+i) % 8));
		bitmapidx = ((port+i)/8);

		//@assert as1: (bitmask == ((uint8_t)1 << ((port+i) % 8)));
		//@assert as2: (bitmapidx == ((port+i)/8));
		uiotbl_setupiotblug_allowaccesstoport_setmask(ugslabiobitmap_idx, bitmapidx, ~bitmask);
		//@ghost gp_s2_setupiotblug_allowaccesstoport_invokedsetmask[i] = true;
	}
}

void uiotbl_setupiotblugportaccess(uapi_iotbl_setupiotblugportaccess_t *ps){
	uiotbl_setupiotblug_allowaccesstoport(
			0,
			ps->port,
			ps->port_size);
}
