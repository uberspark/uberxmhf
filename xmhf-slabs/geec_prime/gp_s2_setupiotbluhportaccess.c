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

/*@
	requires 0 <= uhslabiobitmap_idx < XMHFGEEC_TOTAL_UHSLABS;
	requires 0 <= port_size <= 4;
	assigns \nothing;
@*/
void gp_s2_setupiotbluh_allowaccesstoport(u32 uhslabiobitmap_idx, u16 port, u16 port_size){
	u32 i;

	/*@
		loop invariant d1: 0 <= i <= port_size;
		//loop invariant b2: \forall integer x; 0 <= x < k ==> (
		//		((sysdev_memioregions[sysdev_memioregions_index].memioextents[x].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_IO &&
		//		(sysdev_memioregions[sysdev_memioregions_index].memioextents[x].addr_start <= sysdev_memioregions[sysdev_memioregions_index].memioextents[x].addr_end))) ==>
		//		(gp_s2_setupiotbluh_helper_invokedportaccess[x] == true)
		//				);
		loop assigns i;
		loop variant port_size - i;
	@*/
	for(i=0; i < port_size; i++){
		//gp_rwdatahdr.gp_uhslab_iobitmap[uhslabiobitmap_idx][((port+i)/8)] &= ~((u8)1 << ((port+i) % 8));
	}
}
