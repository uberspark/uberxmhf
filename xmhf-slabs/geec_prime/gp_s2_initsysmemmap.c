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
#include <uapi_sysdata.h>


void gp_s2_initsysmemmap(void){
	slab_params_t sp;
	uxmhf_uapi_sysdata_e820addentry_t *e820entry = (uxmhf_uapi_sysdata_e820addentry_t *)sp.in_out_params;
	u32 i;

	memset(&sp, 0, sizeof(sp));
	sp.cpuid = 0; //XXX: fixme need to plugin BSP cpu id
	sp.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
	sp.dst_slabid = XMHFGEEC_SLAB_UAPI_SYSDATA;
	sp.dst_uapifn =  UXMHF_UAPI_SYSDATA_E820ADDENTRY;

	for(i=0; i < (u32)xcbootinfo->memmapinfo_numentries; i++){
		e820entry->baseaddr_high = xcbootinfo->memmapinfo_buffer[i].baseaddr_high;
		e820entry->baseaddr_low = xcbootinfo->memmapinfo_buffer[i].baseaddr_low;
		e820entry->length_high = xcbootinfo->memmapinfo_buffer[i].length_high;
		e820entry->length_low = xcbootinfo->memmapinfo_buffer[i].length_low;
		e820entry->type = xcbootinfo->memmapinfo_buffer[i].type;
		XMHF_SLAB_CALLNEW(&sp);
	}

}

