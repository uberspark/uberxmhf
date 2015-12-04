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
//#include <geec_sentinel.h>
//#include <uapi_slabmempgtbl.h>
//#include <xc_init.h>

//initialize GDT
/*@
	requires \valid(xcbootinfo);
	requires (xcbootinfo->cpuinfo_numentries < MAX_PLATFORM_CPUS);
@*/
void gp_s2_setupgdt(void){
	u32 i;

    	/*@
		loop invariant a1: 0 <= i <= xcbootinfo->cpuinfo_numentries;
		loop assigns i;
		loop variant xcbootinfo->cpuinfo_numentries - i;
	@*/
	for(i=0; i < xcbootinfo->cpuinfo_numentries; i++){
		#if 0
		TSSENTRY *t;
		u32 tss_idx = xcbootinfo->cpuinfo_buffer[i].lapic_id;
		u32 tss_base=(u32)&__xmhfhic_x86vmx_tss[tss_idx].tss_mainblock;

		//TSS descriptor
		t= (TSSENTRY *)&__xmhfhic_x86vmx_gdt_start[(__TRSEL/8)+(i)];
		t->attributes1= 0xE9;
		t->limit16_19attributes2= 0x0;
		t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
		t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
		t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);
		//t->limit0_15=0x67;
		//t->limit0_15=sizeof(tss_t)-1;
		t->limit0_15=(4*PAGE_SIZE_4K)-1;
		#endif


		_XDPRINTF_("%s: setup TSS CPU idx=%u with base address=%x, iobitmap=%x\n, size=%u bytes", __func__,
		       tss_idx, tss_base, (u32)&__xmhfhic_x86vmx_tss[tss_idx].tss_iobitmap, t->limit0_15);
	}

}

