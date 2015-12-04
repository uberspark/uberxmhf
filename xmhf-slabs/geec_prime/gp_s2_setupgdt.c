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

#if 0
/*@
	//requires \valid(t);
	requires (__TRSEL/8) <= gdtindex <= (XMHFGEEC_MAX_GDT_CODEDATA_DESCRIPTORS + MAX_PLATFORM_CPUS);
	requires 0 <= tssidx < MAX_PLATFORM_CPUS;
	ensures (((TSSENTRY *)&__xmhfhic_x86vmx_gdt_start[gdtindex])->baseAddr0_15 == ((u16)((u32)&__xmhfhic_x86vmx_tss[tssidx].tss_mainblock & 0x0000FFFF)));
	ensures (((TSSENTRY *)&__xmhfhic_x86vmx_gdt_start[gdtindex])->baseAddr16_23 == ((u8)(((u32)&__xmhfhic_x86vmx_tss[tssidx].tss_mainblock & 0x00FF0000) >> 16)));
	ensures (((TSSENTRY *)&__xmhfhic_x86vmx_gdt_start[gdtindex])->baseAddr24_31 == ((u8)(((u32)&__xmhfhic_x86vmx_tss[tssidx].tss_mainblock & 0xFF000000) >> 24)) );
	ensures (((TSSENTRY *)&__xmhfhic_x86vmx_gdt_start[gdtindex])->attributes1 == 0xE9);
	ensures (((TSSENTRY *)&__xmhfhic_x86vmx_gdt_start[gdtindex])->limit16_19attributes2 == 0x0);
	ensures (((TSSENTRY *)&__xmhfhic_x86vmx_gdt_start[gdtindex])->limit0_15 == ((4*PAGE_SIZE_4K)-1) );

@*/
static void gp_s2_setupgdt_setgdttssentry(u32 gdtindex, u32 tssidx){
	TSSENTRY *t = (TSSENTRY *)&__xmhfhic_x86vmx_gdt_start[gdtindex];
	u32 tss_base = (u32)&__xmhfhic_x86vmx_tss[tssidx].tss_mainblock;

	t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
	t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
	t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);
	t->attributes1= 0xE9;
	t->limit16_19attributes2= 0x0;
	t->limit0_15=(4*PAGE_SIZE_4K)-1;
}
#endif // 0

/*@
	requires (__TRSEL/8) <= gdtindex <= (XMHFGEEC_MAX_GDT_CODEDATA_DESCRIPTORS + MAX_PLATFORM_CPUS);
	requires 0 <= tssidx < MAX_PLATFORM_CPUS;
@*/
static void gp_s2_setupgdt_setgdttssentry(u32 gdtindex, u32 tssidx);



#if 1
//initialize GDT
//@ghost bool gp_s2_setupgdt_invokehelper[MAX_PLATFORM_CPUS];
/*@
	requires \valid(xcbootinfo);
	requires (xcbootinfo->cpuinfo_numentries < MAX_PLATFORM_CPUS);
	ensures \forall integer x; 0 <= x < xcbootinfo->cpuinfo_numentries ==> (
				(xcbootinfo->cpuinfo_buffer[x].lapic_id < MAX_PLATFORM_CPUS) ==>
				(gp_s2_setupgdt_invokehelper[x] == true) );
@*/
void gp_s2_setupgdt(void){
	u32 i;

    	/*@
		loop invariant a1: 0 <= i <= xcbootinfo->cpuinfo_numentries;
		loop invariant a2: \forall integer x; 0 <= x < i ==> (
				(xcbootinfo->cpuinfo_buffer[x].lapic_id < MAX_PLATFORM_CPUS) ==>
				(gp_s2_setupgdt_invokehelper[x] == true)
						);
		loop assigns gp_s2_setupgdt_invokehelper[0..(xcbootinfo->cpuinfo_numentries-1)];
		loop assigns i;
		loop variant xcbootinfo->cpuinfo_numentries - i;
	@*/
	for(i=0; i < xcbootinfo->cpuinfo_numentries; i++){

		if(xcbootinfo->cpuinfo_buffer[i].lapic_id < MAX_PLATFORM_CPUS){
			gp_s2_setupgdt_setgdttssentry( ((__TRSEL/8)+(i)) , xcbootinfo->cpuinfo_buffer[i].lapic_id);
			//@ghost gp_s2_setupgdt_invokehelper[i] = true;

			_XDPRINTF_("%s: setup TSS CPU idx=%u with base address=%x, iobitmap=%x\n, size=%u bytes", __func__,
			       xcbootinfo->cpuinfo_buffer[i].lapic_id,
			       (u32)(&__xmhfhic_x86vmx_tss[xcbootinfo->cpuinfo_buffer[i].lapic_id].tss_mainblock),
				(u32)&__xmhfhic_x86vmx_tss[xcbootinfo->cpuinfo_buffer[i].lapic_id].tss_iobitmap,
				((4*PAGE_SIZE_4K)-1) );

		}
	}

}

#endif

