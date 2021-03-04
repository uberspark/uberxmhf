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

#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/uobjs/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/uobjs/geec_prime.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/uobjs/uapi_sysdata.h>

#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
uint32_t check_esp, check_eip = CASM_RET_EIP;

void hwm_vdriver_writeesp(uint32_t oldval, uint32_t newval){
	//@assert (newval >= ((uint32_t)&_init_bsp_cpustack + 4)) && (newval <= ((uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
}

void main(void){
	//populate hardware model stack and program counter
	hwm_cpu_gprs_esp = (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
	hwm_cpu_gprs_eip = check_eip;
	check_esp = hwm_cpu_gprs_esp; // pointing to top-of-stack

	//execute harness
	gp_rwdatahdr.xcbootinfo_store.memmapinfo_numentries = framac_nondetu32interval(0, (MAX_E820_ENTRIES-1));
	gp_s2_initsysmemmap();

	//@assert hwm_cpu_gprs_esp == check_esp;
	//@assert hwm_cpu_gprs_eip == check_eip;
}
#endif
/*@
	requires (gp_rwdatahdr.xcbootinfo_store.memmapinfo_numentries < MAX_E820_ENTRIES);
@*/
void gp_s2_initsysmemmap(void){
	slab_params_t sp;
	uxmhf_uapi_sysdata_e820addentry_t *e820entry = (uxmhf_uapi_sysdata_e820addentry_t *)sp.in_out_params;
	uint32_t i;

	uberspark_uobjrtl_crt__memset(&sp, 0, sizeof(sp));
	sp.cpuid = 0; //XXX: fixme need to plugin BSP cpu id
	sp.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
	sp.dst_slabid = XMHFGEEC_SLAB_UAPI_SYSDATA;
	sp.dst_uapifn =  UXMHF_UAPI_SYSDATA_E820ADDENTRY;

	for(i=0; i < (uint32_t)gp_rwdatahdr.xcbootinfo_store.memmapinfo_numentries; i++){
		e820entry->baseaddr_high = gp_rwdatahdr.xcbootinfo_store.memmapinfo_buffer[i].baseaddr_high;
		e820entry->baseaddr_low = gp_rwdatahdr.xcbootinfo_store.memmapinfo_buffer[i].baseaddr_low;
		e820entry->length_high = gp_rwdatahdr.xcbootinfo_store.memmapinfo_buffer[i].length_high;
		e820entry->length_low = gp_rwdatahdr.xcbootinfo_store.memmapinfo_buffer[i].length_low;
		e820entry->type = gp_rwdatahdr.xcbootinfo_store.memmapinfo_buffer[i].type;
		usysd_slab_main(&sp);
	}

}

