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
	gp_s1_chkreq();

	//@assert ((hwm_cpu_state == CPU_STATE_HALT) ||  ( (hwm_cpu_state == CPU_STATE_RUNNING) && (hwm_cpu_gprs_esp == check_esp) && (hwm_cpu_gprs_eip == check_eip) && (gp_rwdatahdr.xcbootinfo_store.memmapinfo_numentries < MAX_E820_ENTRIES))  );
}
#endif

///////////////////////////////////////////////////////////////
// sanity check HIC (hardware) requirements
void gp_s1_chkreq(void){
	uint32_t cpu_vendor;

	//grab CPU vendor
	cpu_vendor = uberspark_uobjrtl_hw__generic_x86_32_intel__getcpuvendor();
	if (cpu_vendor != CPU_VENDOR_INTEL){
		_XDPRINTF_("%s: not an Intel CPU but running VMX backend. Halting!\n", __func__);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
	}

	//check VMX support
	{
		uint32_t	cpu_features;
		uint32_t res0,res1,res2;

		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__cpuid,0x1, &res0, &res1, &cpu_features, &res2);

		if ( ( cpu_features & (1<<5) ) == 0 ){
			_XDPRINTF_("No VMX support. Halting!\n");
			CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
		}
	}

	//we require unrestricted guest and EPT support, bail out if we don't have it
	{
		uint64_t msr_procctls2 = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__rdmsr64,IA32_VMX_PROCBASED_CTLS2_MSR);
		if( !( (msr_procctls2 >> 32) & 0x80 ) ){
			_XDPRINTF_("%s: need unrestricted guest support but did not find any!\n", __func__);
			CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
		}

		if( !( (msr_procctls2 >> 32) & 0x2) ){
			_XDPRINTF_("%s: need EPTt support but did not find any!\n", __func__);
			CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
		}
	}



	//initialize platform bus
	if(!uberspark_uobjrtl_hw__generic_x86_32_intel__bus_init()){
		_XDPRINTF_("%s: need PCI type-1 access but did not find any!\n", __func__);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
	}

	//ensure bootinfo structure sanity
	if(!(gp_rwdatahdr.xcbootinfo_store.memmapinfo_numentries < MAX_E820_ENTRIES)){
		_XDPRINTF_("%s: xcbootinfo_store.memmapinfo_numentries (%u) out-of-bounds!\n", __func__, gp_rwdatahdr.xcbootinfo_store.memmapinfo_numentries);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
	}

	//@assert (gp_rwdatahdr.xcbootinfo_store.memmapinfo_numentries < MAX_E820_ENTRIES);
}



