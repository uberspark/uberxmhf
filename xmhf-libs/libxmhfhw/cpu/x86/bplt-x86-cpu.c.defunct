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

/*
 * XMHF base platform component interface, x86 common backend
 * general CPU functions
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>

//*
//returns true if CPU has support for XSAVE/XRSTOR
bool xmhf_baseplatform_arch_x86_cpuhasxsavefeature(void){
	u32 eax, ebx, ecx, edx;

	//bit 26 of ECX is 1 in CPUID function 0x00000001 if
	//XSAVE/XRSTOR feature is available

	cpuid(0x00000001, &eax, &ebx, &ecx, &edx);

	if((ecx & (1UL << 26)))
		return true;
	else
		return false;

}

u32 xmhf_baseplatform_arch_x86_getcpulapicid(void){
  u32 eax, edx, *lapic_reg;
  u32 lapic_id;

  //read LAPIC id of this core
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  if (edx != 0 ){ //APIC is not below 4G, unsupported
	_XDPRINTF_("%s: APIC is not below 4G, unsupported. Halting!", __FUNCTION__);
	HALT();
}
  eax &= (u32)0xFFFFF000UL;
  lapic_reg = (u32 *)((u32)eax+ (u32)LAPIC_ID);
  lapic_id = xmhfhw_sysmemaccess_readu32((u32)lapic_reg);
  lapic_id = lapic_id >> 24;

  return lapic_id;
}

u64 xmhf_baseplatform_arch_x86_getgdtbase(void){
		struct {
			u16 limit;
			u64 base;
		} __attribute__ ((packed)) gdtr;


		asm volatile(
			"sgdt %0 \r\n"
			: //no output
			: "m" (gdtr)
			: //no clobber
		);

		return gdtr.base;
}

u64 xmhf_baseplatform_arch_x86_getidtbase(void){
		struct {
			u16 limit;
			u64 base;
		} __attribute__ ((packed)) idtr;


		asm volatile(
			"sidt %0 \r\n"
			: //no output
			: "m" (idtr)
			: //no clobber
		);

		return idtr.base;
}

u64  xmhf_baseplatform_arch_x86_gettssbase(void){
	  u64 gdtbase = xmhf_baseplatform_arch_x86_getgdtbase();
	  u32 tssdesc_low, tssdesc_high;

	  asm volatile(
            "movl %2, %%edi\r\n"
            "xorl %%eax, %%eax\r\n"
            "str %%ax \r\n"
            "addl %%eax, %%edi\r\n"		//%edi is pointer to TSS descriptor in GDT
            "movl (%%edi), %0 \r\n"		//move low 32-bits of TSS descriptor into tssdesc_low
            "addl $0x4, %%edi\r\n"		//%edi points to top 32-bits of 64-bit TSS desc.
            "movl (%%edi), %1 \r\n"		//move high 32-bits of TSS descriptor into tssdesc_high
	     : "=r" (tssdesc_low), "=r" (tssdesc_high)
	     : "m"(gdtbase)
	     : "edi", "eax"
	  );

       return (  (u64)(  ((u32)tssdesc_high & 0xFF000000UL) | (((u32)tssdesc_high & 0x000000FFUL) << 16)  | ((u32)tssdesc_low >> 16)  ) );
}


//*
//get CPU vendor
u32 xmhf_baseplatform_arch_x86_getcpuvendor(void){
	u32 reserved, vendor_dword1, vendor_dword2, vendor_dword3;
	u32 cpu_vendor;

    cpuid(0, &reserved, &vendor_dword1, &vendor_dword3, &vendor_dword2);

	if(vendor_dword1 == AMD_STRING_DWORD1 && vendor_dword2 == AMD_STRING_DWORD2
			&& vendor_dword3 == AMD_STRING_DWORD3)
		cpu_vendor = CPU_VENDOR_AMD;
	else if(vendor_dword1 == INTEL_STRING_DWORD1 && vendor_dword2 == INTEL_STRING_DWORD2
			&& vendor_dword3 == INTEL_STRING_DWORD3)
		cpu_vendor = CPU_VENDOR_INTEL;
	else{
		_XDPRINTF_("%s: unrecognized x86 CPU (0x%08x:0x%08x:0x%08x). HALT!\n",
			__FUNCTION__, vendor_dword1, vendor_dword2, vendor_dword3);
		HALT();
	}

	return cpu_vendor;
}

//*
u32 xmhf_baseplatform_arch_getcpuvendor(void){
	return xmhf_baseplatform_arch_x86_getcpuvendor();
}

