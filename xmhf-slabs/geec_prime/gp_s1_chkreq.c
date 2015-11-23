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
#include <geec_sentinel.h>
#include <uapi_slabmempgtbl.h>
#include <xc_init.h>

///////////////////////////////////////////////////////////////
// sanity check HIC (hardware) requirements
void gp_s1_chkreq(void){
	u32 cpu_vendor;

	//grab CPU vendor
	cpu_vendor = xmhf_baseplatform_arch_getcpuvendor();
	if (cpu_vendor != CPU_VENDOR_INTEL){
		_XDPRINTF_("%s: not an Intel CPU but running VMX backend. Halting!\n", __func__);
		HALT();
	}

	//check VMX support
	{
		u32	cpu_features;
		u32 res0,res1,res2;

 CASM_FUNCCALL(xmhfhw_cpu_cpuid,0x1, &res0, &res1, &cpu_features, &res2);

		if ( ( cpu_features & (1<<5) ) == 0 ){
			_XDPRINTF_("No VMX support. Halting!\n");
			HALT();
		}
	}

	//we require unrestricted guest and EPT support, bail out if we don't have it
    {
        u64 msr_procctls2 = CASM_FUNCCALL(rdmsr64,IA32_VMX_PROCBASED_CTLS2_MSR);
        if( !( (msr_procctls2 >> 32) & 0x80 ) ){
            _XDPRINTF_("%s: need unrestricted guest support but did not find any!\n", __func__);
            HALT();
        }

        if( !( (msr_procctls2 >> 32) & 0x2) ){
            _XDPRINTF_("%s: need EPTt support but did not find any!\n", __func__);
            HALT();
        }

    }


	//initialize platform bus
	xmhfhw_platform_bus_init();


}



