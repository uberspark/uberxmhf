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


//we enter here with SMP enabled
//@ghost bool gp_s5_entry_invokedisbsp = false;
//@ghost bool gp_s5_entry_invokedgetcpulapicid = false;
//@ghost bool gp_s5_entry_invokedspinlock = false;
//@ghost bool gp_s5_entry_invokedsetupcpustate = false;
//@ghost bool gp_s5_entry_invokedspinunlock = false;
//@ghost bool gp_s5_entry_invokedstrt = false;
//@ghost bool gp_s5_entry_invokedhlt = false;
/*@
	ensures (gp_s5_entry_invokedisbsp == true);
	ensures (gp_s5_entry_invokedgetcpulapicid == true);
	ensures (gp_s5_entry_invokedspinlock == true);
	ensures (gp_s5_entry_invokedsetupcpustate == true);
	ensures (gp_s5_entry_invokedspinunlock == true);
	ensures (gp_s5_entry_invokedstrt == true);
	ensures (gp_s5_entry_invokedhlt == true);
@*/
void gp_s5_entry(void){
	u32 cpuid;
	bool isbsp;
	#if defined (__DEBUG_SERIAL__)
	static volatile u32 cpucount=0;
	#endif //__DEBUG_SERIAL__

	isbsp = xmhfhw_lapic_isbsp();
	//@ghost gp_s5_entry_invokedisbsp = true;

	cpuid  = xmhf_baseplatform_arch_x86_getcpulapicid();
	//@ghost gp_s5_entry_invokedgetcpulapicid = true;

    CASM_FUNCCALL(spin_lock,&gp_state4_smplock);
	//@ghost gp_s5_entry_invokedspinlock = true;

    _XDPRINTF_("%s[%u]: ESP=%08x\n", __func__, (u16)cpuid, CASM_FUNCCALL(read_esp,CASM_NOPARAM));

	gp_s5_setupcpustate((u16)cpuid, isbsp);
	//@ghost gp_s5_entry_invokedsetupcpustate = true;
	//@ghost gp_s5_entry_invokedisbsp = true;

	#if defined (__DEBUG_SERIAL__)
	cpucount++;
	#endif //__DEBUG_SERIAL__


    CASM_FUNCCALL(spin_unlock,&gp_state4_smplock);
	//@ghost gp_s5_entry_invokedspinunlock = true;

    #if defined (__DEBUG_SERIAL__)
    while(cpucount < __XMHF_CONFIG_DEBUG_SERIAL_MAXCPUS__);
    #endif //__DEBUG_SERIAL__

	gp_s5_invokestrt(cpuid);
	//@ghost gp_s5_entry_invokedstrt = true;

	_XDPRINTF_("%s[%u]: Should never be here. Halting!\n",
		__func__, (u16)cpuid);
	CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
	//@ghost gp_s5_entry_invokedhlt = true;
}
