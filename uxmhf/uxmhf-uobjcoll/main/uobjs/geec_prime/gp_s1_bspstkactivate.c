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
// #include <xmhfgeec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_prime.h>

#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
bool gp_s1_hub_called = false;
uint32_t check_esp, check_eip = CASM_RET_EIP;
slab_params_t test_sp;

void hwm_vdriver_writeesp(uint32_t oldval, uint32_t newval){
	//@assert (newval >= ((uint32_t)&_init_bsp_cpustack + 4)) && (newval <= ((uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
}

void gp_s1_hub(void){
	//@assert hwm_cpu_state == CPU_STATE_RUNNING;
	//@assert (hwm_cpu_msr_efer & (1ULL << EFER_NXE));
	//@assert (hwm_cpu_cr4 & CR4_PSE);
	//@assert (hwm_cpu_cr4 & CR4_PAE);
	//@assert (hwm_cpu_cr3 == (uint32_t)&_xcprimeon_init_pdpt);
	//@assert (hwm_cpu_cr0 == (CR0_PE | CR0_PG | CR0_ET | CR0_EM));

	//indicate s1_hub was invoked from bspstkactivate
	gp_s1_hub_called = true;
}

void main(void){
	//populate hardware model stack and program counter
	hwm_cpu_gprs_esp = (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
	hwm_cpu_gprs_eip = check_eip;
	check_esp = hwm_cpu_gprs_esp; // pointing to top-of-stack

	//execute harness
	gp_s1_bspstkactivate();

	//@assert gp_s1_hub_called == true;
	//@assert hwm_cpu_gprs_esp == check_esp;
	//@assert hwm_cpu_gprs_eip == check_eip;
}
#endif

void gp_s1_bspstkactivate(void){
	uint64_t _msrefer;
	uint32_t _cr4;
	uint32_t _cr0 = (CR0_PE | CR0_PG | CR0_ET | CR0_EM);

	_msrefer = CASM_FUNCCALL(rdmsr64, MSR_EFER);
	_msrefer |= (1ULL << EFER_NXE);
	CASM_FUNCCALL(wrmsr64, MSR_EFER, (uint32_t)_msrefer, (uint32_t)((uint64_t)_msrefer >> 32) );

	_XDPRINTF_("EFER=%016llx\n", CASM_FUNCCALL(rdmsr64,MSR_EFER));

	_cr4 = CASM_FUNCCALL(read_cr4, CASM_NOPARAM);
        _cr4 |= (CR4_PSE | CR4_PAE);
	CASM_FUNCCALL(write_cr4, _cr4);

	_XDPRINTF_("CR4=%08x\n", CASM_FUNCCALL(read_cr4,CASM_NOPARAM));

	CASM_FUNCCALL(write_cr3,(uint32_t)&_xcprimeon_init_pdpt);

	_XDPRINTF_("CR3=%08x\n", CASM_FUNCCALL(read_cr3,CASM_NOPARAM));

	CASM_FUNCCALL(write_cr0, _cr0);

	gp_s1_hub();
}
