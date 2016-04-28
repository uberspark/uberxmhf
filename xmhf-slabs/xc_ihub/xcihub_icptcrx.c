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
#include <xmhfgeec.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <xc_ihub.h>
#include <uapi_gcpustate.h>
#include <uapi_hcpustate.h>

/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


static u32 _xcihub_icptcrx_getregval(u32 gpr, x86regs_t r){
	  switch(gpr){
		case 0: return r.eax;
		case 1: return r.ecx;
		case 2: return r.edx;
		case 3: return r.ebx;
		case 4: return r.esp; //XXX: TODO: return value from GUEST RSP VMCS register
		case 5: return r.ebp;
		case 6: return r.esi;
		case 7: return r.edi;
		default:
			//_XDPRINTF_("\n%s: warning, invalid gpr value (%u): returning zero value", __FUNCTION__, gpr);
			return 0;
	}
}



void xcihub_icptcrx(u32 cpuid, u32 src_slabid){
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;
	xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs = (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;

	u32 guest_rip;
	u32 info_vmexit_instruction_length;
	u32 info_exit_qualification;
	u32 tofrom, gpr, crx;
	x86regs_t r;

	//_XDPRINTF_("%s[%u]: CRX access\n", __func__, cpuid);

	spl.cpuid = cpuid;
	spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;

	//read GPRs
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
	XMHF_SLAB_CALLNEW(&spl);
	memcpy(&r, &gcpustate_gprs->gprs, sizeof(x86regs_t));


	//read exit qualification
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
	gcpustate_vmrwp->encoding = VMCS_INFO_EXIT_QUALIFICATION;
    XMHF_SLAB_CALLNEW(&spl);
    info_exit_qualification = gcpustate_vmrwp->value;

	crx=(u32) ((u32)info_exit_qualification & 0x0000000FUL);
	gpr=(u32) (((u32)info_exit_qualification & 0x00000F00UL) >> (u32)8);
	tofrom = (u32) (((u32)info_exit_qualification & 0x00000030UL) >> (u32)4);

	if ( !(gpr >=0 && gpr <= 7) ){
		_XDPRINTF_("%s[%u]: invalid GPR value, gpr=%u\n", __func__, cpuid, gpr);
		HALT();
	}

	if (crx == 0x0 && tofrom == VMX_CRX_ACCESS_TO){
		//CR0 access
		u32 cr0_value = _xcihub_icptcrx_getregval(gpr, r);
		//_XDPRINTF_("%s[%u]: CR0 access, gpr=%u, tofrom=%u\n", __func__, cpuid, gpr, tofrom);

		//propagate CR0 while keeping CR_CD and CR0_NW clear in control CR0 shadow
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_GUEST_CR0;
		gcpustate_vmrwp->value = cr0_value;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_CR0_SHADOW;
		gcpustate_vmrwp->value = (cr0_value & ~(CR0_CD | CR0_NW));
	    XMHF_SLAB_CALLNEW(&spl);

		//we need to flush logical processor VPID mappings as we emulated CR0 load above
		CASM_FUNCCALL(xmhfhw_cpu_invvpid, VMX_INVVPID_SINGLECONTEXT, src_slabid, 0, 0);

	}else if(crx == 0x4 && tofrom == VMX_CRX_ACCESS_TO){
		//CR4 access
		_XDPRINTF_("%s[%u]: CR4 access, gpr=%u, tofrom=%u, WIP!\n", __func__, cpuid, gpr, tofrom);
		HALT();

	}else{
		_XDPRINTF_("%s[%u]: Unhandled CRx access, crx=0x%08x, gpr=%u, tofrom=%u\n", __func__, cpuid, crx, gpr, tofrom);
		HALT();
	}


	//skip over CRx instruction by adjusting RIP
	{
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
		gcpustate_vmrwp->encoding = VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH;
	    XMHF_SLAB_CALLNEW(&spl);
	    info_vmexit_instruction_length = gcpustate_vmrwp->value;
	}

	{
	    gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
	    XMHF_SLAB_CALLNEW(&spl);
	    guest_rip = gcpustate_vmrwp->value;
	    guest_rip+=info_vmexit_instruction_length;
	}

	{
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
		gcpustate_vmrwp->value = guest_rip;
		XMHF_SLAB_CALLNEW(&spl);
	}

	//write interruptibility = 0
	gcpustate_vmrwp->encoding = VMCS_GUEST_INTERRUPTIBILITY;
	gcpustate_vmrwp->value = 0;
	XMHF_SLAB_CALLNEW(&spl);

	//_XDPRINTF_("%s[%u]: adjusted guest_rip=%08x\n",  __func__, cpuid, guest_rip);


	//_XDPRINTF_("%s[%u]: CRx WIP. Halting!\n", __func__, cpuid);
	//HALT();

}



