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

#include <xmhfhw.h>

#include <xc.h>
#include <xc_ihub.h>
#include <uapi_gcpustate.h>
#include <uapi_hcpustate.h>

#define CR4_SMEP	(1UL << 20)
#define CR4_SMAP 	(1UL << 21)
#define CR4_PKE		(1UL << 22)
/*
 * xcihub_icptcrx -- rich guest control register access emulation
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

u32 xcihub_icptcrx_read_cr4(u32 cpuid){
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;

	memset(&spl, 0, sizeof(spl));

	spl.cpuid = cpuid;
	spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
	gcpustate_vmrwp->encoding = VMCS_GUEST_CR4;
	XMHF_SLAB_CALLNEW(&spl);

	return (gcpustate_vmrwp->value);
}

u32 xcihub_icptcrx_read_cr0(u32 cpuid){
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;

	memset(&spl, 0, sizeof(spl));

	spl.cpuid = cpuid;
	spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
	gcpustate_vmrwp->encoding = VMCS_GUEST_CR0;
	XMHF_SLAB_CALLNEW(&spl);

	return (gcpustate_vmrwp->value);
}


u32 xcihub_icptcrx_read_cr3(u32 cpuid){
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;

	memset(&spl, 0, sizeof(spl));

	spl.cpuid = cpuid;
	spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
	gcpustate_vmrwp->encoding = VMCS_GUEST_CR3;
	XMHF_SLAB_CALLNEW(&spl);

	return (gcpustate_vmrwp->value);
}



u32 xcihub_icptcrx_read_cr4_shadow(u32 cpuid){
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;

	memset(&spl, 0, sizeof(spl));

	spl.cpuid = cpuid;
	spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
	gcpustate_vmrwp->encoding = VMCS_CONTROL_CR4_SHADOW;
	XMHF_SLAB_CALLNEW(&spl);

	return (gcpustate_vmrwp->value);
}



bool is_paging_enabled(u32 cpuid){
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;

	memset(&spl, 0, sizeof(spl));

	spl.cpuid = cpuid;
	spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
	gcpustate_vmrwp->encoding = VMCS_GUEST_CR0;
	XMHF_SLAB_CALLNEW(&spl);

	if(gcpustate_vmrwp->value & CR0_PG)
		return true;
	else
		return false;
}

#define CR0_RESERVED_BITS                                               \
        (~(u32)(CR0_PE | CR0_MP | CR0_EM | CR0_TS \
                          | CR0_ET | CR0_NE | CR0_WP | CR0_AM \
                          | CR0_NW | CR0_CD | CR0_PG))

#define GUEST_CR0_MASK (CR0_NW | CR0_CD)

u32 xcihub_icptcrx_handle_cr0(u32 cpuid, u32 src_slabid, u32 cr0){
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;
	u32 old_cr0 = xcihub_icptcrx_read_cr0(cpuid);
	u32 hw_cr0;
	u32 update_bits = CR0_PG | CR0_WP;

	memset(&spl, 0, sizeof(spl));

	cr0 |= CR0_ET;
	cr0 &= ~CR0_RESERVED_BITS;

	hw_cr0 = (cr0 & ~GUEST_CR0_MASK);
	hw_cr0 |= CR0_NE;

		spl.cpuid = cpuid;
		spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
		spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_CONTROL_CR0_SHADOW;
		gcpustate_vmrwp->value = cr0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_CR0;
		gcpustate_vmrwp->value = hw_cr0;
		XMHF_SLAB_CALLNEW(&spl);

		if ((cr0 ^ old_cr0) & CR0_PG) {
			_XDPRINTF_("%s[%u]: CR0[WRITE]: PG bit set logic\n", __func__, cpuid);
			CASM_FUNCCALL(xmhfhw_cpu_invvpid, VMX_INVVPID_SINGLECONTEXT, src_slabid, 0, 0);

		}

		if ((cr0 ^ old_cr0) & update_bits){
			_XDPRINTF_("%s[%u]: CR0[WRITE]: flushing TLB(update bits)\n", __func__, cpuid);
			CASM_FUNCCALL(xmhfhw_cpu_invvpid, VMX_INVVPID_SINGLECONTEXT, src_slabid, 0, 0);
		}

	//_XDPRINTF_("%s[%u]: CR0[WRITE]: old=0x%08x, new=0x%08x, final=0x%08x\n",
	//		__func__, cpuid, old_cr0, cr0, hw_cr0);

}


u32 xcihub_icptcrx_handle_cr4(u32 cpuid, u32 src_slabid, u32 cr4){
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;
	u32 old_cr4 = xcihub_icptcrx_read_cr4(cpuid);
	u32 pdptr_bits = CR4_PGE | CR4_PSE | CR4_PAE |
					   CR4_SMEP | CR4_SMAP | CR4_PKE;
	u32 hw_cr4;


	memset(&spl, 0, sizeof(spl));

	_XDPRINTF_("%s[%u]: CR4[WRITE]: old=0x%08x, new=0x%08x\n",
			__func__, cpuid, old_cr4, cr4);

	if(is_paging_enabled(cpuid) && (cr4 & CR4_PAE)
			&& ((cr4 ^ old_cr4) & pdptr_bits) ){
		_XDPRINTF_("%s[%u]: CR4[WRITE]: PAE enabling logic.WiP!\n", __func__, cpuid);
		CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
	}

	if ((cr4 & CR4_PCIDE) && !(old_cr4 & CR4_PCIDE)) {
		_XDPRINTF_("%s[%u]: CR4[WRITE]: PCIDE logic enabling.WiP!\n", __func__, cpuid);
			CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
	}

	//set cr4 logic
	hw_cr4 = (xcihub_icptcrx_read_cr4_shadow(cpuid) & CR4_MCE) |
			(cr4 & ~CR4_MCE);

	hw_cr4 |= CR4_VMXE;

	spl.cpuid = cpuid;
	spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
	gcpustate_vmrwp->encoding = VMCS_CONTROL_CR4_SHADOW;
	gcpustate_vmrwp->value = cr4;
	XMHF_SLAB_CALLNEW(&spl);

	gcpustate_vmrwp->encoding = VMCS_GUEST_CR4;
	gcpustate_vmrwp->value = hw_cr4;
	XMHF_SLAB_CALLNEW(&spl);

	_XDPRINTF_("%s[%u]: CR4[WRITE]: old=0x%08x, new=0x%08x, final=0x%08x\n",
			__func__, cpuid, old_cr4, cr4, hw_cr4);


	if (((cr4 ^ old_cr4) & pdptr_bits) ||
		    (!(cr4 & CR4_PCIDE) && (old_cr4 & CR4_PCIDE))){
		_XDPRINTF_("%s[%u]: CR4[WRITE]: flushing TLB\n", __func__, cpuid);
		CASM_FUNCCALL(xmhfhw_cpu_invvpid, VMX_INVVPID_SINGLECONTEXT, src_slabid, 0, 0);
	}

	if ((cr4 ^ old_cr4) & (CR4_OSXSAVE | CR4_PKE)){
		_XDPRINTF_("%s[%u]: CR4[WRITE]: Should we update cpuid?\n", __func__, cpuid);
		//CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
		CASM_FUNCCALL(xmhfhw_cpu_invvpid, VMX_INVVPID_SINGLECONTEXT, src_slabid, 0, 0);
	}

	return 0;
}

void xcihub_icptcrx(u32 cpuid, u32 src_slabid){
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;
	xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs = (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;

	u32 guest_rip;
	u32 info_vmexit_instruction_length;
	u32 info_exit_qualification;
	u32 tofrom, gpr, crx;
	u32 lmsw_op_type, lmsw_src_data;
	u32 hw_cr0;
	x86regs_t r;

	//_XDPRINTF_("%s[%u]: CRX access\n", __func__, cpuid);
	memset(&spl, 0, sizeof(spl));

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
		CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
	}

	if (crx == 0x0 && tofrom == VMX_CRX_ACCESS_TO){
#if 0
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
#endif
		xcihub_icptcrx_handle_cr0(cpuid, src_slabid, _xcihub_icptcrx_getregval(gpr, r));

	}else if (crx == 0x0 && tofrom == 0x3){
		//LMSW instruction
		lmsw_op_type = (u32) (((u32)info_exit_qualification & 0x00000040UL) >> (u32)6);
		lmsw_src_data = (u32) (((u32)info_exit_qualification & 0xFFFF0000UL) >> (u32)16);
		lmsw_src_data &= 0x0000000FUL;
		hw_cr0 = xcihub_icptcrx_read_cr0((u32)cpuid);

		_XDPRINTF_("%s[%u]: CR0 write via LMSW: hw_cr0=0x%08x, op_type=%u, src_data=0x%08x\n", __func__, cpuid,
				hw_cr0, lmsw_op_type, lmsw_src_data);

		hw_cr0 &= 0xFFFFFFF0UL;
		hw_cr0 |= lmsw_src_data;

		xcihub_icptcrx_handle_cr0(cpuid, src_slabid, hw_cr0);

	}else if(crx == 0x4 && tofrom == VMX_CRX_ACCESS_TO){
#if 0
		//CR4 write emulation
		u32 cr4_shadow = 0;
		u32 cr4_value = _xcihub_icptcrx_getregval(gpr, r);

		_XDPRINTF_("%s[%u]: CR4[WRITE], gpr=%u, value=0x%08x, tofrom=%u\n",
				__func__, cpuid, gpr, cr4_value, tofrom);

		//read CR4 shadow to get fixed 1 bits that we need to set
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
		gcpustate_vmrwp->encoding = VMCS_CONTROL_CR4_SHADOW;
		XMHF_SLAB_CALLNEW(&spl);
		cr4_shadow = gcpustate_vmrwp->value;

		_XDPRINTF_("%s[%u]: CR4[WRITE], cr4_shadow=0x%08x\n",
				__func__, cpuid, cr4_shadow);

		//propagate CR4 but set fixed 1 bits
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_GUEST_CR4;
		gcpustate_vmrwp->value = cr4_value | cr4_shadow;
		XMHF_SLAB_CALLNEW(&spl);

		//propagate CR4 read shadow as well but set fixed 1 bits
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_CONTROL_CR4_SHADOW;
		gcpustate_vmrwp->value = cr4_value | cr4_shadow;
		XMHF_SLAB_CALLNEW(&spl);

		//we need to flush logical processor VPID mappings as we emulated CR0 load above
		CASM_FUNCCALL(xmhfhw_cpu_invvpid, VMX_INVVPID_SINGLECONTEXT, src_slabid, 0, 0);
#endif

		xcihub_icptcrx_handle_cr4(cpuid, src_slabid, _xcihub_icptcrx_getregval(gpr, r));

	}else{
		_XDPRINTF_("%s[%u]: Unhandled CRx access, crx=0x%08x, gpr=%u, tofrom=%u\n", __func__, cpuid, crx, gpr, tofrom);
		CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
	}

	//skip over CRx instruction by adjusting RIP
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
	gcpustate_vmrwp->encoding = VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH;
	XMHF_SLAB_CALLNEW(&spl);
	info_vmexit_instruction_length = gcpustate_vmrwp->value;

	gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
	XMHF_SLAB_CALLNEW(&spl);
	guest_rip = gcpustate_vmrwp->value;
	guest_rip+=info_vmexit_instruction_length;

	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
	gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
	gcpustate_vmrwp->value = guest_rip;
	XMHF_SLAB_CALLNEW(&spl);

	//write interruptibility = 0
	gcpustate_vmrwp->encoding = VMCS_GUEST_INTERRUPTIBILITY;
	gcpustate_vmrwp->value = 0;
	XMHF_SLAB_CALLNEW(&spl);

	//_XDPRINTF_("%s[%u]: adjusted guest_rip=%08x\n",  __func__, cpuid, guest_rip);
}



