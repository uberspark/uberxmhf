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

// peh-x86vmx-nested.c
// Intercept handlers for nested virtualization
// author: Eric Li (xiaoyili@andrew.cmu.edu)
#include <xmhf.h>

union _vmx_decode_m64_inst_info {
	struct {
		u32 scaling: 2;
		u32 undefined6_2: 5;
		u32 address_size: 3;
		u32 zero_10: 1;
		u32 undefined14_11: 4;
		u32 segment_register: 3;
		u32 index_reg: 4;
		u32 index_reg_invalid: 1;
		u32 base_reg: 4;
		u32 base_reg_invalid: 1;
		u32 undefined_31_28: 4;
	};
	u32 raw;
};

/*
 * Given a segment index, return the segment offset
 * TODO: do we need to check access rights?
 */
static u64 _vmx_decode_seg(u32 seg, VCPU *vcpu)
{
	switch (seg) {
		case 0: return vcpu->vmcs.guest_ES_base;
		case 1: return vcpu->vmcs.guest_CS_base;
		case 2: return vcpu->vmcs.guest_SS_base;
		case 3: return vcpu->vmcs.guest_DS_base;
		case 4: return vcpu->vmcs.guest_FS_base;
		case 5: return vcpu->vmcs.guest_GS_base;
		default:
			HALT_ON_ERRORCOND(0 && "Unexpected segment");
			return 0;
	}
}

/*
 * Decode the operand for instructions that take one m64 operand. Following
 * Table 26-13. Format of the VM-Exit Instruction-Information Field as Used
 * for VMCLEAR, VMPTRLD, VMPTRST, VMXON, XRSTORS, and XSAVES in Intel's
 * System Programming Guide, Order Number 325384
 */
static u64 _vmx_decode_m64(VCPU *vcpu, struct regs *r)
{
	union _vmx_decode_m64_inst_info inst_info;
	u64 ans = 0;
	inst_info.raw = vcpu->vmcs.info_vmx_instruction_information;
	HALT_ON_ERRORCOND(inst_info.zero_10 == 0);
	ans = _vmx_decode_seg(inst_info.segment_register, vcpu);
	ans += vcpu->vmcs.info_exit_qualification;
	if (!inst_info.base_reg_invalid) {
		ans += *_vmx_decode_reg(inst_info.base_reg, vcpu, r);
	}
	if (!inst_info.index_reg_invalid) {
		ans += *_vmx_decode_reg(inst_info.index_reg, vcpu, r) << inst_info.scaling;
	}
	switch (inst_info.address_size) {
	case 0:	/* 16-bit */
		ans &= 0xffffULL;
		break;
	case 1:	/* 32-bit */
		ans &= 0xffffffffULL;
		break;
	case 2:	/* 64-bit */
		break;
	default:
		HALT_ON_ERRORCOND(0 && "Unexpected address size");
		break;
	}
	return ans;
}

// TODO: also need to virtualize VMCALL

void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmclear(VCPU *vcpu, struct regs *r)
{
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmlaunch(VCPU *vcpu, struct regs *r)
{
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmptrld(VCPU *vcpu, struct regs *r)
{
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmptrst(VCPU *vcpu, struct regs *r)
{
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmread(VCPU *vcpu, struct regs *r)
{
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmresume(VCPU *vcpu, struct regs *r)
{
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmwrite(VCPU *vcpu, struct regs *r)
{
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmxoff(VCPU *vcpu, struct regs *r)
{
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmxon(VCPU *vcpu, struct regs *r)
{
	if ((vcpu->vmcs.guest_CR0 & CR0_PE) == 0 ||
		(vcpu->vmcs.guest_CR4 & CR4_VMXE) == 0 ||
		(vcpu->vmcs.guest_RFLAGS & EFLAGS_VM) ||
		((_vmx_get_guest_efer(vcpu) & (1ULL << EFER_LMA)) && !VCPU_g64(vcpu))) {
		_vmx_inject_exception(vcpu, CPU_EXCEPTION_UD, 0, 0);
	} else if (!vcpu->vmx_nested_is_vmx_operation) {
		// TODO: perform checks (CPL > 0, ...)
		u64 addr = _vmx_decode_m64(vcpu, r);
		gpa_t vmxon_ptr;
		guestmem_hptw_ctx_pair_t ctx_pair;
		HALT_ON_ERRORCOND(0 && "Checks not implemented");
		guestmem_init(vcpu, &ctx_pair);
		guestmem_copy_gv2h(&ctx_pair, 0, &vmxon_ptr, addr, sizeof(vmxon_ptr));
		HALT_ON_ERRORCOND(PA_PAGE_ALIGNED_4K(vmxon_ptr));
		vcpu->vmx_nested_is_vmx_operation = 1;
		vcpu->vmx_nested_vmxon_pointer = vmxon_ptr;
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	} else {
		/* This may happen if guest tries nested virtualization */
		printf("\nNot implemented, HALT!");
		HALT();
	}
}

