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
	printf("\nCPU(0x%02x): %s(): r=%p", vcpu->id, __func__, r);
	HALT_ON_ERRORCOND(0 && "Not implemented");
}

