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

// EMHF nested virtualization component declarations
// author: Eric Li (xiaoyili@andrew.cmu.edu)

#ifndef __EMHF_NESTED_H__
#define __EMHF_NESTED_H__

/* Modes for vcpu->vmx_nested_vmx_operation_mode */
#define NESTED_VMX_MODE_DISABLED	0
#define NESTED_VMX_MODE_ROOT		1
#define NESTED_VMX_MODE_NONROOT		2

#ifndef __ASSEMBLY__

//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------

//----------------------------------------------------------------------
//x86 ARCH. INTERFACES
//----------------------------------------------------------------------

//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------

void xmhf_nested_arch_x86vmx_vcpu_init(VCPU *vcpu);

void xmhf_nested_arch_x86vmx_handle_nmi(VCPU * vcpu);
void xmhf_nested_arch_x86vmx_handle_vmexit(VCPU *vcpu, struct regs *r);
void xmhf_nested_arch_x86vmx_handle_vmentry_fail(VCPU *vcpu, bool is_resume);
void xmhf_nested_arch_x86vmx_handle_invept(VCPU *vcpu, struct regs *r);
void xmhf_nested_arch_x86vmx_handle_invvpid(VCPU *vcpu, struct regs *r);
void xmhf_nested_arch_x86vmx_handle_vmclear(VCPU *vcpu, struct regs *r);
void xmhf_nested_arch_x86vmx_handle_vmlaunch_vmresume(VCPU *vcpu,
													  struct regs *r,
													  bool is_vmresume);
void xmhf_nested_arch_x86vmx_handle_vmptrld(VCPU *vcpu, struct regs *r);
void xmhf_nested_arch_x86vmx_handle_vmptrst(VCPU *vcpu, struct regs *r);
void xmhf_nested_arch_x86vmx_handle_vmread(VCPU *vcpu, struct regs *r);
void xmhf_nested_arch_x86vmx_handle_vmwrite(VCPU *vcpu, struct regs *r);
void xmhf_nested_arch_x86vmx_handle_vmxoff(VCPU *vcpu, struct regs *r);
void xmhf_nested_arch_x86vmx_handle_vmxon(VCPU *vcpu, struct regs *r);

void xmhf_nested_arch_x86vmx_update_nested_nmi(VCPU * vcpu);
void *xmhf_nested_arch_x86vmx_access_ept02(VCPU * vcpu, void* cache_line,
										   hpt_prot_t access_type,
										   hpt_va_t va, size_t requested_sz,
										   size_t *avail_sz);
bool xmhf_nested_arch_x86vmx_get_ept12(VCPU * vcpu, gpa_t * ept12);
void xmhf_nested_arch_x86vmx_set_ept12(VCPU * vcpu, bool enable, gpa_t ept12);
void xmhf_nested_arch_x86vmx_flush_ept02(VCPU *vcpu, u32 flags);

#endif	//__ASSEMBLY__

#endif //__EMHF_NESTED_H__
