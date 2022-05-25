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

// EMHF partition event-hub component declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_PARTEVENTHUB_H__
#define __EMHF_PARTEVENTHUB_H__

#ifndef __ASSEMBLY__

#include <hptw.h>
#include <hpt_emhf.h>

typedef struct {
	hptw_ctx_t guest_ctx;
	hptw_ctx_t host_ctx;
} guestmem_hptw_ctx_pair_t;

//XXX: FIX this
//extern u8 * _svm_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr);

//XXX: FIX this
//extern u8 * _vmx_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr);
extern void _vmx_putVMCS(VCPU *vcpu);
extern void _vmx_getVMCS(VCPU *vcpu);
extern void _vmx_dumpVMCS(VCPU *vcpu);

extern u32 rdmsr_safe(struct regs *r);

//----------------------------------------------------------------------
//exported DATA
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//exported FUNCTIONS
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------

//----------------------------------------------------------------------
//x86 ARCH. INTERFACES
//----------------------------------------------------------------------

//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------
#ifdef __AMD64__
uintptr_t * _vmx_decode_reg(u32 gpr, VCPU *vcpu, struct regs *r);
#elif defined(__I386__)
uintptr_t * _vmx_decode_reg(u32 gpr, VCPU *vcpu, struct regs *r);
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
void _vmx_inject_exception(VCPU *vcpu, u32 vector, u32 has_ec, u32 errcode);
u64 _vmx_get_guest_efer(VCPU *vcpu);
void xmhf_parteventhub_arch_x86vmx_entry(void);
u32 xmhf_parteventhub_arch_x86vmx_intercept_handler(VCPU *vcpu, struct regs *r);
void guestmem_init(VCPU *vcpu, guestmem_hptw_ctx_pair_t *ctx_pair);
void guestmem_copy_gv2h(guestmem_hptw_ctx_pair_t *ctx_pair, hptw_cpl_t cpl,
						void *dst, hpt_va_t src, size_t len);
void guestmem_copy_gp2h(guestmem_hptw_ctx_pair_t *ctx_pair, hptw_cpl_t cpl,
						void *dst, hpt_va_t src, size_t len);
#ifdef __UPDATE_INTEL_UCODE__
void handle_intel_ucode_update(VCPU *vcpu, u64 update_data);
#endif /* __UPDATE_INTEL_UCODE__ */
#ifdef __NESTED_VIRTUALIZATION__
void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmclear(VCPU *vcpu, struct regs *r);
void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmlaunch(VCPU *vcpu, struct regs *r);
void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmptrld(VCPU *vcpu, struct regs *r);
void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmptrst(VCPU *vcpu, struct regs *r);
void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmread(VCPU *vcpu, struct regs *r);
void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmresume(VCPU *vcpu, struct regs *r);
void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmwrite(VCPU *vcpu, struct regs *r);
void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmxoff(VCPU *vcpu, struct regs *r);
void xmhf_parteventhub_arch_x86vmx_handle_intercept_vmxon(VCPU *vcpu, struct regs *r);
#endif /* !__NESTED_VIRTUALIZATION__ */

//----------------------------------------------------------------------
//x86svm SUBARCH. INTERFACES
//----------------------------------------------------------------------
void xmhf_parteventhub_arch_x86svm_entry(void);
u32 xmhf_parteventhub_arch_x86svm_intercept_handler(VCPU *vcpu, struct regs *r);


#endif	//__ASSEMBLY__

#endif //__EMHF_PARTEVENTHUB_H__
