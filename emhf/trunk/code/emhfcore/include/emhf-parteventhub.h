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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

//XXX: FIX this
extern u8 * _svm_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr);

//XXX: FIX this
extern u8 * _vmx_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr);
extern void _vmx_putVMCS(VCPU *vcpu);
extern void _vmx_getVMCS(VCPU *vcpu);
extern void _vmx_dumpVMCS(VCPU *vcpu);

//exported functions
u32 emhf_parteventhub_intercept_handler_x86svm(VCPU *vcpu, struct regs *r);
u32 emhf_parteventhub_intercept_handler_x86vmx(VCPU *vcpu, struct regs *r);



#endif	//__ASSEMBLY__

#endif //__EMHF_PARTEVENTHUB_H__

