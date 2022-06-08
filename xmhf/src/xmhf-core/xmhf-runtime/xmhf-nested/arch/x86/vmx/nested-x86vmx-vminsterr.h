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

// nested-x86vmx-vminsterr.h
// VM instruction error numbers
// author: Eric Li (xiaoyili@andrew.cmu.edu)

#ifndef _NESTED_X86VMX_VMINSTERR_H_
#define _NESTED_X86VMX_VMINSTERR_H_

/* VMCALL executed in VMX root operation */
#define VM_INST_ERRNO_VMCALL_IN_VMXROOT 1
/* VMCLEAR with invalid physical address */
#define VM_INST_ERRNO_VMCLEAR_INVALID_PHY_ADDR 2
/* VMCLEAR with VMXON pointer */
#define VM_INST_ERRNO_VMCLEAR_VMXON_PTR 3
/* VMLAUNCH with non-clear VMCS */
#define VM_INST_ERRNO_VMLAUNCH_NONCLEAR_VMCS 4
/* VMRESUME with non-launched VMCS */
#define VM_INST_ERRNO_VMRESUME_NONLAUNCH_VMCS 5
/* VMRESUME after VMXOFF (VMXOFF and VMXON between VMLAUNCH and VMRESUME) */
#define VM_INST_ERRNO_VMLAUNCH_AFTER_VMXOFF 6
/* VM entry with invalid control field(s) */
#define VM_INST_ERRNO_VMENTRY_INVALID_CTRL 7
/* VM entry with invalid host-state field(s) */
#define VM_INST_ERRNO_VMENTRY_INVALID_HOST 8
/* VMPTRLD with invalid physical address */
#define VM_INST_ERRNO_VMPTRLD_INVALID_PHY_ADDR 9
/* VMPTRLD with VMXON pointer */
#define VM_INST_ERRNO_VMPTRLD_VMXON_PTR 10
/* VMPTRLD with incorrect VMCS revision identifier */
#define VM_INST_ERRNO_VMPTRLD_WITH_INCORRECT_VMCS_REV_ID 11
/* VMREAD/VMWRITE from/to unsupported VMCS component */
#define VM_INST_ERRNO_VMRDWR_UNSUPP_VMCS_COMP 12
/* VMWRITE to read-only VMCS component */
#define VM_INST_ERRNO_VMWRITE_RO_VMCS_COMP 13
/* VMXON executed in VMX root operation */
#define VM_INST_ERRNO_VMXON_IN_VMXROOT 15
/* VM entry with invalid executive-VMCS pointer */
#define VM_INST_ERRNO_VMENTRY_INVALID_EXEC_VMCS_PTR 16
/* VM entry with non-launched executive VMCS */
#define VM_INST_ERRNO_VMENTRY_NONLAUNCH_EXEC_VMCS 17
/* VM entry with executive-VMCS pointer not VMXON pointer */
#define VM_INST_ERRNO_VMENTRY_EXEC_VMCS_PTR_NOT_VMXON_PTR 18
/* VMCALL with non-clear VMCS */
#define VM_INST_ERRNO_VMCALL_NONCLEAR_VMCS 19
/* VMCALL with invalid VM-exit control fields */
#define VM_INST_ERRNO_VMCALL_INVALID_VMEXIT_CTRL 20
/* VMCALL with incorrect MSEG revision identifier */
#define VM_INST_ERRNO_VMCALL_INCORRECT_MSEG_REV_ID 22
/* VMXOFF under dual-monitor treatment of SMIs and SMM */
#define VM_INST_ERRNO_VMXOFF_UNDER_DUAL_MONITOR_SMI_SMM 23
/* VMCALL with invalid SMM-monitor features */
#define VM_INST_ERRNO_VMCALL_INVALID_SMM_MONITOR_FEATURE 24
/* VM entry with invalid VM-execution control fields in executive VMCS */
#define VM_INST_ERRNO_VMENTRY_INVALID_VMEXEC_CTRL_FIELD_EXEC_VMCS 25
/* VM entry with events blocked by MOV SS */
#define VM_INST_ERRNO_VMENTRY_EVENT_BLOCK_MOVSS 26
/* Invalid operand to INVEPT/INVVPID */
#define VM_INST_ERRNO_INVALID_OPERAND_INVEPT_INVVPID 28

#endif /* _NESTED_X86VMX_VMINSTERR_H_ */

