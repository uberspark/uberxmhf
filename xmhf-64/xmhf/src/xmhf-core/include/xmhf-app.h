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

// EMHF app. callback declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_APP_H__
#define __EMHF_APP_H__

#ifndef __ASSEMBLY__

//----------------------------------------------------------------------
// EMHF application related declarations
//----------------------------------------------------------------------

//generic catch-all app return codes
#define APP_SUCCESS     		(0x1)
#define APP_ERROR				(0x0)

//emhf app constant definitions
#define APP_IOINTERCEPT_CHAIN   0xA0
#define APP_IOINTERCEPT_SKIP    0xA1
#define APP_INIT_SUCCESS        0x0
#define APP_INIT_FAIL           0xFF
#define APP_CPUID_CHAIN         0x0F
#define APP_CPUID_SKIP          0xA2


//application parameter block
//for now it holds the bootsector and optional module info loaded by GRUB
//eventually this will be generic enough for both boot-time and dynamic loading
//capabilities
typedef struct {
  hva_t bootsector_ptr;
  hva_t bootsector_size;
  hva_t optionalmodule_ptr;
  hva_t optionalmodule_size;
  hva_t runtimephysmembase;
  u8 boot_drive;
  char cmdline[1024];
} APP_PARAM_BLOCK;


//EMHF application callbacks

/*
 * Called by all CPUs when XMHF boots.
 *
 * Hypapp should return APP_INIT_SUCCESS if hypapp initialization is successful.
 * Otherwise hypapp should return APP_INIT_FAIL (XMHF will halt).
 *
 * When this function is called, other CPUs are NOT quiesced. However, when
 * this function is called all CPUs are in hypervisor mode (guest has not been
 * started).
 */
extern u32 xmhf_app_main(VCPU *vcpu, APP_PARAM_BLOCK *apb);

/*
 * Called when the guest accesses some I/O port that is configured to be
 * intercepted using the I/O bitmap.
 *
 * portnum: I/O port number accessed (0 - 0xffff inclusive)
 * access_type: IO_TYPE_IN or IO_TYPE_OUT
 * access_size: IO_SIZE_BYTE or IO_SIZE_WORD or IO_SIZE_DWORD
 *
 * Hypapp should return APP_IOINTERCEPT_SKIP if the I/O port access is handled.
 * Otherwise hypapp should return APP_IOINTERCEPT_CHAIN (XMHF will perform the
 * access in hypervisor mode).
 *
 * When this function is called, other CPUs may or may not be quiesced. This is
 * configured using __XMHF_QUIESCE_CPU_IN_GUEST_MEM_PIO_TRAPS__.
 */
extern u32 xmhf_app_handleintercept_portaccess(VCPU *vcpu, struct regs *r,
                                               u32 portnum, u32 access_type,
                                               u32 access_size);

/*
 * Called when the guest accesses invalid memory in NPT / EPT.
 *
 * In nested virtualization, this function is called when EPT02 violation is
 * due to EPT01 violation. L1 will handle EPT02 violation due to EPT12
 * violation.
 *
 * gpa: guest physical address accessed
 * gva: guest virtual address accessed
 * violationcode: platform specific reason of NPT / EPT violation
 *
 * Hypapp should return APP_SUCCESS.
 *
 * When this function is called, other CPUs may or may not be quiesced. This is
 * configured using __XMHF_QUIESCE_CPU_IN_GUEST_MEM_PIO_TRAPS__.
 */
extern u32 xmhf_app_handleintercept_hwpgtblviolation(VCPU *vcpu, struct regs *r,
                                                     gpa_t gpa, gva_t gva,
                                                     u64 violationcode);

/*
 * Called when the guest tries to shutdown / restart.
 *
 * Hypapp should call xmhf_baseplatform_reboot() to perform the restart.
 * xmhf_baseplatform_reboot() will never return.
 *
 * When this function is called, other CPUs are NOT quiesced. However, all
 * CPUs are going to call xmhf_app_handleshutdown() concurrently (all CPUs
 * are in hypervisor mode).
 */
extern void xmhf_app_handleshutdown(VCPU *vcpu, struct regs *r);

/*
 * Called when the guest tries to perform VMCALL / VMMCALL.
 *
 * In nested virtualization, this function is called when r->eax is within
 * range [VMX_HYPAPP_L2_VMCALL_MIN, VMX_HYPAPP_L2_VMCALL_MAX] (inclusive).
 * Otherwise the hyper call is handled by L1.
 *
 * Hypapp should return APP_SUCCESS if hyper call is handled. Otherwise hypapp
 * should return APP_ERROR (XMHF will halt).
 *
 * When this function is called, other CPUs are quiesced.
 */
extern u32 xmhf_app_handlehypercall(VCPU *vcpu, struct regs *r);

/*
 * Called when the guest tries to modify MTRR.
 *
 * Hypapp should return APP_SUCCESS if MTRR can be modified (for VMX, XMHF will
 * modify MTRR). Otherwise hypapp should return APP_ERROR (XMHF will halt).
 *
 * When this function is called, other CPUs are NOT quiesced. For formal
 * verification purpose, XMHF assumes that the hypapp does not access XMHF's
 * global variables.
 */
extern u32 xmhf_app_handlemtrr(VCPU *vcpu, u32 msr, u64 val);

/*
 * Called when the guest executes CPUID.
 *
 * The intention of this function is to allow the guest to detect presence of
 * the hypapp. If the hypapp handles the CPUID instruction, it should return
 * APP_CPUID_SKIP. Otherwise the hypapp should return APP_CPUID_CHAIN and XMHF
 * will handle the CPUID instruction.
 *
 * When this function is called, other CPUs are NOT quiesced. For formal
 * verification purpose, XMHF assumes that the hypapp does not access XMHF's
 * global variables.
 */
extern u32 xmhf_app_handlecpuid(VCPU *vcpu, struct regs *r);

/*
 * Called when the CPU receives an interrupt from hardware during guest mode.
 *
 * In VMX, this function is only called when "External-interrupt exiting" VMCS
 * control bit is set to 1 by the hypapp.
 *
 * Currently call to this function is NOT implemented in nested virtualization.
 * All such events from nested virtualization are sent to the guest hypervisor.
 *
 * Hypapp should return APP_SUCCESS.
 *
 * When this function is called, other CPUs are NOT quiesced. For formal
 * verification purpose, XMHF assumes that the hypapp does not access XMHF's
 * global variables.
 */
extern u32 xmhf_app_handle_external_interrupt(VCPU *vcpu, struct regs *r);

/*
 * Called when the guest is able to receive an interrupt (EFLAGS.IF = 1).
 *
 * In VMX, this function is only called when "Interrupt-window exiting" VMCS
 * control bit is set to 1 by the hypapp.
 *
 * Currently call to this function is NOT implemented in nested virtualization.
 * All such events from nested virtualization are sent to the guest hypervisor.
 *
 * Hypapp should return APP_SUCCESS.
 *
 * When this function is called, other CPUs are NOT quiesced. For formal
 * verification purpose, XMHF assumes that the hypapp does not access XMHF's
 * global variables.
 */
extern u32 xmhf_app_handle_interrupt_window(VCPU *vcpu, struct regs *r);

#ifdef __NESTED_VIRTUALIZATION__
/*
 * Called when the guest enters to L2 from L1 (VMENTRY in VMX).
 *
 * This function, together with xmhf_app_handle_nest_exit(), allows the hypapp
 * to track which virtual machine is currently running.
 *
 * Hypapp should return APP_SUCCESS.
 *
 * When this function is called, other CPUs are NOT quiesced. For formal
 * verification purpose, XMHF assumes that the hypapp does not access XMHF's
 * global variables.
 */
extern u32 xmhf_app_handle_nest_entry(VCPU *vcpu, struct regs *r);

/*
 * Called when the guest exits to L1 from L2 (VMEXIT in VMX).
 *
 * This function, together with xmhf_app_handle_nest_entry(), allows the hypapp
 * to track which virtual machine is currently running.
 *
 * Hypapp should return APP_SUCCESS.
 *
 * When this function is called, other CPUs are NOT quiesced. For formal
 * verification purpose, XMHF assumes that the hypapp does not access XMHF's
 * global variables.
 */
extern u32 xmhf_app_handle_nest_exit(VCPU *vcpu, struct regs *r);
#endif /* __NESTED_VIRTUALIZATION__ */

#endif	//__ASSEMBLY__

#endif	// __EMHF_APP_H__
