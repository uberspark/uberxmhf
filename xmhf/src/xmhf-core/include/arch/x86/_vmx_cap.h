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

// _vmx_cap.h - Determine Intel VMX capabilities
// author: Eric Li (xiaoyili@andrew.cmu.edu)

#ifndef _VMX_CAP_H_
#define _VMX_CAP_H_

/* External-interrupt exiting */
#define VMX_BINBASED_EXTERNAL_INTERRUPT_EXITING 0
static inline bool _vmx_has_external_interrupt_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR] >> 32) &
			(1U << VMX_BINBASED_EXTERNAL_INTERRUPT_EXITING));
}

/* NMI exiting */
#define VMX_BINBASED_NMI_EXITING 3
static inline bool _vmx_has_nmi_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR] >> 32) &
			(1U << VMX_BINBASED_NMI_EXITING));
}

/* Virtual NMIs */
#define VMX_BINBASED_VIRTUAL_NMIS 5
static inline bool _vmx_has_virtual_nmis(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR] >> 32) &
			(1U << VMX_BINBASED_VIRTUAL_NMIS));
}

/* Activate VMX-preemption timer */
#define VMX_BINBASED_ACTIVATE_VMX_PREEMPTION_TIMER 6
static inline bool _vmx_has_activate_vmx_preemption_timer(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR] >> 32) &
			(1U << VMX_BINBASED_ACTIVATE_VMX_PREEMPTION_TIMER));
}

/* Process posted interrupts */
#define VMX_BINBASED_PROCESS_POSTED_INTERRUPTS 7
static inline bool _vmx_has_process_posted_interrupts(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR] >> 32) &
			(1U << VMX_BINBASED_PROCESS_POSTED_INTERRUPTS));
}

/* Interrupt-window exiting */
#define VMX_PROCBASED_INTERRUPT_WINDOW_EXITING 2
static inline bool _vmx_has_interrupt_window_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_INTERRUPT_WINDOW_EXITING));
}

/* Use TSC offsetting */
#define VMX_PROCBASED_USE_TSC_OFFSETTING 3
static inline bool _vmx_has_use_tsc_offsetting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_USE_TSC_OFFSETTING));
}

/* HLT exiting */
#define VMX_PROCBASED_HLT_EXITING 7
static inline bool _vmx_has_hlt_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_HLT_EXITING));
}

/* INVLPG exiting */
#define VMX_PROCBASED_INVLPG_EXITING 9
static inline bool _vmx_has_invlpg_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_INVLPG_EXITING));
}

/* MWAIT exiting */
#define VMX_PROCBASED_MWAIT_EXITING 10
static inline bool _vmx_has_mwait_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_MWAIT_EXITING));
}

/* RDPMC exiting */
#define VMX_PROCBASED_RDPMC_EXITING 11
static inline bool _vmx_has_rdpmc_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_RDPMC_EXITING));
}

/* RDTSC exiting */
#define VMX_PROCBASED_RDTSC_EXITING 12
static inline bool _vmx_has_rdtsc_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_RDTSC_EXITING));
}

/* CR3-load exiting */
#define VMX_PROCBASED_CR3_LOAD_EXITING 15
static inline bool _vmx_has_cr3_load_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_CR3_LOAD_EXITING));
}

/* CR3-store exiting */
#define VMX_PROCBASED_CR3_STORE_EXITING 16
static inline bool _vmx_has_cr3_store_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_CR3_STORE_EXITING));
}

/* Activate tertiary controls */
#define VMX_PROCBASED_ACTIVATE_TERTIARY_CONTROLS 17
static inline bool _vmx_has_activate_tertiary_controls(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_ACTIVATE_TERTIARY_CONTROLS));
}

/* CR8-load exiting */
#define VMX_PROCBASED_CR8_LOAD_EXITING 19
static inline bool _vmx_has_cr8_load_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_CR8_LOAD_EXITING));
}

/* CR8-store exiting */
#define VMX_PROCBASED_CR8_STORE_EXITING 20
static inline bool _vmx_has_cr8_store_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_CR8_STORE_EXITING));
}

/* Use TPR shadow */
#define VMX_PROCBASED_USE_TPR_SHADOW 21
static inline bool _vmx_has_use_tpr_shadow(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_USE_TPR_SHADOW));
}

/* NMI-window exiting */
#define VMX_PROCBASED_NMI_WINDOW_EXITING 22
static inline bool _vmx_has_nmi_window_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_NMI_WINDOW_EXITING));
}

/* MOV-DR exiting */
#define VMX_PROCBASED_MOV_DR_EXITING 23
static inline bool _vmx_has_mov_dr_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_MOV_DR_EXITING));
}

/* Unconditional I/O exiting */
#define VMX_PROCBASED_UNCONDITIONAL_IO_EXITING 24
static inline bool _vmx_has_unconditional_io_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_UNCONDITIONAL_IO_EXITING));
}

/* Use I/O bitmaps */
#define VMX_PROCBASED_USE_IO_BITMAPS 25
static inline bool _vmx_has_use_io_bitmaps(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_USE_IO_BITMAPS));
}

/* Monitor trap flag */
#define VMX_PROCBASED_MONITOR_TRAP_FLAG 27
static inline bool _vmx_has_monitor_trap_flag(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_MONITOR_TRAP_FLAG));
}

/* Use MSR bitmaps */
#define VMX_PROCBASED_USE_MSR_BITMAPS 28
static inline bool _vmx_has_use_msr_bitmaps(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_USE_MSR_BITMAPS));
}

/* MONITOR exiting */
#define VMX_PROCBASED_MONITOR_EXITING 29
static inline bool _vmx_has_monitor_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_MONITOR_EXITING));
}

/* PAUSE exiting */
#define VMX_PROCBASED_PAUSE_EXITING 30
static inline bool _vmx_has_pause_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_PAUSE_EXITING));
}

/* Activate secondary controls */
#define VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS 31
static inline bool _vmx_has_activate_secondary_controls(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR] >> 32) &
			(1U << VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS));
}

/* Virtualize APIC accesses */
#define VMX_SECPROCBASED_VIRTUALIZE_APIC_ACCESS 0
static inline bool _vmx_has_virtualize_apic_access(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_VIRTUALIZE_APIC_ACCESS));
}

/* Enable EPT */
#define VMX_SECPROCBASED_ENABLE_EPT 1
static inline bool _vmx_has_enable_ept(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_ENABLE_EPT));
}

/* Descriptor-table exiting */
#define VMX_SECPROCBASED_DESCRIPTOR_TABLE_EXITING 2
static inline bool _vmx_has_descriptor_table_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_DESCRIPTOR_TABLE_EXITING));
}

/* Enable RDTSCP */
#define VMX_SECPROCBASED_ENABLE_RDTSCP 3
static inline bool _vmx_has_enable_rdtscp(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_ENABLE_RDTSCP));
}

/* Virtualize x2APIC mode */
#define VMX_SECPROCBASED_VIRTUALIZE_X2APIC_MODE 4
static inline bool _vmx_has_virtualize_x2apic_mode(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_VIRTUALIZE_X2APIC_MODE));
}

/* Enable VPID */
#define VMX_SECPROCBASED_ENABLE_VPID 5
static inline bool _vmx_has_enable_vpid(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_ENABLE_VPID));
}

/* WBINVD exiting */
#define VMX_SECPROCBASED_WBINVD_EXITING 6
static inline bool _vmx_has_wbinvd_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_WBINVD_EXITING));
}

/* Unrestricted guest */
#define VMX_SECPROCBASED_UNRESTRICTED_GUEST 7
static inline bool _vmx_has_unrestricted_guest(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_UNRESTRICTED_GUEST));
}

/* APIC-register virtualization */
#define VMX_SECPROCBASED_APIC_REGISTER_VIRTUALIZATION 8
static inline bool _vmx_has_apic_register_virtualization(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_APIC_REGISTER_VIRTUALIZATION));
}

/* Virtual-interrupt delivery */
#define VMX_SECPROCBASED_VIRTUAL_INTERRUPT_DELIVERY 9
static inline bool _vmx_has_virtual_interrupt_delivery(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_VIRTUAL_INTERRUPT_DELIVERY));
}

/* PAUSE-loop exiting */
#define VMX_SECPROCBASED_PAUSE_LOOP_EXITING 10
static inline bool _vmx_has_pause_loop_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_PAUSE_LOOP_EXITING));
}

/* RDRAND exiting */
#define VMX_SECPROCBASED_RDRAND_EXITING 11
static inline bool _vmx_has_rdrand_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_RDRAND_EXITING));
}

/* Enable INVPCID */
#define VMX_SECPROCBASED_ENABLE_INVPCID 12
static inline bool _vmx_has_enable_invpcid(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_ENABLE_INVPCID));
}

/* Enable VM functions */
#define VMX_SECPROCBASED_ENABLE_VM_FUNCTIONS 13
static inline bool _vmx_has_enable_vm_functions(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_ENABLE_VM_FUNCTIONS));
}

/* VMCS shadowing */
#define VMX_SECPROCBASED_VMCS_SHADOWING 14
static inline bool _vmx_has_vmcs_shadowing(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_VMCS_SHADOWING));
}

/* Enable ENCLS exiting */
#define VMX_SECPROCBASED_ENABLE_ENCLS_EXITING 15
static inline bool _vmx_has_enable_encls_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_ENABLE_ENCLS_EXITING));
}

/* RDSEED exiting */
#define VMX_SECPROCBASED_RDSEED_EXITING 16
static inline bool _vmx_has_rdseed_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_RDSEED_EXITING));
}

/* Enable PML */
#define VMX_SECPROCBASED_ENABLE_PML 17
static inline bool _vmx_has_enable_pml(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_ENABLE_PML));
}

/* EPT-violation #VE */
#define VMX_SECPROCBASED_EPT_VIOLATION_VE 18
static inline bool _vmx_has_ept_violation_ve(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_EPT_VIOLATION_VE));
}

/* Conceal VMX from PT */
#define VMX_SECPROCBASED_CONCEAL_VMX_FROM_PT 19
static inline bool _vmx_has_conceal_vmx_from_pt(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_CONCEAL_VMX_FROM_PT));
}

/* Enable XSAVES/XRSTORS */
#define VMX_SECPROCBASED_ENABLE_XSAVES_XRSTORS 20
static inline bool _vmx_has_enable_xsaves_xrstors(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_ENABLE_XSAVES_XRSTORS));
}

/* Mode-based execute control for EPT */
#define VMX_SECPROCBASED_MODE_BASED_EXECUTE_CONTROL_FOR_EPT 22
static inline bool _vmx_has_mode_based_execute_control_for_ept(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_MODE_BASED_EXECUTE_CONTROL_FOR_EPT));
}

/* Sub-page write permissions for EPT */
#define VMX_SECPROCBASED_SUB_PAGE_WRITE_PERMISSIONS_FOR_EPT 23
static inline bool _vmx_has_sub_page_write_permissions_for_ept(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_SUB_PAGE_WRITE_PERMISSIONS_FOR_EPT));
}

/* Intel PT uses guest physical addresses */
#define VMX_SECPROCBASED_INTEL_PT_USES_GUEST_PHYSICAL_ADDRESSES 24
static inline bool _vmx_has_intel_pt_uses_guest_physical_addresses(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_INTEL_PT_USES_GUEST_PHYSICAL_ADDRESSES));
}

/* Use TSC scaling */
#define VMX_SECPROCBASED_USE_TSC_SCALING 25
static inline bool _vmx_has_use_tsc_scaling(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_USE_TSC_SCALING));
}

/* Enable user wait and pause */
#define VMX_SECPROCBASED_ENABLE_USER_WAIT_AND_PAUSE 26
static inline bool _vmx_has_enable_user_wait_and_pause(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_ENABLE_USER_WAIT_AND_PAUSE));
}

/* Enable ENCLV exiting */
#define VMX_SECPROCBASED_ENABLE_ENCLV_EXITING 28
static inline bool _vmx_has_enable_enclv_exiting(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR] >> 32) &
			(1U << VMX_SECPROCBASED_ENABLE_ENCLV_EXITING));
}

/* Save debug controls */
#define VMX_VMEXIT_SAVE_DEBUG_CONTROLS 2
static inline bool _vmx_has_vmexit_save_debug_controls(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] >> 32) &
			(1U << VMX_VMEXIT_SAVE_DEBUG_CONTROLS));
}

/* Host address-space size */
#define VMX_VMEXIT_HOST_ADDRESS_SPACE_SIZE 9
static inline bool _vmx_has_vmexit_host_address_space_size(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] >> 32) &
			(1U << VMX_VMEXIT_HOST_ADDRESS_SPACE_SIZE));
}

/* Load IA32_PERF_GLOBAL_CTRL */
#define VMX_VMEXIT_LOAD_IA32_PERF_GLOBAL_CTRL 12
static inline bool _vmx_has_vmexit_load_ia32_perf_global_ctrl(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] >> 32) &
			(1U << VMX_VMEXIT_LOAD_IA32_PERF_GLOBAL_CTRL));
}

/* Acknowledge interrupt on exit */
#define VMX_VMEXIT_ACKNOWLEDGE_INTERRUPT_ON_EXIT 15
static inline bool _vmx_has_vmexit_acknowledge_interrupt_on_exit(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] >> 32) &
			(1U << VMX_VMEXIT_ACKNOWLEDGE_INTERRUPT_ON_EXIT));
}

/* Save IA32_PAT */
#define VMX_VMEXIT_SAVE_IA32_PAT 18
static inline bool _vmx_has_vmexit_save_ia32_pat(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] >> 32) &
			(1U << VMX_VMEXIT_SAVE_IA32_PAT));
}

/* Load IA32_PAT */
#define VMX_VMEXIT_LOAD_IA32_PAT 19
static inline bool _vmx_has_vmexit_load_ia32_pat(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] >> 32) &
			(1U << VMX_VMEXIT_LOAD_IA32_PAT));
}

/* Save IA32_EFER */
#define VMX_VMEXIT_SAVE_IA32_EFER 20
static inline bool _vmx_has_vmexit_save_ia32_efer(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] >> 32) &
			(1U << VMX_VMEXIT_SAVE_IA32_EFER));
}

/* Load IA32_EFER */
#define VMX_VMEXIT_LOAD_IA32_EFER 21
static inline bool _vmx_has_vmexit_load_ia32_efer(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] >> 32) &
			(1U << VMX_VMEXIT_LOAD_IA32_EFER));
}

/* Save VMX-preemption timer value */
#define VMX_VMEXIT_SAVE_VMX_PREEMPTION_TIMER_VALUE 22
static inline bool _vmx_has_vmexit_save_vmx_preemption_timer_value(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] >> 32) &
			(1U << VMX_VMEXIT_SAVE_VMX_PREEMPTION_TIMER_VALUE));
}

/* Clear IA32_BNDCFGS */
#define VMX_VMEXIT_CLEAR_IA32_BNDCFGS 23
static inline bool _vmx_has_vmexit_clear_ia32_bndcfgs(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] >> 32) &
			(1U << VMX_VMEXIT_CLEAR_IA32_BNDCFGS));
}

/* Conceal VMX from PT */
#define VMX_VMEXIT_CONCEAL_VMX_FROM_PT 24
static inline bool _vmx_has_vmexit_conceal_vmx_from_pt(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] >> 32) &
			(1U << VMX_VMEXIT_CONCEAL_VMX_FROM_PT));
}

/* Clear IA32_RTIT_CTL */
#define VMX_VMEXIT_CLEAR_IA32_RTIT_CTL 25
static inline bool _vmx_has_vmexit_clear_ia32_rtit_ctl(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] >> 32) &
			(1U << VMX_VMEXIT_CLEAR_IA32_RTIT_CTL));
}

/* Load CET state */
#define VMX_VMEXIT_LOAD_CET_STATE 28
static inline bool _vmx_has_vmexit_load_cet_state(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] >> 32) &
			(1U << VMX_VMEXIT_LOAD_CET_STATE));
}

/* Load PKRS */
#define VMX_VMEXIT_LOAD_PKRS 29
static inline bool _vmx_has_vmexit_load_pkrs(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR] >> 32) &
			(1U << VMX_VMEXIT_LOAD_PKRS));
}

/* Load debug controls */
#define VMX_VMENTRY_LOAD_DEBUG_CONTROLS 2
static inline bool _vmx_has_vmentry_load_debug_controls(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR] >> 32) &
			(1U << VMX_VMENTRY_LOAD_DEBUG_CONTROLS));
}

/* IA-32e mode guest */
#define VMX_VMENTRY_IA_32E_MODE_GUEST 9
static inline bool _vmx_has_vmentry_ia_32e_mode_guest(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR] >> 32) &
			(1U << VMX_VMENTRY_IA_32E_MODE_GUEST));
}

/* Entry to SMM */
#define VMX_VMENTRY_ENTRY_TO_SMM 10
static inline bool _vmx_has_vmentry_entry_to_smm(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR] >> 32) &
			(1U << VMX_VMENTRY_ENTRY_TO_SMM));
}

/* Deactivate dual-monitor treatment */
#define VMX_VMENTRY_DEACTIVATE_DUAL_MONITOR_TREATMENT 11
static inline bool _vmx_has_vmentry_deactivate_dual_monitor_treatment(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR] >> 32) &
			(1U << VMX_VMENTRY_DEACTIVATE_DUAL_MONITOR_TREATMENT));
}

/* Load IA32_PERF_GLOBAL_CTRL */
#define VMX_VMENTRY_LOAD_IA32_PERF_GLOBAL_CTRL 13
static inline bool _vmx_has_vmentry_load_ia32_perf_global_ctrl(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR] >> 32) &
			(1U << VMX_VMENTRY_LOAD_IA32_PERF_GLOBAL_CTRL));
}

/* Load IA32_PAT */
#define VMX_VMENTRY_LOAD_IA32_PAT 14
static inline bool _vmx_has_vmentry_load_ia32_pat(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR] >> 32) &
			(1U << VMX_VMENTRY_LOAD_IA32_PAT));
}

/* Load IA32_EFER */
#define VMX_VMENTRY_LOAD_IA32_EFER 15
static inline bool _vmx_has_vmentry_load_ia32_efer(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR] >> 32) &
			(1U << VMX_VMENTRY_LOAD_IA32_EFER));
}

/* Load IA32_BNDCFGS */
#define VMX_VMENTRY_LOAD_IA32_BNDCFGS 16
static inline bool _vmx_has_vmentry_load_ia32_bndcfgs(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR] >> 32) &
			(1U << VMX_VMENTRY_LOAD_IA32_BNDCFGS));
}

/* Conceal VMX from PT */
#define VMX_VMENTRY_CONCEAL_VMX_FROM_PT 17
static inline bool _vmx_has_vmentry_conceal_vmx_from_pt(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR] >> 32) &
			(1U << VMX_VMENTRY_CONCEAL_VMX_FROM_PT));
}

/* Load IA32_RTIT_CTL */
#define VMX_VMENTRY_LOAD_IA32_RTIT_CTL 18
static inline bool _vmx_has_vmentry_load_ia32_rtit_ctl(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR] >> 32) &
			(1U << VMX_VMENTRY_LOAD_IA32_RTIT_CTL));
}

/* Load CET state */
#define VMX_VMENTRY_LOAD_CET_STATE 20
static inline bool _vmx_has_vmentry_load_cet_state(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR] >> 32) &
			(1U << VMX_VMENTRY_LOAD_CET_STATE));
}

/* Load PKRS */
#define VMX_VMENTRY_LOAD_PKRS 22
static inline bool _vmx_has_vmentry_load_pkrs(VCPU *vcpu)
{
	return ((vcpu->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR] >> 32) &
			(1U << VMX_VMENTRY_LOAD_PKRS));
}

#endif /* _VMX_CAP_H_ */

