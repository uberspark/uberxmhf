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

// _vmx_ctls.h - Manage Intel VMX control bits
// author: Eric Li (xiaoyili@andrew.cmu.edu)

#ifndef _VMX_CTLS_H_
#define _VMX_CTLS_H_

#ifndef __ASSEMBLY__

typedef struct vmx_ctls {
	u32 pinbased_ctls;
	u32 procbased_ctls;
	u32 procbased_ctls2;
	u32 exit_ctls;
	u32 entry_ctls;
} vmx_ctls_t;

/* Begin program-generated content */

/* External-interrupt exiting */
#define VMX_BINBASED_EXTERNAL_INTERRUPT_EXITING 0
static inline bool _vmx_hasctl_external_interrupt_exiting(vmx_ctls_t *ctls)
{
	return ctls->pinbased_ctls & (1U << VMX_BINBASED_EXTERNAL_INTERRUPT_EXITING);
}
static inline void _vmx_setctl_external_interrupt_exiting(vmx_ctls_t *ctls)
{
	ctls->pinbased_ctls |= (1U << VMX_BINBASED_EXTERNAL_INTERRUPT_EXITING);
}
static inline void _vmx_clearctl_external_interrupt_exiting(vmx_ctls_t *ctls)
{
	ctls->pinbased_ctls &= ~(1U << VMX_BINBASED_EXTERNAL_INTERRUPT_EXITING);
}

/* NMI exiting */
#define VMX_BINBASED_NMI_EXITING 3
static inline bool _vmx_hasctl_nmi_exiting(vmx_ctls_t *ctls)
{
	return ctls->pinbased_ctls & (1U << VMX_BINBASED_NMI_EXITING);
}
static inline void _vmx_setctl_nmi_exiting(vmx_ctls_t *ctls)
{
	ctls->pinbased_ctls |= (1U << VMX_BINBASED_NMI_EXITING);
}
static inline void _vmx_clearctl_nmi_exiting(vmx_ctls_t *ctls)
{
	ctls->pinbased_ctls &= ~(1U << VMX_BINBASED_NMI_EXITING);
}

/* Virtual NMIs */
#define VMX_BINBASED_VIRTUAL_NMIS 5
static inline bool _vmx_hasctl_virtual_nmis(vmx_ctls_t *ctls)
{
	return ctls->pinbased_ctls & (1U << VMX_BINBASED_VIRTUAL_NMIS);
}
static inline void _vmx_setctl_virtual_nmis(vmx_ctls_t *ctls)
{
	ctls->pinbased_ctls |= (1U << VMX_BINBASED_VIRTUAL_NMIS);
}
static inline void _vmx_clearctl_virtual_nmis(vmx_ctls_t *ctls)
{
	ctls->pinbased_ctls &= ~(1U << VMX_BINBASED_VIRTUAL_NMIS);
}

/* Activate VMX-preemption timer */
#define VMX_BINBASED_ACTIVATE_VMX_PREEMPTION_TIMER 6
static inline bool _vmx_hasctl_activate_vmx_preemption_timer(vmx_ctls_t *ctls)
{
	return ctls->pinbased_ctls & (1U << VMX_BINBASED_ACTIVATE_VMX_PREEMPTION_TIMER);
}
static inline void _vmx_setctl_activate_vmx_preemption_timer(vmx_ctls_t *ctls)
{
	ctls->pinbased_ctls |= (1U << VMX_BINBASED_ACTIVATE_VMX_PREEMPTION_TIMER);
}
static inline void _vmx_clearctl_activate_vmx_preemption_timer(vmx_ctls_t *ctls)
{
	ctls->pinbased_ctls &= ~(1U << VMX_BINBASED_ACTIVATE_VMX_PREEMPTION_TIMER);
}

/* Process posted interrupts */
#define VMX_BINBASED_PROCESS_POSTED_INTERRUPTS 7
static inline bool _vmx_hasctl_process_posted_interrupts(vmx_ctls_t *ctls)
{
	return ctls->pinbased_ctls & (1U << VMX_BINBASED_PROCESS_POSTED_INTERRUPTS);
}
static inline void _vmx_setctl_process_posted_interrupts(vmx_ctls_t *ctls)
{
	ctls->pinbased_ctls |= (1U << VMX_BINBASED_PROCESS_POSTED_INTERRUPTS);
}
static inline void _vmx_clearctl_process_posted_interrupts(vmx_ctls_t *ctls)
{
	ctls->pinbased_ctls &= ~(1U << VMX_BINBASED_PROCESS_POSTED_INTERRUPTS);
}

/* Interrupt-window exiting */
#define VMX_PROCBASED_INTERRUPT_WINDOW_EXITING 2
static inline bool _vmx_hasctl_interrupt_window_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_INTERRUPT_WINDOW_EXITING);
}
static inline void _vmx_setctl_interrupt_window_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_INTERRUPT_WINDOW_EXITING);
}
static inline void _vmx_clearctl_interrupt_window_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_INTERRUPT_WINDOW_EXITING);
}

/* Use TSC offsetting */
#define VMX_PROCBASED_USE_TSC_OFFSETTING 3
static inline bool _vmx_hasctl_use_tsc_offsetting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_USE_TSC_OFFSETTING);
}
static inline void _vmx_setctl_use_tsc_offsetting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_USE_TSC_OFFSETTING);
}
static inline void _vmx_clearctl_use_tsc_offsetting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_USE_TSC_OFFSETTING);
}

/* HLT exiting */
#define VMX_PROCBASED_HLT_EXITING 7
static inline bool _vmx_hasctl_hlt_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_HLT_EXITING);
}
static inline void _vmx_setctl_hlt_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_HLT_EXITING);
}
static inline void _vmx_clearctl_hlt_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_HLT_EXITING);
}

/* INVLPG exiting */
#define VMX_PROCBASED_INVLPG_EXITING 9
static inline bool _vmx_hasctl_invlpg_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_INVLPG_EXITING);
}
static inline void _vmx_setctl_invlpg_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_INVLPG_EXITING);
}
static inline void _vmx_clearctl_invlpg_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_INVLPG_EXITING);
}

/* MWAIT exiting */
#define VMX_PROCBASED_MWAIT_EXITING 10
static inline bool _vmx_hasctl_mwait_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_MWAIT_EXITING);
}
static inline void _vmx_setctl_mwait_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_MWAIT_EXITING);
}
static inline void _vmx_clearctl_mwait_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_MWAIT_EXITING);
}

/* RDPMC exiting */
#define VMX_PROCBASED_RDPMC_EXITING 11
static inline bool _vmx_hasctl_rdpmc_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_RDPMC_EXITING);
}
static inline void _vmx_setctl_rdpmc_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_RDPMC_EXITING);
}
static inline void _vmx_clearctl_rdpmc_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_RDPMC_EXITING);
}

/* RDTSC exiting */
#define VMX_PROCBASED_RDTSC_EXITING 12
static inline bool _vmx_hasctl_rdtsc_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_RDTSC_EXITING);
}
static inline void _vmx_setctl_rdtsc_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_RDTSC_EXITING);
}
static inline void _vmx_clearctl_rdtsc_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_RDTSC_EXITING);
}

/* CR3-load exiting */
#define VMX_PROCBASED_CR3_LOAD_EXITING 15
static inline bool _vmx_hasctl_cr3_load_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_CR3_LOAD_EXITING);
}
static inline void _vmx_setctl_cr3_load_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_CR3_LOAD_EXITING);
}
static inline void _vmx_clearctl_cr3_load_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_CR3_LOAD_EXITING);
}

/* CR3-store exiting */
#define VMX_PROCBASED_CR3_STORE_EXITING 16
static inline bool _vmx_hasctl_cr3_store_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_CR3_STORE_EXITING);
}
static inline void _vmx_setctl_cr3_store_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_CR3_STORE_EXITING);
}
static inline void _vmx_clearctl_cr3_store_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_CR3_STORE_EXITING);
}

/* Activate tertiary controls */
#define VMX_PROCBASED_ACTIVATE_TERTIARY_CONTROLS 17
static inline bool _vmx_hasctl_activate_tertiary_controls(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_ACTIVATE_TERTIARY_CONTROLS);
}
static inline void _vmx_setctl_activate_tertiary_controls(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_ACTIVATE_TERTIARY_CONTROLS);
}
static inline void _vmx_clearctl_activate_tertiary_controls(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_ACTIVATE_TERTIARY_CONTROLS);
}

/* CR8-load exiting */
#define VMX_PROCBASED_CR8_LOAD_EXITING 19
static inline bool _vmx_hasctl_cr8_load_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_CR8_LOAD_EXITING);
}
static inline void _vmx_setctl_cr8_load_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_CR8_LOAD_EXITING);
}
static inline void _vmx_clearctl_cr8_load_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_CR8_LOAD_EXITING);
}

/* CR8-store exiting */
#define VMX_PROCBASED_CR8_STORE_EXITING 20
static inline bool _vmx_hasctl_cr8_store_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_CR8_STORE_EXITING);
}
static inline void _vmx_setctl_cr8_store_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_CR8_STORE_EXITING);
}
static inline void _vmx_clearctl_cr8_store_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_CR8_STORE_EXITING);
}

/* Use TPR shadow */
#define VMX_PROCBASED_USE_TPR_SHADOW 21
static inline bool _vmx_hasctl_use_tpr_shadow(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_USE_TPR_SHADOW);
}
static inline void _vmx_setctl_use_tpr_shadow(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_USE_TPR_SHADOW);
}
static inline void _vmx_clearctl_use_tpr_shadow(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_USE_TPR_SHADOW);
}

/* NMI-window exiting */
#define VMX_PROCBASED_NMI_WINDOW_EXITING 22
static inline bool _vmx_hasctl_nmi_window_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_NMI_WINDOW_EXITING);
}
static inline void _vmx_setctl_nmi_window_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_NMI_WINDOW_EXITING);
}
static inline void _vmx_clearctl_nmi_window_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_NMI_WINDOW_EXITING);
}

/* MOV-DR exiting */
#define VMX_PROCBASED_MOV_DR_EXITING 23
static inline bool _vmx_hasctl_mov_dr_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_MOV_DR_EXITING);
}
static inline void _vmx_setctl_mov_dr_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_MOV_DR_EXITING);
}
static inline void _vmx_clearctl_mov_dr_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_MOV_DR_EXITING);
}

/* Unconditional I/O exiting */
#define VMX_PROCBASED_UNCONDITIONAL_IO_EXITING 24
static inline bool _vmx_hasctl_unconditional_io_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_UNCONDITIONAL_IO_EXITING);
}
static inline void _vmx_setctl_unconditional_io_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_UNCONDITIONAL_IO_EXITING);
}
static inline void _vmx_clearctl_unconditional_io_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_UNCONDITIONAL_IO_EXITING);
}

/* Use I/O bitmaps */
#define VMX_PROCBASED_USE_IO_BITMAPS 25
static inline bool _vmx_hasctl_use_io_bitmaps(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_USE_IO_BITMAPS);
}
static inline void _vmx_setctl_use_io_bitmaps(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_USE_IO_BITMAPS);
}
static inline void _vmx_clearctl_use_io_bitmaps(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_USE_IO_BITMAPS);
}

/* Monitor trap flag */
#define VMX_PROCBASED_MONITOR_TRAP_FLAG 27
static inline bool _vmx_hasctl_monitor_trap_flag(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_MONITOR_TRAP_FLAG);
}
static inline void _vmx_setctl_monitor_trap_flag(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_MONITOR_TRAP_FLAG);
}
static inline void _vmx_clearctl_monitor_trap_flag(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_MONITOR_TRAP_FLAG);
}

/* Use MSR bitmaps */
#define VMX_PROCBASED_USE_MSR_BITMAPS 28
static inline bool _vmx_hasctl_use_msr_bitmaps(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_USE_MSR_BITMAPS);
}
static inline void _vmx_setctl_use_msr_bitmaps(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_USE_MSR_BITMAPS);
}
static inline void _vmx_clearctl_use_msr_bitmaps(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_USE_MSR_BITMAPS);
}

/* MONITOR exiting */
#define VMX_PROCBASED_MONITOR_EXITING 29
static inline bool _vmx_hasctl_monitor_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_MONITOR_EXITING);
}
static inline void _vmx_setctl_monitor_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_MONITOR_EXITING);
}
static inline void _vmx_clearctl_monitor_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_MONITOR_EXITING);
}

/* PAUSE exiting */
#define VMX_PROCBASED_PAUSE_EXITING 30
static inline bool _vmx_hasctl_pause_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_PAUSE_EXITING);
}
static inline void _vmx_setctl_pause_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_PAUSE_EXITING);
}
static inline void _vmx_clearctl_pause_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_PAUSE_EXITING);
}

/* Activate secondary controls */
#define VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS 31
static inline bool _vmx_hasctl_activate_secondary_controls(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls & (1U << VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS);
}
static inline void _vmx_setctl_activate_secondary_controls(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls |= (1U << VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS);
}
static inline void _vmx_clearctl_activate_secondary_controls(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls &= ~(1U << VMX_PROCBASED_ACTIVATE_SECONDARY_CONTROLS);
}

/* Virtualize APIC accesses */
#define VMX_SECPROCBASED_VIRTUALIZE_APIC_ACCESS 0
static inline bool _vmx_hasctl_virtualize_apic_access(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_VIRTUALIZE_APIC_ACCESS);
}
static inline void _vmx_setctl_virtualize_apic_access(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_VIRTUALIZE_APIC_ACCESS);
}
static inline void _vmx_clearctl_virtualize_apic_access(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_VIRTUALIZE_APIC_ACCESS);
}

/* Enable EPT */
#define VMX_SECPROCBASED_ENABLE_EPT 1
static inline bool _vmx_hasctl_enable_ept(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_ENABLE_EPT);
}
static inline void _vmx_setctl_enable_ept(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_ENABLE_EPT);
}
static inline void _vmx_clearctl_enable_ept(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_ENABLE_EPT);
}

/* Descriptor-table exiting */
#define VMX_SECPROCBASED_DESCRIPTOR_TABLE_EXITING 2
static inline bool _vmx_hasctl_descriptor_table_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_DESCRIPTOR_TABLE_EXITING);
}
static inline void _vmx_setctl_descriptor_table_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_DESCRIPTOR_TABLE_EXITING);
}
static inline void _vmx_clearctl_descriptor_table_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_DESCRIPTOR_TABLE_EXITING);
}

/* Enable RDTSCP */
#define VMX_SECPROCBASED_ENABLE_RDTSCP 3
static inline bool _vmx_hasctl_enable_rdtscp(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_ENABLE_RDTSCP);
}
static inline void _vmx_setctl_enable_rdtscp(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_ENABLE_RDTSCP);
}
static inline void _vmx_clearctl_enable_rdtscp(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_ENABLE_RDTSCP);
}

/* Virtualize x2APIC mode */
#define VMX_SECPROCBASED_VIRTUALIZE_X2APIC_MODE 4
static inline bool _vmx_hasctl_virtualize_x2apic_mode(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_VIRTUALIZE_X2APIC_MODE);
}
static inline void _vmx_setctl_virtualize_x2apic_mode(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_VIRTUALIZE_X2APIC_MODE);
}
static inline void _vmx_clearctl_virtualize_x2apic_mode(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_VIRTUALIZE_X2APIC_MODE);
}

/* Enable VPID */
#define VMX_SECPROCBASED_ENABLE_VPID 5
static inline bool _vmx_hasctl_enable_vpid(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_ENABLE_VPID);
}
static inline void _vmx_setctl_enable_vpid(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_ENABLE_VPID);
}
static inline void _vmx_clearctl_enable_vpid(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_ENABLE_VPID);
}

/* WBINVD exiting */
#define VMX_SECPROCBASED_WBINVD_EXITING 6
static inline bool _vmx_hasctl_wbinvd_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_WBINVD_EXITING);
}
static inline void _vmx_setctl_wbinvd_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_WBINVD_EXITING);
}
static inline void _vmx_clearctl_wbinvd_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_WBINVD_EXITING);
}

/* Unrestricted guest */
#define VMX_SECPROCBASED_UNRESTRICTED_GUEST 7
static inline bool _vmx_hasctl_unrestricted_guest(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_UNRESTRICTED_GUEST);
}
static inline void _vmx_setctl_unrestricted_guest(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_UNRESTRICTED_GUEST);
}
static inline void _vmx_clearctl_unrestricted_guest(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_UNRESTRICTED_GUEST);
}

/* APIC-register virtualization */
#define VMX_SECPROCBASED_APIC_REGISTER_VIRTUALIZATION 8
static inline bool _vmx_hasctl_apic_register_virtualization(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_APIC_REGISTER_VIRTUALIZATION);
}
static inline void _vmx_setctl_apic_register_virtualization(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_APIC_REGISTER_VIRTUALIZATION);
}
static inline void _vmx_clearctl_apic_register_virtualization(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_APIC_REGISTER_VIRTUALIZATION);
}

/* Virtual-interrupt delivery */
#define VMX_SECPROCBASED_VIRTUAL_INTERRUPT_DELIVERY 9
static inline bool _vmx_hasctl_virtual_interrupt_delivery(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_VIRTUAL_INTERRUPT_DELIVERY);
}
static inline void _vmx_setctl_virtual_interrupt_delivery(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_VIRTUAL_INTERRUPT_DELIVERY);
}
static inline void _vmx_clearctl_virtual_interrupt_delivery(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_VIRTUAL_INTERRUPT_DELIVERY);
}

/* PAUSE-loop exiting */
#define VMX_SECPROCBASED_PAUSE_LOOP_EXITING 10
static inline bool _vmx_hasctl_pause_loop_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_PAUSE_LOOP_EXITING);
}
static inline void _vmx_setctl_pause_loop_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_PAUSE_LOOP_EXITING);
}
static inline void _vmx_clearctl_pause_loop_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_PAUSE_LOOP_EXITING);
}

/* RDRAND exiting */
#define VMX_SECPROCBASED_RDRAND_EXITING 11
static inline bool _vmx_hasctl_rdrand_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_RDRAND_EXITING);
}
static inline void _vmx_setctl_rdrand_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_RDRAND_EXITING);
}
static inline void _vmx_clearctl_rdrand_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_RDRAND_EXITING);
}

/* Enable INVPCID */
#define VMX_SECPROCBASED_ENABLE_INVPCID 12
static inline bool _vmx_hasctl_enable_invpcid(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_ENABLE_INVPCID);
}
static inline void _vmx_setctl_enable_invpcid(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_ENABLE_INVPCID);
}
static inline void _vmx_clearctl_enable_invpcid(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_ENABLE_INVPCID);
}

/* Enable VM functions */
#define VMX_SECPROCBASED_ENABLE_VM_FUNCTIONS 13
static inline bool _vmx_hasctl_enable_vm_functions(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_ENABLE_VM_FUNCTIONS);
}
static inline void _vmx_setctl_enable_vm_functions(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_ENABLE_VM_FUNCTIONS);
}
static inline void _vmx_clearctl_enable_vm_functions(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_ENABLE_VM_FUNCTIONS);
}

/* VMCS shadowing */
#define VMX_SECPROCBASED_VMCS_SHADOWING 14
static inline bool _vmx_hasctl_vmcs_shadowing(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_VMCS_SHADOWING);
}
static inline void _vmx_setctl_vmcs_shadowing(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_VMCS_SHADOWING);
}
static inline void _vmx_clearctl_vmcs_shadowing(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_VMCS_SHADOWING);
}

/* Enable ENCLS exiting */
#define VMX_SECPROCBASED_ENABLE_ENCLS_EXITING 15
static inline bool _vmx_hasctl_enable_encls_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_ENABLE_ENCLS_EXITING);
}
static inline void _vmx_setctl_enable_encls_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_ENABLE_ENCLS_EXITING);
}
static inline void _vmx_clearctl_enable_encls_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_ENABLE_ENCLS_EXITING);
}

/* RDSEED exiting */
#define VMX_SECPROCBASED_RDSEED_EXITING 16
static inline bool _vmx_hasctl_rdseed_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_RDSEED_EXITING);
}
static inline void _vmx_setctl_rdseed_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_RDSEED_EXITING);
}
static inline void _vmx_clearctl_rdseed_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_RDSEED_EXITING);
}

/* Enable PML */
#define VMX_SECPROCBASED_ENABLE_PML 17
static inline bool _vmx_hasctl_enable_pml(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_ENABLE_PML);
}
static inline void _vmx_setctl_enable_pml(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_ENABLE_PML);
}
static inline void _vmx_clearctl_enable_pml(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_ENABLE_PML);
}

/* EPT-violation #VE */
#define VMX_SECPROCBASED_EPT_VIOLATION_VE 18
static inline bool _vmx_hasctl_ept_violation_ve(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_EPT_VIOLATION_VE);
}
static inline void _vmx_setctl_ept_violation_ve(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_EPT_VIOLATION_VE);
}
static inline void _vmx_clearctl_ept_violation_ve(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_EPT_VIOLATION_VE);
}

/* Conceal VMX from PT */
#define VMX_SECPROCBASED_CONCEAL_VMX_FROM_PT 19
static inline bool _vmx_hasctl_conceal_vmx_from_pt(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_CONCEAL_VMX_FROM_PT);
}
static inline void _vmx_setctl_conceal_vmx_from_pt(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_CONCEAL_VMX_FROM_PT);
}
static inline void _vmx_clearctl_conceal_vmx_from_pt(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_CONCEAL_VMX_FROM_PT);
}

/* Enable XSAVES/XRSTORS */
#define VMX_SECPROCBASED_ENABLE_XSAVES_XRSTORS 20
static inline bool _vmx_hasctl_enable_xsaves_xrstors(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_ENABLE_XSAVES_XRSTORS);
}
static inline void _vmx_setctl_enable_xsaves_xrstors(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_ENABLE_XSAVES_XRSTORS);
}
static inline void _vmx_clearctl_enable_xsaves_xrstors(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_ENABLE_XSAVES_XRSTORS);
}

/* Mode-based execute control for EPT */
#define VMX_SECPROCBASED_MODE_BASED_EXECUTE_CONTROL_FOR_EPT 22
static inline bool _vmx_hasctl_mode_based_execute_control_for_ept(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_MODE_BASED_EXECUTE_CONTROL_FOR_EPT);
}
static inline void _vmx_setctl_mode_based_execute_control_for_ept(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_MODE_BASED_EXECUTE_CONTROL_FOR_EPT);
}
static inline void _vmx_clearctl_mode_based_execute_control_for_ept(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_MODE_BASED_EXECUTE_CONTROL_FOR_EPT);
}

/* Sub-page write permissions for EPT */
#define VMX_SECPROCBASED_SUB_PAGE_WRITE_PERMISSIONS_FOR_EPT 23
static inline bool _vmx_hasctl_sub_page_write_permissions_for_ept(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_SUB_PAGE_WRITE_PERMISSIONS_FOR_EPT);
}
static inline void _vmx_setctl_sub_page_write_permissions_for_ept(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_SUB_PAGE_WRITE_PERMISSIONS_FOR_EPT);
}
static inline void _vmx_clearctl_sub_page_write_permissions_for_ept(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_SUB_PAGE_WRITE_PERMISSIONS_FOR_EPT);
}

/* Intel PT uses guest physical addresses */
#define VMX_SECPROCBASED_INTEL_PT_USES_GUEST_PHYSICAL_ADDRESSES 24
static inline bool _vmx_hasctl_intel_pt_uses_guest_physical_addresses(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_INTEL_PT_USES_GUEST_PHYSICAL_ADDRESSES);
}
static inline void _vmx_setctl_intel_pt_uses_guest_physical_addresses(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_INTEL_PT_USES_GUEST_PHYSICAL_ADDRESSES);
}
static inline void _vmx_clearctl_intel_pt_uses_guest_physical_addresses(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_INTEL_PT_USES_GUEST_PHYSICAL_ADDRESSES);
}

/* Use TSC scaling */
#define VMX_SECPROCBASED_USE_TSC_SCALING 25
static inline bool _vmx_hasctl_use_tsc_scaling(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_USE_TSC_SCALING);
}
static inline void _vmx_setctl_use_tsc_scaling(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_USE_TSC_SCALING);
}
static inline void _vmx_clearctl_use_tsc_scaling(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_USE_TSC_SCALING);
}

/* Enable user wait and pause */
#define VMX_SECPROCBASED_ENABLE_USER_WAIT_AND_PAUSE 26
static inline bool _vmx_hasctl_enable_user_wait_and_pause(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_ENABLE_USER_WAIT_AND_PAUSE);
}
static inline void _vmx_setctl_enable_user_wait_and_pause(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_ENABLE_USER_WAIT_AND_PAUSE);
}
static inline void _vmx_clearctl_enable_user_wait_and_pause(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_ENABLE_USER_WAIT_AND_PAUSE);
}

/* Enable ENCLV exiting */
#define VMX_SECPROCBASED_ENABLE_ENCLV_EXITING 28
static inline bool _vmx_hasctl_enable_enclv_exiting(vmx_ctls_t *ctls)
{
	return ctls->procbased_ctls2 & (1U << VMX_SECPROCBASED_ENABLE_ENCLV_EXITING);
}
static inline void _vmx_setctl_enable_enclv_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 |= (1U << VMX_SECPROCBASED_ENABLE_ENCLV_EXITING);
}
static inline void _vmx_clearctl_enable_enclv_exiting(vmx_ctls_t *ctls)
{
	ctls->procbased_ctls2 &= ~(1U << VMX_SECPROCBASED_ENABLE_ENCLV_EXITING);
}

/* Save debug controls */
#define VMX_VMEXIT_SAVE_DEBUG_CONTROLS 2
static inline bool _vmx_hasctl_vmexit_save_debug_controls(vmx_ctls_t *ctls)
{
	return ctls->exit_ctls & (1U << VMX_VMEXIT_SAVE_DEBUG_CONTROLS);
}
static inline void _vmx_setctl_vmexit_save_debug_controls(vmx_ctls_t *ctls)
{
	ctls->exit_ctls |= (1U << VMX_VMEXIT_SAVE_DEBUG_CONTROLS);
}
static inline void _vmx_clearctl_vmexit_save_debug_controls(vmx_ctls_t *ctls)
{
	ctls->exit_ctls &= ~(1U << VMX_VMEXIT_SAVE_DEBUG_CONTROLS);
}

/* Host address-space size */
#define VMX_VMEXIT_HOST_ADDRESS_SPACE_SIZE 9
static inline bool _vmx_hasctl_vmexit_host_address_space_size(vmx_ctls_t *ctls)
{
	return ctls->exit_ctls & (1U << VMX_VMEXIT_HOST_ADDRESS_SPACE_SIZE);
}
static inline void _vmx_setctl_vmexit_host_address_space_size(vmx_ctls_t *ctls)
{
	ctls->exit_ctls |= (1U << VMX_VMEXIT_HOST_ADDRESS_SPACE_SIZE);
}
static inline void _vmx_clearctl_vmexit_host_address_space_size(vmx_ctls_t *ctls)
{
	ctls->exit_ctls &= ~(1U << VMX_VMEXIT_HOST_ADDRESS_SPACE_SIZE);
}

/* Load IA32_PERF_GLOBAL_CTRL */
#define VMX_VMEXIT_LOAD_IA32_PERF_GLOBAL_CTRL 12
static inline bool _vmx_hasctl_vmexit_load_ia32_perf_global_ctrl(vmx_ctls_t *ctls)
{
	return ctls->exit_ctls & (1U << VMX_VMEXIT_LOAD_IA32_PERF_GLOBAL_CTRL);
}
static inline void _vmx_setctl_vmexit_load_ia32_perf_global_ctrl(vmx_ctls_t *ctls)
{
	ctls->exit_ctls |= (1U << VMX_VMEXIT_LOAD_IA32_PERF_GLOBAL_CTRL);
}
static inline void _vmx_clearctl_vmexit_load_ia32_perf_global_ctrl(vmx_ctls_t *ctls)
{
	ctls->exit_ctls &= ~(1U << VMX_VMEXIT_LOAD_IA32_PERF_GLOBAL_CTRL);
}

/* Acknowledge interrupt on exit */
#define VMX_VMEXIT_ACKNOWLEDGE_INTERRUPT_ON_EXIT 15
static inline bool _vmx_hasctl_vmexit_acknowledge_interrupt_on_exit(vmx_ctls_t *ctls)
{
	return ctls->exit_ctls & (1U << VMX_VMEXIT_ACKNOWLEDGE_INTERRUPT_ON_EXIT);
}
static inline void _vmx_setctl_vmexit_acknowledge_interrupt_on_exit(vmx_ctls_t *ctls)
{
	ctls->exit_ctls |= (1U << VMX_VMEXIT_ACKNOWLEDGE_INTERRUPT_ON_EXIT);
}
static inline void _vmx_clearctl_vmexit_acknowledge_interrupt_on_exit(vmx_ctls_t *ctls)
{
	ctls->exit_ctls &= ~(1U << VMX_VMEXIT_ACKNOWLEDGE_INTERRUPT_ON_EXIT);
}

/* Save IA32_PAT */
#define VMX_VMEXIT_SAVE_IA32_PAT 18
static inline bool _vmx_hasctl_vmexit_save_ia32_pat(vmx_ctls_t *ctls)
{
	return ctls->exit_ctls & (1U << VMX_VMEXIT_SAVE_IA32_PAT);
}
static inline void _vmx_setctl_vmexit_save_ia32_pat(vmx_ctls_t *ctls)
{
	ctls->exit_ctls |= (1U << VMX_VMEXIT_SAVE_IA32_PAT);
}
static inline void _vmx_clearctl_vmexit_save_ia32_pat(vmx_ctls_t *ctls)
{
	ctls->exit_ctls &= ~(1U << VMX_VMEXIT_SAVE_IA32_PAT);
}

/* Load IA32_PAT */
#define VMX_VMEXIT_LOAD_IA32_PAT 19
static inline bool _vmx_hasctl_vmexit_load_ia32_pat(vmx_ctls_t *ctls)
{
	return ctls->exit_ctls & (1U << VMX_VMEXIT_LOAD_IA32_PAT);
}
static inline void _vmx_setctl_vmexit_load_ia32_pat(vmx_ctls_t *ctls)
{
	ctls->exit_ctls |= (1U << VMX_VMEXIT_LOAD_IA32_PAT);
}
static inline void _vmx_clearctl_vmexit_load_ia32_pat(vmx_ctls_t *ctls)
{
	ctls->exit_ctls &= ~(1U << VMX_VMEXIT_LOAD_IA32_PAT);
}

/* Save IA32_EFER */
#define VMX_VMEXIT_SAVE_IA32_EFER 20
static inline bool _vmx_hasctl_vmexit_save_ia32_efer(vmx_ctls_t *ctls)
{
	return ctls->exit_ctls & (1U << VMX_VMEXIT_SAVE_IA32_EFER);
}
static inline void _vmx_setctl_vmexit_save_ia32_efer(vmx_ctls_t *ctls)
{
	ctls->exit_ctls |= (1U << VMX_VMEXIT_SAVE_IA32_EFER);
}
static inline void _vmx_clearctl_vmexit_save_ia32_efer(vmx_ctls_t *ctls)
{
	ctls->exit_ctls &= ~(1U << VMX_VMEXIT_SAVE_IA32_EFER);
}

/* Load IA32_EFER */
#define VMX_VMEXIT_LOAD_IA32_EFER 21
static inline bool _vmx_hasctl_vmexit_load_ia32_efer(vmx_ctls_t *ctls)
{
	return ctls->exit_ctls & (1U << VMX_VMEXIT_LOAD_IA32_EFER);
}
static inline void _vmx_setctl_vmexit_load_ia32_efer(vmx_ctls_t *ctls)
{
	ctls->exit_ctls |= (1U << VMX_VMEXIT_LOAD_IA32_EFER);
}
static inline void _vmx_clearctl_vmexit_load_ia32_efer(vmx_ctls_t *ctls)
{
	ctls->exit_ctls &= ~(1U << VMX_VMEXIT_LOAD_IA32_EFER);
}

/* Save VMX-preemption timer value */
#define VMX_VMEXIT_SAVE_VMX_PREEMPTION_TIMER_VALUE 22
static inline bool _vmx_hasctl_vmexit_save_vmx_preemption_timer_value(vmx_ctls_t *ctls)
{
	return ctls->exit_ctls & (1U << VMX_VMEXIT_SAVE_VMX_PREEMPTION_TIMER_VALUE);
}
static inline void _vmx_setctl_vmexit_save_vmx_preemption_timer_value(vmx_ctls_t *ctls)
{
	ctls->exit_ctls |= (1U << VMX_VMEXIT_SAVE_VMX_PREEMPTION_TIMER_VALUE);
}
static inline void _vmx_clearctl_vmexit_save_vmx_preemption_timer_value(vmx_ctls_t *ctls)
{
	ctls->exit_ctls &= ~(1U << VMX_VMEXIT_SAVE_VMX_PREEMPTION_TIMER_VALUE);
}

/* Clear IA32_BNDCFGS */
#define VMX_VMEXIT_CLEAR_IA32_BNDCFGS 23
static inline bool _vmx_hasctl_vmexit_clear_ia32_bndcfgs(vmx_ctls_t *ctls)
{
	return ctls->exit_ctls & (1U << VMX_VMEXIT_CLEAR_IA32_BNDCFGS);
}
static inline void _vmx_setctl_vmexit_clear_ia32_bndcfgs(vmx_ctls_t *ctls)
{
	ctls->exit_ctls |= (1U << VMX_VMEXIT_CLEAR_IA32_BNDCFGS);
}
static inline void _vmx_clearctl_vmexit_clear_ia32_bndcfgs(vmx_ctls_t *ctls)
{
	ctls->exit_ctls &= ~(1U << VMX_VMEXIT_CLEAR_IA32_BNDCFGS);
}

/* Conceal VMX from PT */
#define VMX_VMEXIT_CONCEAL_VMX_FROM_PT 24
static inline bool _vmx_hasctl_vmexit_conceal_vmx_from_pt(vmx_ctls_t *ctls)
{
	return ctls->exit_ctls & (1U << VMX_VMEXIT_CONCEAL_VMX_FROM_PT);
}
static inline void _vmx_setctl_vmexit_conceal_vmx_from_pt(vmx_ctls_t *ctls)
{
	ctls->exit_ctls |= (1U << VMX_VMEXIT_CONCEAL_VMX_FROM_PT);
}
static inline void _vmx_clearctl_vmexit_conceal_vmx_from_pt(vmx_ctls_t *ctls)
{
	ctls->exit_ctls &= ~(1U << VMX_VMEXIT_CONCEAL_VMX_FROM_PT);
}

/* Clear IA32_RTIT_CTL */
#define VMX_VMEXIT_CLEAR_IA32_RTIT_CTL 25
static inline bool _vmx_hasctl_vmexit_clear_ia32_rtit_ctl(vmx_ctls_t *ctls)
{
	return ctls->exit_ctls & (1U << VMX_VMEXIT_CLEAR_IA32_RTIT_CTL);
}
static inline void _vmx_setctl_vmexit_clear_ia32_rtit_ctl(vmx_ctls_t *ctls)
{
	ctls->exit_ctls |= (1U << VMX_VMEXIT_CLEAR_IA32_RTIT_CTL);
}
static inline void _vmx_clearctl_vmexit_clear_ia32_rtit_ctl(vmx_ctls_t *ctls)
{
	ctls->exit_ctls &= ~(1U << VMX_VMEXIT_CLEAR_IA32_RTIT_CTL);
}

/* Load CET state */
#define VMX_VMEXIT_LOAD_CET_STATE 28
static inline bool _vmx_hasctl_vmexit_load_cet_state(vmx_ctls_t *ctls)
{
	return ctls->exit_ctls & (1U << VMX_VMEXIT_LOAD_CET_STATE);
}
static inline void _vmx_setctl_vmexit_load_cet_state(vmx_ctls_t *ctls)
{
	ctls->exit_ctls |= (1U << VMX_VMEXIT_LOAD_CET_STATE);
}
static inline void _vmx_clearctl_vmexit_load_cet_state(vmx_ctls_t *ctls)
{
	ctls->exit_ctls &= ~(1U << VMX_VMEXIT_LOAD_CET_STATE);
}

/* Load PKRS */
#define VMX_VMEXIT_LOAD_PKRS 29
static inline bool _vmx_hasctl_vmexit_load_pkrs(vmx_ctls_t *ctls)
{
	return ctls->exit_ctls & (1U << VMX_VMEXIT_LOAD_PKRS);
}
static inline void _vmx_setctl_vmexit_load_pkrs(vmx_ctls_t *ctls)
{
	ctls->exit_ctls |= (1U << VMX_VMEXIT_LOAD_PKRS);
}
static inline void _vmx_clearctl_vmexit_load_pkrs(vmx_ctls_t *ctls)
{
	ctls->exit_ctls &= ~(1U << VMX_VMEXIT_LOAD_PKRS);
}

/* Load debug controls */
#define VMX_VMENTRY_LOAD_DEBUG_CONTROLS 2
static inline bool _vmx_hasctl_vmentry_load_debug_controls(vmx_ctls_t *ctls)
{
	return ctls->entry_ctls & (1U << VMX_VMENTRY_LOAD_DEBUG_CONTROLS);
}
static inline void _vmx_setctl_vmentry_load_debug_controls(vmx_ctls_t *ctls)
{
	ctls->entry_ctls |= (1U << VMX_VMENTRY_LOAD_DEBUG_CONTROLS);
}
static inline void _vmx_clearctl_vmentry_load_debug_controls(vmx_ctls_t *ctls)
{
	ctls->entry_ctls &= ~(1U << VMX_VMENTRY_LOAD_DEBUG_CONTROLS);
}

/* IA-32e mode guest */
#define VMX_VMENTRY_IA_32E_MODE_GUEST 9
static inline bool _vmx_hasctl_vmentry_ia_32e_mode_guest(vmx_ctls_t *ctls)
{
	return ctls->entry_ctls & (1U << VMX_VMENTRY_IA_32E_MODE_GUEST);
}
static inline void _vmx_setctl_vmentry_ia_32e_mode_guest(vmx_ctls_t *ctls)
{
	ctls->entry_ctls |= (1U << VMX_VMENTRY_IA_32E_MODE_GUEST);
}
static inline void _vmx_clearctl_vmentry_ia_32e_mode_guest(vmx_ctls_t *ctls)
{
	ctls->entry_ctls &= ~(1U << VMX_VMENTRY_IA_32E_MODE_GUEST);
}

/* Entry to SMM */
#define VMX_VMENTRY_ENTRY_TO_SMM 10
static inline bool _vmx_hasctl_vmentry_entry_to_smm(vmx_ctls_t *ctls)
{
	return ctls->entry_ctls & (1U << VMX_VMENTRY_ENTRY_TO_SMM);
}
static inline void _vmx_setctl_vmentry_entry_to_smm(vmx_ctls_t *ctls)
{
	ctls->entry_ctls |= (1U << VMX_VMENTRY_ENTRY_TO_SMM);
}
static inline void _vmx_clearctl_vmentry_entry_to_smm(vmx_ctls_t *ctls)
{
	ctls->entry_ctls &= ~(1U << VMX_VMENTRY_ENTRY_TO_SMM);
}

/* Deactivate dual-monitor treatment */
#define VMX_VMENTRY_DEACTIVATE_DUAL_MONITOR_TREATMENT 11
static inline bool _vmx_hasctl_vmentry_deactivate_dual_monitor_treatment(vmx_ctls_t *ctls)
{
	return ctls->entry_ctls & (1U << VMX_VMENTRY_DEACTIVATE_DUAL_MONITOR_TREATMENT);
}
static inline void _vmx_setctl_vmentry_deactivate_dual_monitor_treatment(vmx_ctls_t *ctls)
{
	ctls->entry_ctls |= (1U << VMX_VMENTRY_DEACTIVATE_DUAL_MONITOR_TREATMENT);
}
static inline void _vmx_clearctl_vmentry_deactivate_dual_monitor_treatment(vmx_ctls_t *ctls)
{
	ctls->entry_ctls &= ~(1U << VMX_VMENTRY_DEACTIVATE_DUAL_MONITOR_TREATMENT);
}

/* Load IA32_PERF_GLOBAL_CTRL */
#define VMX_VMENTRY_LOAD_IA32_PERF_GLOBAL_CTRL 13
static inline bool _vmx_hasctl_vmentry_load_ia32_perf_global_ctrl(vmx_ctls_t *ctls)
{
	return ctls->entry_ctls & (1U << VMX_VMENTRY_LOAD_IA32_PERF_GLOBAL_CTRL);
}
static inline void _vmx_setctl_vmentry_load_ia32_perf_global_ctrl(vmx_ctls_t *ctls)
{
	ctls->entry_ctls |= (1U << VMX_VMENTRY_LOAD_IA32_PERF_GLOBAL_CTRL);
}
static inline void _vmx_clearctl_vmentry_load_ia32_perf_global_ctrl(vmx_ctls_t *ctls)
{
	ctls->entry_ctls &= ~(1U << VMX_VMENTRY_LOAD_IA32_PERF_GLOBAL_CTRL);
}

/* Load IA32_PAT */
#define VMX_VMENTRY_LOAD_IA32_PAT 14
static inline bool _vmx_hasctl_vmentry_load_ia32_pat(vmx_ctls_t *ctls)
{
	return ctls->entry_ctls & (1U << VMX_VMENTRY_LOAD_IA32_PAT);
}
static inline void _vmx_setctl_vmentry_load_ia32_pat(vmx_ctls_t *ctls)
{
	ctls->entry_ctls |= (1U << VMX_VMENTRY_LOAD_IA32_PAT);
}
static inline void _vmx_clearctl_vmentry_load_ia32_pat(vmx_ctls_t *ctls)
{
	ctls->entry_ctls &= ~(1U << VMX_VMENTRY_LOAD_IA32_PAT);
}

/* Load IA32_EFER */
#define VMX_VMENTRY_LOAD_IA32_EFER 15
static inline bool _vmx_hasctl_vmentry_load_ia32_efer(vmx_ctls_t *ctls)
{
	return ctls->entry_ctls & (1U << VMX_VMENTRY_LOAD_IA32_EFER);
}
static inline void _vmx_setctl_vmentry_load_ia32_efer(vmx_ctls_t *ctls)
{
	ctls->entry_ctls |= (1U << VMX_VMENTRY_LOAD_IA32_EFER);
}
static inline void _vmx_clearctl_vmentry_load_ia32_efer(vmx_ctls_t *ctls)
{
	ctls->entry_ctls &= ~(1U << VMX_VMENTRY_LOAD_IA32_EFER);
}

/* Load IA32_BNDCFGS */
#define VMX_VMENTRY_LOAD_IA32_BNDCFGS 16
static inline bool _vmx_hasctl_vmentry_load_ia32_bndcfgs(vmx_ctls_t *ctls)
{
	return ctls->entry_ctls & (1U << VMX_VMENTRY_LOAD_IA32_BNDCFGS);
}
static inline void _vmx_setctl_vmentry_load_ia32_bndcfgs(vmx_ctls_t *ctls)
{
	ctls->entry_ctls |= (1U << VMX_VMENTRY_LOAD_IA32_BNDCFGS);
}
static inline void _vmx_clearctl_vmentry_load_ia32_bndcfgs(vmx_ctls_t *ctls)
{
	ctls->entry_ctls &= ~(1U << VMX_VMENTRY_LOAD_IA32_BNDCFGS);
}

/* Conceal VMX from PT */
#define VMX_VMENTRY_CONCEAL_VMX_FROM_PT 17
static inline bool _vmx_hasctl_vmentry_conceal_vmx_from_pt(vmx_ctls_t *ctls)
{
	return ctls->entry_ctls & (1U << VMX_VMENTRY_CONCEAL_VMX_FROM_PT);
}
static inline void _vmx_setctl_vmentry_conceal_vmx_from_pt(vmx_ctls_t *ctls)
{
	ctls->entry_ctls |= (1U << VMX_VMENTRY_CONCEAL_VMX_FROM_PT);
}
static inline void _vmx_clearctl_vmentry_conceal_vmx_from_pt(vmx_ctls_t *ctls)
{
	ctls->entry_ctls &= ~(1U << VMX_VMENTRY_CONCEAL_VMX_FROM_PT);
}

/* Load IA32_RTIT_CTL */
#define VMX_VMENTRY_LOAD_IA32_RTIT_CTL 18
static inline bool _vmx_hasctl_vmentry_load_ia32_rtit_ctl(vmx_ctls_t *ctls)
{
	return ctls->entry_ctls & (1U << VMX_VMENTRY_LOAD_IA32_RTIT_CTL);
}
static inline void _vmx_setctl_vmentry_load_ia32_rtit_ctl(vmx_ctls_t *ctls)
{
	ctls->entry_ctls |= (1U << VMX_VMENTRY_LOAD_IA32_RTIT_CTL);
}
static inline void _vmx_clearctl_vmentry_load_ia32_rtit_ctl(vmx_ctls_t *ctls)
{
	ctls->entry_ctls &= ~(1U << VMX_VMENTRY_LOAD_IA32_RTIT_CTL);
}

/* Load CET state */
#define VMX_VMENTRY_LOAD_CET_STATE 20
static inline bool _vmx_hasctl_vmentry_load_cet_state(vmx_ctls_t *ctls)
{
	return ctls->entry_ctls & (1U << VMX_VMENTRY_LOAD_CET_STATE);
}
static inline void _vmx_setctl_vmentry_load_cet_state(vmx_ctls_t *ctls)
{
	ctls->entry_ctls |= (1U << VMX_VMENTRY_LOAD_CET_STATE);
}
static inline void _vmx_clearctl_vmentry_load_cet_state(vmx_ctls_t *ctls)
{
	ctls->entry_ctls &= ~(1U << VMX_VMENTRY_LOAD_CET_STATE);
}

/* Load PKRS */
#define VMX_VMENTRY_LOAD_PKRS 22
static inline bool _vmx_hasctl_vmentry_load_pkrs(vmx_ctls_t *ctls)
{
	return ctls->entry_ctls & (1U << VMX_VMENTRY_LOAD_PKRS);
}
static inline void _vmx_setctl_vmentry_load_pkrs(vmx_ctls_t *ctls)
{
	ctls->entry_ctls |= (1U << VMX_VMENTRY_LOAD_PKRS);
}
static inline void _vmx_clearctl_vmentry_load_pkrs(vmx_ctls_t *ctls)
{
	ctls->entry_ctls &= ~(1U << VMX_VMENTRY_LOAD_PKRS);
}

/* End program-generated content */

#endif /* !__ASSEMBLY__ */

#endif /* _VMX_CTLS_H_ */

