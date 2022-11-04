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

// _vmx_vmcs_fields.h
// Enumerate through all VMCS fields
// author: Eric Li (xiaoyili@andrew.cmu.edu)

/*
 * Macros are defined as DECLARE_FIELD_<size>_<writability>
 * size is 16, 64, 32, or NW (natural width).
 * writability is RO (read only) or RW (read write).
 * The arguments are:
 * * encoding: field encoding used in VMRAED and VMWRITE instructions
 * * name: name of the field in struct _vmx_vmcsfields
 * * exist: an expression showing whether the field exists, when the macro
 *          FIELD_CTLS_ARG is set to the controls
 * * ...: reserved for future use
 */

#ifndef DECLARE_FIELD_16
#define DECLARE_FIELD_16(...)
#endif

#ifndef DECLARE_FIELD_64
#define DECLARE_FIELD_64(...)
#endif

#ifndef DECLARE_FIELD_32
#define DECLARE_FIELD_32(...)
#endif

#ifndef DECLARE_FIELD_NW
#define DECLARE_FIELD_NW(...)
#endif

#ifndef DECLARE_FIELD_16_RO
#define DECLARE_FIELD_16_RO(...) DECLARE_FIELD_16(__VA_ARGS__)
#endif

#ifndef DECLARE_FIELD_64_RO
#define DECLARE_FIELD_64_RO(...) DECLARE_FIELD_64(__VA_ARGS__)
#endif

#ifndef DECLARE_FIELD_32_RO
#define DECLARE_FIELD_32_RO(...) DECLARE_FIELD_32(__VA_ARGS__)
#endif

#ifndef DECLARE_FIELD_NW_RO
#define DECLARE_FIELD_NW_RO(...) DECLARE_FIELD_NW(__VA_ARGS__)
#endif
#ifndef DECLARE_FIELD_16_RW
#define DECLARE_FIELD_16_RW(...) DECLARE_FIELD_16(__VA_ARGS__)
#endif

#ifndef DECLARE_FIELD_64_RW
#define DECLARE_FIELD_64_RW(...) DECLARE_FIELD_64(__VA_ARGS__)
#endif

#ifndef DECLARE_FIELD_32_RW
#define DECLARE_FIELD_32_RW(...) DECLARE_FIELD_32(__VA_ARGS__)
#endif

#ifndef DECLARE_FIELD_NW_RW
#define DECLARE_FIELD_NW_RW(...) DECLARE_FIELD_NW(__VA_ARGS__)
#endif

#ifndef FIELD_CTLS_ARG
#define FIELD_CTLS_ARG
#endif

#ifdef __DEBUG_QEMU__
#define VMCS12_FIELDS_QEMU 1
#else /* !__DEBUG_QEMU__ */
#define VMCS12_FIELDS_QEMU 0
#endif /* __DEBUG_QEMU__ */

/*
 * 16-Bit Control Fields
 */

/* Virtual-processor identifier (VPID) */
DECLARE_FIELD_16_RW(0x0000, control_vpid,
					(_vmx_hasctl_enable_vpid(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Posted-interrupt notification vector */
DECLARE_FIELD_16_RW(0x0002, control_post_interrupt_notification_vec,
					(_vmx_hasctl_process_posted_interrupts(FIELD_CTLS_ARG)),
					UNDEFINED)
/* EPTP index */
DECLARE_FIELD_16_RW(0x0004, control_eptp_index,
					(_vmx_hasctl_ept_violation_ve(FIELD_CTLS_ARG)),
					UNDEFINED)

/*
 * 16-Bit Guest-State Fields
 */

/* Guest ES selector */
DECLARE_FIELD_16_RW(0x0800, guest_ES_selector,
					(1),
					UNDEFINED)
/* Guest CS selector */
DECLARE_FIELD_16_RW(0x0802, guest_CS_selector,
					(1),
					UNDEFINED)
/* Guest SS selector */
DECLARE_FIELD_16_RW(0x0804, guest_SS_selector,
					(1),
					UNDEFINED)
/* Guest DS selector */
DECLARE_FIELD_16_RW(0x0806, guest_DS_selector,
					(1),
					UNDEFINED)
/* Guest FS selector */
DECLARE_FIELD_16_RW(0x0808, guest_FS_selector,
					(1),
					UNDEFINED)
/* Guest GS selector */
DECLARE_FIELD_16_RW(0x080A, guest_GS_selector,
					(1),
					UNDEFINED)
/* Guest LDTR selector */
DECLARE_FIELD_16_RW(0x080C, guest_LDTR_selector,
					(1),
					UNDEFINED)
/* Guest TR selector */
DECLARE_FIELD_16_RW(0x080E, guest_TR_selector,
					(1),
					UNDEFINED)
/* Guest interrupt status */
DECLARE_FIELD_16_RW(0x0810, guest_interrupt_status,
					(_vmx_hasctl_virtual_interrupt_delivery(FIELD_CTLS_ARG)),
					UNDEFINED)
/* PML index */
DECLARE_FIELD_16_RW(0x0812, guest_PML_index,
					(_vmx_hasctl_enable_pml(FIELD_CTLS_ARG)),
					UNDEFINED)

/*
 * 16-Bit Host-State Fields
 */

/* Host ES selector */
DECLARE_FIELD_16_RW(0x0C00, host_ES_selector,
					(1),
					UNDEFINED)
/* Host CS selector */
DECLARE_FIELD_16_RW(0x0C02, host_CS_selector,
					(1),
					UNDEFINED)
/* Host SS selector */
DECLARE_FIELD_16_RW(0x0C04, host_SS_selector,
					(1),
					UNDEFINED)
/* Host DS selector */
DECLARE_FIELD_16_RW(0x0C06, host_DS_selector,
					(1),
					UNDEFINED)
/* Host FS selector */
DECLARE_FIELD_16_RW(0x0C08, host_FS_selector,
					(1),
					UNDEFINED)
/* Host GS selector */
DECLARE_FIELD_16_RW(0x0C0A, host_GS_selector,
					(1),
					UNDEFINED)
/* Host TR selector */
DECLARE_FIELD_16_RW(0x0C0C, host_TR_selector,
					(1),
					UNDEFINED)

/*
 * 64-Bit Control Fields
 */

/* Address of I/O bitmap A */
DECLARE_FIELD_64_RW(0x2000, control_IO_BitmapA_address,
					(_vmx_hasctl_use_io_bitmaps(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Address of I/O bitmap B */
DECLARE_FIELD_64_RW(0x2002, control_IO_BitmapB_address,
					(_vmx_hasctl_use_io_bitmaps(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Address of MSR bitmaps */
DECLARE_FIELD_64_RW(0x2004, control_MSR_Bitmaps_address,
					(_vmx_hasctl_use_msr_bitmaps(FIELD_CTLS_ARG)),
					UNDEFINED)
/* VM-exit MSR-store address */
DECLARE_FIELD_64_RW(0x2006, control_VM_exit_MSR_store_address,
					(1),
					UNDEFINED)
/* VM-exit MSR-load address */
DECLARE_FIELD_64_RW(0x2008, control_VM_exit_MSR_load_address,
					(1),
					UNDEFINED)
/* VM-entry MSR-load address */
DECLARE_FIELD_64_RW(0x200A, control_VM_entry_MSR_load_address,
					(1),
					UNDEFINED)
/* Executive-VMCS pointer */
DECLARE_FIELD_64_RW(0x200C, control_Executive_VMCS_pointer,
					(!VMCS12_FIELDS_QEMU),
					UNDEFINED)
/* PML address */
DECLARE_FIELD_64_RW(0x200E, control_PML_address,
					(_vmx_hasctl_enable_pml(FIELD_CTLS_ARG)),
					UNDEFINED)
/* TSC offset */
DECLARE_FIELD_64_RW(0x2010, control_TSC_offset,
					(1),
					UNDEFINED)
/* Virtual-APIC address */
DECLARE_FIELD_64_RW(0x2012, control_virtual_APIC_address,
					(_vmx_hasctl_use_tpr_shadow(FIELD_CTLS_ARG)),
					UNDEFINED)
/* APIC-access address */
DECLARE_FIELD_64_RW(0x2014, control_APIC_access_address,
					(_vmx_hasctl_virtualize_apic_access(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Posted-interrupt descriptor address */
DECLARE_FIELD_64_RW(0x2016, control_posted_interrupt_desc_address,
					(_vmx_hasctl_process_posted_interrupts(FIELD_CTLS_ARG)),
					UNDEFINED)
/* VM-function controls */
DECLARE_FIELD_64_RW(0x2018, control_VM_function_controls,
					(_vmx_hasctl_enable_vm_functions(FIELD_CTLS_ARG)),
					UNDEFINED)
/* EPT pointer (EPTP) */
DECLARE_FIELD_64_RW(0x201A, control_EPT_pointer,
					(_vmx_hasctl_enable_ept(FIELD_CTLS_ARG)),
					UNDEFINED)
/* EOI-exit bitmap 0 (EOI_EXIT0) */
DECLARE_FIELD_64_RW(0x201C, control_EOI_exit_bitmap_0,
					(_vmx_hasctl_virtual_interrupt_delivery(FIELD_CTLS_ARG)),
					UNDEFINED)
/* EOI-exit bitmap 1 (EOI_EXIT1) */
DECLARE_FIELD_64_RW(0x201E, control_EOI_exit_bitmap_1,
					(_vmx_hasctl_virtual_interrupt_delivery(FIELD_CTLS_ARG)),
					UNDEFINED)
/* EOI-exit bitmap 2 (EOI_EXIT2) */
DECLARE_FIELD_64_RW(0x2020, control_EOI_exit_bitmap_2,
					(_vmx_hasctl_virtual_interrupt_delivery(FIELD_CTLS_ARG)),
					UNDEFINED)
/* EOI-exit bitmap 3 (EOI_EXIT3) */
DECLARE_FIELD_64_RW(0x2022, control_EOI_exit_bitmap_3,
					(_vmx_hasctl_virtual_interrupt_delivery(FIELD_CTLS_ARG)),
					UNDEFINED)
/* EPTP-list address */
DECLARE_FIELD_64_RW(0x2024, control_EPTP_list_address,
					(0 /* TODO: Not able to detect "EPTP switching" */),
					UNDEFINED)
/* VMREAD-bitmap address */
DECLARE_FIELD_64_RW(0x2026, control_VMREAD_bitmap_address,
					(_vmx_hasctl_vmcs_shadowing(FIELD_CTLS_ARG)),
					UNDEFINED)
/* VMWRITE-bitmap address */
DECLARE_FIELD_64_RW(0x2028, control_VMWRITE_bitmap_address,
					(_vmx_hasctl_vmcs_shadowing(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Virtualization-exception information address */
DECLARE_FIELD_64_RW(0x202A, control_virt_exception_info_address,
					(_vmx_hasctl_ept_violation_ve(FIELD_CTLS_ARG)),
					UNDEFINED)
/* XSS-exiting bitmap */
DECLARE_FIELD_64_RW(0x202C, control_XSS_exiting_bitmap,
					(_vmx_hasctl_enable_xsaves_xrstors(FIELD_CTLS_ARG)),
					UNDEFINED)
/* ENCLS-exiting bitmap */
DECLARE_FIELD_64_RW(0x202E, control_ENCLS_exiting_bitmap,
					(_vmx_hasctl_enable_encls_exiting(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Sub-page-permission-table pointer */
DECLARE_FIELD_64_RW(0x2030, control_subpage_permission_table_pointer,
					(_vmx_hasctl_sub_page_write_permissions_for_ept(FIELD_CTLS_ARG)),
					UNDEFINED)
/* TSC multiplier */
DECLARE_FIELD_64_RW(0x2032, control_TSC_multiplier,
					(_vmx_hasctl_use_tsc_scaling(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Tertiary processor-based VM-execution controls */
DECLARE_FIELD_64_RW(0x2034, control_tertiary_proc_based_VMexec_ctls,
					(_vmx_hasctl_activate_tertiary_controls(FIELD_CTLS_ARG)),
					UNDEFINED)
/* ENCLV-exiting bitmap */
DECLARE_FIELD_64_RW(0x2036, control_ENCLV_exiting_bitmap,
					(_vmx_hasctl_enable_enclv_exiting(FIELD_CTLS_ARG)),
					UNDEFINED)

/*
 * 64-Bit Read-Only Data Field
 */

/* Guest-physical address */
DECLARE_FIELD_64_RO(0x2400, guest_paddr,
					(_vmx_hasctl_enable_ept(FIELD_CTLS_ARG)),
					UNDEFINED)

/*
 * 64-Bit Guest-State Fields
 */

/* VMCS link pointer */
DECLARE_FIELD_64_RW(0x2800, guest_VMCS_link_pointer,
					(1),
					UNDEFINED)
/* Guest IA32_DEBUGCTL */
DECLARE_FIELD_64_RW(0x2802, guest_IA32_DEBUGCTL,
					(1),
					UNDEFINED)
/* Guest IA32_PAT */
DECLARE_FIELD_64_RW(0x2804, guest_IA32_PAT,
					(_vmx_hasctl_vmexit_save_ia32_pat(FIELD_CTLS_ARG) || _vmx_hasctl_vmentry_load_ia32_pat(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Guest IA32_EFER */
DECLARE_FIELD_64_RW(0x2806, guest_IA32_EFER,
					(_vmx_hasctl_vmexit_save_ia32_efer(FIELD_CTLS_ARG) || _vmx_hasctl_vmentry_load_ia32_efer(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Guest IA32_PERF_GLOBAL_CTRL */
DECLARE_FIELD_64_RW(0x2808, guest_IA32_PERF_GLOBAL_CTRL,
					(_vmx_hasctl_vmentry_load_ia32_perf_global_ctrl(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Guest PDPTE0 */
DECLARE_FIELD_64_RW(0x280A, guest_PDPTE0,
					(_vmx_hasctl_enable_ept(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Guest PDPTE1 */
DECLARE_FIELD_64_RW(0x280C, guest_PDPTE1,
					(_vmx_hasctl_enable_ept(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Guest PDPTE2 */
DECLARE_FIELD_64_RW(0x280E, guest_PDPTE2,
					(_vmx_hasctl_enable_ept(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Guest PDPTE3 */
DECLARE_FIELD_64_RW(0x2810, guest_PDPTE3,
					(_vmx_hasctl_enable_ept(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Guest IA32_BNDCFGS */
DECLARE_FIELD_64_RW(0x2812, guest_IA32_BNDCFGS,
					(_vmx_hasctl_vmexit_clear_ia32_bndcfgs(FIELD_CTLS_ARG) || _vmx_hasctl_vmentry_load_ia32_bndcfgs(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Guest IA32_RTIT_CTL */
DECLARE_FIELD_64_RW(0x2814, guest_IA32_RTIT_CTL,
					(_vmx_hasctl_vmexit_clear_ia32_rtit_ctl(FIELD_CTLS_ARG) || _vmx_hasctl_vmentry_load_ia32_rtit_ctl(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Guest IA32_PKRS */
DECLARE_FIELD_64_RW(0x2818, guest_IA32_PKRS,
					(_vmx_hasctl_vmentry_load_pkrs(FIELD_CTLS_ARG)),
					UNDEFINED)

/*
 * 64-Bit Host-State Fields
 */

/* Host IA32_PAT */
DECLARE_FIELD_64_RW(0x2C00, host_IA32_PAT,
					(_vmx_hasctl_vmexit_load_ia32_pat(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Host IA32_EFER */
DECLARE_FIELD_64_RW(0x2C02, host_IA32_EFER,
					(_vmx_hasctl_vmexit_load_ia32_efer(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Host IA32_PERF_GLOBAL_CTRL */
DECLARE_FIELD_64_RW(0x2C04, host_IA32_PERF_GLOBAL_CTRL,
					(_vmx_hasctl_vmexit_load_ia32_perf_global_ctrl(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Host IA32_PKRS */
DECLARE_FIELD_64_RW(0x2C06, host_IA32_PKRS,
					(_vmx_hasctl_vmexit_load_pkrs(FIELD_CTLS_ARG)),
					UNDEFINED)

/*
 * 32-Bit Control Fields
 */

/* Pin-based VM-execution controls */
DECLARE_FIELD_32_RW(0x4000, control_VMX_pin_based,
					(1),
					UNDEFINED)
/* Primary processor-based VM-execution controls */
DECLARE_FIELD_32_RW(0x4002, control_VMX_cpu_based,
					(1),
					UNDEFINED)
/* Exception bitmap */
DECLARE_FIELD_32_RW(0x4004, control_exception_bitmap,
					(1),
					UNDEFINED)
/* Page-fault error-code mask */
DECLARE_FIELD_32_RW(0x4006, control_pagefault_errorcode_mask,
					(1),
					UNDEFINED)
/* Page-fault error-code match */
DECLARE_FIELD_32_RW(0x4008, control_pagefault_errorcode_match,
					(1),
					UNDEFINED)
/* CR3-target count */
DECLARE_FIELD_32_RW(0x400A, control_CR3_target_count,
					(1),
					UNDEFINED)
/* VM-exit controls */
DECLARE_FIELD_32_RW(0x400C, control_VM_exit_controls,
					(1),
					UNDEFINED)
/* VM-exit MSR-store count */
DECLARE_FIELD_32_RW(0x400E, control_VM_exit_MSR_store_count,
					(1),
					UNDEFINED)
/* VM-exit MSR-load count */
DECLARE_FIELD_32_RW(0x4010, control_VM_exit_MSR_load_count,
					(1),
					UNDEFINED)
/* VM-entry controls */
DECLARE_FIELD_32_RW(0x4012, control_VM_entry_controls,
					(1),
					UNDEFINED)
/* VM-entry MSR-load count */
DECLARE_FIELD_32_RW(0x4014, control_VM_entry_MSR_load_count,
					(1),
					UNDEFINED)
/* VM-entry interruption-information field */
DECLARE_FIELD_32_RW(0x4016, control_VM_entry_interruption_information,
					(1),
					UNDEFINED)
/* VM-entry exception error code */
DECLARE_FIELD_32_RW(0x4018, control_VM_entry_exception_errorcode,
					(1),
					UNDEFINED)
/* VM-entry instruction length */
DECLARE_FIELD_32_RW(0x401A, control_VM_entry_instruction_length,
					(1),
					UNDEFINED)
/* TPR threshold */
DECLARE_FIELD_32_RW(0x401C, control_Task_PRivilege_Threshold,
					(_vmx_hasctl_use_tpr_shadow(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Secondary processor-based VM-execution controls */
DECLARE_FIELD_32_RW(0x401E, control_VMX_seccpu_based,
					(_vmx_hasctl_activate_secondary_controls(FIELD_CTLS_ARG)),
					UNDEFINED)
/* PLE_Gap */
DECLARE_FIELD_32_RW(0x4020, control_PLE_gap,
					(_vmx_hasctl_pause_loop_exiting(FIELD_CTLS_ARG)),
					UNDEFINED)
/* PLE_Window */
DECLARE_FIELD_32_RW(0x4022, control_PLE_window,
					(_vmx_hasctl_pause_loop_exiting(FIELD_CTLS_ARG)),
					UNDEFINED)

/*
 * 32-Bit Read-Only Data Fields
 */

/* VM-instruction error */
DECLARE_FIELD_32_RO(0x4400, info_vminstr_error,
					(1),
					UNDEFINED)
/* Exit reason */
DECLARE_FIELD_32_RO(0x4402, info_vmexit_reason,
					(1),
					UNDEFINED)
/* VM-exit interruption information */
DECLARE_FIELD_32_RO(0x4404, info_vmexit_interrupt_information,
					(1),
					UNDEFINED)
/* VM-exit interruption error code */
DECLARE_FIELD_32_RO(0x4406, info_vmexit_interrupt_error_code,
					(1),
					UNDEFINED)
/* IDT-vectoring information field */
DECLARE_FIELD_32_RO(0x4408, info_IDT_vectoring_information,
					(1),
					UNDEFINED)
/* IDT-vectoring error code */
DECLARE_FIELD_32_RO(0x440A, info_IDT_vectoring_error_code,
					(1),
					UNDEFINED)
/* VM-exit instruction length */
DECLARE_FIELD_32_RO(0x440C, info_vmexit_instruction_length,
					(1),
					UNDEFINED)
/* VM-exit instruction information */
DECLARE_FIELD_32_RO(0x440E, info_vmx_instruction_information,
					(1),
					UNDEFINED)

/*
 * 32-Bit Guest-State Fields
 */

/* Guest ES limit */
DECLARE_FIELD_32_RW(0x4800, guest_ES_limit,
					(1),
					UNDEFINED)
/* Guest CS limit */
DECLARE_FIELD_32_RW(0x4802, guest_CS_limit,
					(1),
					UNDEFINED)
/* Guest SS limit */
DECLARE_FIELD_32_RW(0x4804, guest_SS_limit,
					(1),
					UNDEFINED)
/* Guest DS limit */
DECLARE_FIELD_32_RW(0x4806, guest_DS_limit,
					(1),
					UNDEFINED)
/* Guest FS limit */
DECLARE_FIELD_32_RW(0x4808, guest_FS_limit,
					(1),
					UNDEFINED)
/* Guest GS limit */
DECLARE_FIELD_32_RW(0x480A, guest_GS_limit,
					(1),
					UNDEFINED)
/* Guest LDTR limit */
DECLARE_FIELD_32_RW(0x480C, guest_LDTR_limit,
					(1),
					UNDEFINED)
/* Guest TR limit */
DECLARE_FIELD_32_RW(0x480E, guest_TR_limit,
					(1),
					UNDEFINED)
/* Guest GDTR limit */
DECLARE_FIELD_32_RW(0x4810, guest_GDTR_limit,
					(1),
					UNDEFINED)
/* Guest IDTR limit */
DECLARE_FIELD_32_RW(0x4812, guest_IDTR_limit,
					(1),
					UNDEFINED)
/* Guest ES access rights */
DECLARE_FIELD_32_RW(0x4814, guest_ES_access_rights,
					(1),
					UNDEFINED)
/* Guest CS access rights */
DECLARE_FIELD_32_RW(0x4816, guest_CS_access_rights,
					(1),
					UNDEFINED)
/* Guest SS access rights */
DECLARE_FIELD_32_RW(0x4818, guest_SS_access_rights,
					(1),
					UNDEFINED)
/* Guest DS access rights */
DECLARE_FIELD_32_RW(0x481A, guest_DS_access_rights,
					(1),
					UNDEFINED)
/* Guest FS access rights */
DECLARE_FIELD_32_RW(0x481C, guest_FS_access_rights,
					(1),
					UNDEFINED)
/* Guest GS access rights */
DECLARE_FIELD_32_RW(0x481E, guest_GS_access_rights,
					(1),
					UNDEFINED)
/* Guest LDTR access rights */
DECLARE_FIELD_32_RW(0x4820, guest_LDTR_access_rights,
					(1),
					UNDEFINED)
/* Guest TR access rights */
DECLARE_FIELD_32_RW(0x4822, guest_TR_access_rights,
					(1),
					UNDEFINED)
/* Guest interruptibility state */
DECLARE_FIELD_32_RW(0x4824, guest_interruptibility,
					(1),
					UNDEFINED)
/* Guest activity state */
DECLARE_FIELD_32_RW(0x4826, guest_activity_state,
					(1),
					UNDEFINED)
/* Guest SMBASE */
DECLARE_FIELD_32_RW(0x4828, guest_SMBASE,
					(!VMCS12_FIELDS_QEMU),
					UNDEFINED)
/* Guest IA32_SYSENTER_CS */
DECLARE_FIELD_32_RW(0x482A, guest_SYSENTER_CS,
					(1),
					UNDEFINED)
/* VMX-preemption timer value */
DECLARE_FIELD_32_RW(0x482E, guest_VMX_preemption_timer_value,
					(_vmx_hasctl_activate_vmx_preemption_timer(FIELD_CTLS_ARG)),
					UNDEFINED)

/*
 * 32-Bit Host-State Field
 */

/* Host IA32_SYSENTER_CS */
DECLARE_FIELD_32_RW(0x4C00, host_SYSENTER_CS,
					(1),
					UNDEFINED)

/*
 * Natural-Width Control Fields
 */

/* CR0 guest/host mask */
DECLARE_FIELD_NW_RW(0x6000, control_CR0_mask,
					(1),
					UNDEFINED)
/* CR4 guest/host mask */
DECLARE_FIELD_NW_RW(0x6002, control_CR4_mask,
					(1),
					UNDEFINED)
/* CR0 read shadow */
DECLARE_FIELD_NW_RW(0x6004, control_CR0_shadow,
					(1),
					UNDEFINED)
/* CR4 read shadow */
DECLARE_FIELD_NW_RW(0x6006, control_CR4_shadow,
					(1),
					UNDEFINED)
/* CR3-target value 0 */
DECLARE_FIELD_NW_RW(0x6008, control_CR3_target0,
					(!VMCS12_FIELDS_QEMU),
					UNDEFINED)
/* CR3-target value 1 */
DECLARE_FIELD_NW_RW(0x600A, control_CR3_target1,
					(!VMCS12_FIELDS_QEMU),
					UNDEFINED)
/* CR3-target value 2 */
DECLARE_FIELD_NW_RW(0x600C, control_CR3_target2,
					(!VMCS12_FIELDS_QEMU),
					UNDEFINED)
/* CR3-target value 3 */
DECLARE_FIELD_NW_RW(0x600E, control_CR3_target3,
					(!VMCS12_FIELDS_QEMU),
					UNDEFINED)

/*
 * Natural-Width Read-Only Data Fields
 */

/* Exit qualification */
DECLARE_FIELD_NW_RO(0x6400, info_exit_qualification,
					(1),
					UNDEFINED)
/* I/O RCX */
DECLARE_FIELD_NW_RO(0x6402, info_IO_RCX,
					(!VMCS12_FIELDS_QEMU),
					UNDEFINED)
/* I/O RSI */
DECLARE_FIELD_NW_RO(0x6404, info_IO_RSI,
					(!VMCS12_FIELDS_QEMU),
					UNDEFINED)
/* I/O RDI */
DECLARE_FIELD_NW_RO(0x6406, info_IO_RDI,
					(!VMCS12_FIELDS_QEMU),
					UNDEFINED)
/* I/O RIP */
DECLARE_FIELD_NW_RO(0x6408, info_IO_RIP,
					(!VMCS12_FIELDS_QEMU),
					UNDEFINED)
/* Guest-linear address */
DECLARE_FIELD_NW_RO(0x640A, info_guest_linear_address,
					(1),
					UNDEFINED)

/*
 * Natural-Width Guest-State Fields
 */

/* Guest CR0 */
DECLARE_FIELD_NW_RW(0x6800, guest_CR0,
					(1),
					UNDEFINED)
/* Guest CR3 */
DECLARE_FIELD_NW_RW(0x6802, guest_CR3,
					(1),
					UNDEFINED)
/* Guest CR4 */
DECLARE_FIELD_NW_RW(0x6804, guest_CR4,
					(1),
					UNDEFINED)
/* Guest ES base */
DECLARE_FIELD_NW_RW(0x6806, guest_ES_base,
					(1),
					UNDEFINED)
/* Guest CS base */
DECLARE_FIELD_NW_RW(0x6808, guest_CS_base,
					(1),
					UNDEFINED)
/* Guest SS base */
DECLARE_FIELD_NW_RW(0x680A, guest_SS_base,
					(1),
					UNDEFINED)
/* Guest DS base */
DECLARE_FIELD_NW_RW(0x680C, guest_DS_base,
					(1),
					UNDEFINED)
/* Guest FS base */
DECLARE_FIELD_NW_RW(0x680E, guest_FS_base,
					(1),
					UNDEFINED)
/* Guest GS base */
DECLARE_FIELD_NW_RW(0x6810, guest_GS_base,
					(1),
					UNDEFINED)
/* Guest LDTR base */
DECLARE_FIELD_NW_RW(0x6812, guest_LDTR_base,
					(1),
					UNDEFINED)
/* Guest TR base */
DECLARE_FIELD_NW_RW(0x6814, guest_TR_base,
					(1),
					UNDEFINED)
/* Guest GDTR base */
DECLARE_FIELD_NW_RW(0x6816, guest_GDTR_base,
					(1),
					UNDEFINED)
/* Guest IDTR base */
DECLARE_FIELD_NW_RW(0x6818, guest_IDTR_base,
					(1),
					UNDEFINED)
/* Guest DR7 */
DECLARE_FIELD_NW_RW(0x681A, guest_DR7,
					(1),
					UNDEFINED)
/* Guest RSP */
DECLARE_FIELD_NW_RW(0x681C, guest_RSP,
					(1),
					UNDEFINED)
/* Guest RIP */
DECLARE_FIELD_NW_RW(0x681E, guest_RIP,
					(1),
					UNDEFINED)
/* Guest RFLAGS */
DECLARE_FIELD_NW_RW(0x6820, guest_RFLAGS,
					(1),
					UNDEFINED)
/* Guest pending debug exceptions */
DECLARE_FIELD_NW_RW(0x6822, guest_pending_debug_x,
					(1),
					UNDEFINED)
/* Guest IA32_SYSENTER_ESP */
DECLARE_FIELD_NW_RW(0x6824, guest_SYSENTER_ESP,
					(1),
					UNDEFINED)
/* Guest IA32_SYSENTER_EIP */
DECLARE_FIELD_NW_RW(0x6826, guest_SYSENTER_EIP,
					(1),
					UNDEFINED)
/* Guest IA32_S_CET */
DECLARE_FIELD_NW_RW(0x6828, guest_IA32_S_CET,
					(_vmx_hasctl_vmentry_load_cet_state(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Guest SSP */
DECLARE_FIELD_NW_RW(0x682A, guest_SSP,
					(_vmx_hasctl_vmentry_load_cet_state(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Guest IA32_INTERRUPT_SSP_TABLE_ADDR */
DECLARE_FIELD_NW_RW(0x682C, guest_IA32_INTERRUPT_SSP_TABLE_ADDR,
					(_vmx_hasctl_vmentry_load_cet_state(FIELD_CTLS_ARG)),
					UNDEFINED)

/*
 * Natural-Width Host-State Fields
 */

/* Host CR0 */
DECLARE_FIELD_NW_RW(0x6C00, host_CR0,
					(1),
					UNDEFINED)
/* Host CR3 */
DECLARE_FIELD_NW_RW(0x6C02, host_CR3,
					(1),
					UNDEFINED)
/* Host CR4 */
DECLARE_FIELD_NW_RW(0x6C04, host_CR4,
					(1),
					UNDEFINED)
/* Host FS base */
DECLARE_FIELD_NW_RW(0x6C06, host_FS_base,
					(1),
					UNDEFINED)
/* Host GS base */
DECLARE_FIELD_NW_RW(0x6C08, host_GS_base,
					(1),
					UNDEFINED)
/* Host TR base */
DECLARE_FIELD_NW_RW(0x6C0A, host_TR_base,
					(1),
					UNDEFINED)
/* Host GDTR base */
DECLARE_FIELD_NW_RW(0x6C0C, host_GDTR_base,
					(1),
					UNDEFINED)
/* Host IDTR base */
DECLARE_FIELD_NW_RW(0x6C0E, host_IDTR_base,
					(1),
					UNDEFINED)
/* Host IA32_SYSENTER_ESP */
DECLARE_FIELD_NW_RW(0x6C10, host_SYSENTER_ESP,
					(1),
					UNDEFINED)
/* Host IA32_SYSENTER_EIP */
DECLARE_FIELD_NW_RW(0x6C12, host_SYSENTER_EIP,
					(1),
					UNDEFINED)
/* Host RSP */
DECLARE_FIELD_NW_RW(0x6C14, host_RSP,
					(1),
					UNDEFINED)
/* Host RIP */
DECLARE_FIELD_NW_RW(0x6C16, host_RIP,
					(1),
					UNDEFINED)
/* Host IA32_S_CET */
DECLARE_FIELD_NW_RW(0x6C18, host_IA32_S_CET,
					(_vmx_hasctl_vmexit_load_cet_state(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Host SSP */
DECLARE_FIELD_NW_RW(0x6C1A, host_SSP,
					(_vmx_hasctl_vmexit_load_cet_state(FIELD_CTLS_ARG)),
					UNDEFINED)
/* Host IA32_INTERRUPT_SSP_TABLE_ADDR */
DECLARE_FIELD_NW_RW(0x6C1C, host_IA32_INTERRUPT_SSP_TABLE_ADDR,
					(_vmx_hasctl_vmexit_load_cet_state(FIELD_CTLS_ARG)),
					UNDEFINED)

#undef DECLARE_FIELD_16
#undef DECLARE_FIELD_64
#undef DECLARE_FIELD_32
#undef DECLARE_FIELD_NW
#undef DECLARE_FIELD_16_RO
#undef DECLARE_FIELD_64_RO
#undef DECLARE_FIELD_32_RO
#undef DECLARE_FIELD_NW_RO
#undef DECLARE_FIELD_16_RW
#undef DECLARE_FIELD_64_RW
#undef DECLARE_FIELD_32_RW
#undef DECLARE_FIELD_NW_RW
#undef FIELD_CTLS_ARG
#undef VMCS12_FIELDS_QEMU

