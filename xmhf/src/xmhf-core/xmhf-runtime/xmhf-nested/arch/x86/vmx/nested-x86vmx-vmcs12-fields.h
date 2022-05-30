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

// nested-x86vmx-vmcs12-fields.h
// Enumerate through all VMCS fields
// author: Eric Li (xiaoyili@andrew.cmu.edu)

#ifndef DECLARE_FIELD_16_RO
 #ifdef DECLARE_FIELD_16
  #define DECLARE_FIELD_16_RO(encoding, name, extra) \
          DECLARE_FIELD_16(encoding, name, extra)
 #else
  #define DECLARE_FIELD_16_RO(encoding, name, extra)
 #endif
#endif

#ifndef DECLARE_FIELD_32_RO
 #ifdef DECLARE_FIELD_32
  #define DECLARE_FIELD_32_RO(encoding, name, extra) \
          DECLARE_FIELD_32(encoding, name, extra)
 #else
  #define DECLARE_FIELD_32_RO(encoding, name, extra)
 #endif
#endif

#ifndef DECLARE_FIELD_64_RO
 #ifdef DECLARE_FIELD_64
  #define DECLARE_FIELD_64_RO(encoding, name, extra) \
          DECLARE_FIELD_64(encoding, name, extra)
 #else
  #define DECLARE_FIELD_64_RO(encoding, name, extra)
 #endif
#endif

#ifndef DECLARE_FIELD_NW_RO
 #ifdef DECLARE_FIELD_NW
  #define DECLARE_FIELD_NW_RO(encoding, name, extra) \
          DECLARE_FIELD_NW(encoding, name, extra)
 #else
  #define DECLARE_FIELD_NW_RO(encoding, name, extra)
 #endif
#endif
#ifndef DECLARE_FIELD_16_RW
 #ifdef DECLARE_FIELD_16
  #define DECLARE_FIELD_16_RW(encoding, name, extra) \
          DECLARE_FIELD_16(encoding, name, extra)
 #else
  #define DECLARE_FIELD_16_RW(encoding, name, extra)
 #endif
#endif

#ifndef DECLARE_FIELD_32_RW
 #ifdef DECLARE_FIELD_32
  #define DECLARE_FIELD_32_RW(encoding, name, extra) \
          DECLARE_FIELD_32(encoding, name, extra)
 #else
  #define DECLARE_FIELD_32_RW(encoding, name, extra)
 #endif
#endif

#ifndef DECLARE_FIELD_64_RW
 #ifdef DECLARE_FIELD_64
  #define DECLARE_FIELD_64_RW(encoding, name, extra) \
          DECLARE_FIELD_64(encoding, name, extra)
 #else
  #define DECLARE_FIELD_64_RW(encoding, name, extra)
 #endif
#endif

#ifndef DECLARE_FIELD_NW_RW
 #ifdef DECLARE_FIELD_NW
  #define DECLARE_FIELD_NW_RW(encoding, name, extra) \
          DECLARE_FIELD_NW(encoding, name, extra)
 #else
  #define DECLARE_FIELD_NW_RW(encoding, name, extra)
 #endif
#endif

/* 16-Bit Control Fields */
DECLARE_FIELD_16_RW(0x0000, control_vpid, UNDEFINED)
DECLARE_FIELD_16_RW(0x0002, control_post_interrupt_notification_vec, UNDEFINED)
DECLARE_FIELD_16_RW(0x0004, control_eptp_index, UNDEFINED)

/* 16-Bit Guest-State Fields */
DECLARE_FIELD_16_RW(0x0800, guest_ES_selector, UNDEFINED)
DECLARE_FIELD_16_RW(0x0802, guest_CS_selector, UNDEFINED)
DECLARE_FIELD_16_RW(0x0804, guest_SS_selector, UNDEFINED)
DECLARE_FIELD_16_RW(0x0806, guest_DS_selector, UNDEFINED)
DECLARE_FIELD_16_RW(0x0808, guest_FS_selector, UNDEFINED)
DECLARE_FIELD_16_RW(0x080A, guest_GS_selector, UNDEFINED)
DECLARE_FIELD_16_RW(0x080C, guest_LDTR_selector, UNDEFINED)
DECLARE_FIELD_16_RW(0x080E, guest_TR_selector, UNDEFINED)
DECLARE_FIELD_16_RW(0x0810, guest_interrupt_status, UNDEFINED)
DECLARE_FIELD_16_RW(0x0812, guest_PML_index, UNDEFINED)

/* 16-Bit Host-State Fields */
DECLARE_FIELD_16_RW(0x0C00, host_ES_selector, UNDEFINED)
DECLARE_FIELD_16_RW(0x0C02, host_CS_selector, UNDEFINED)
DECLARE_FIELD_16_RW(0x0C04, host_SS_selector, UNDEFINED)
DECLARE_FIELD_16_RW(0x0C06, host_DS_selector, UNDEFINED)
DECLARE_FIELD_16_RW(0x0C08, host_FS_selector, UNDEFINED)
DECLARE_FIELD_16_RW(0x0C0A, host_GS_selector, UNDEFINED)
DECLARE_FIELD_16_RW(0x0C0C, host_TR_selector, UNDEFINED)

/* 64-Bit Control Fields */
DECLARE_FIELD_64_RW(0x2000, control_IO_BitmapA_address, UNDEFINED)
DECLARE_FIELD_64_RW(0x2002, control_IO_BitmapB_address, UNDEFINED)
DECLARE_FIELD_64_RW(0x2004, control_MSR_Bitmaps_address, UNDEFINED)
DECLARE_FIELD_64_RW(0x2006, control_VM_exit_MSR_store_address, UNDEFINED)
DECLARE_FIELD_64_RW(0x2008, control_VM_exit_MSR_load_address, UNDEFINED)
DECLARE_FIELD_64_RW(0x200A, control_VM_entry_MSR_load_address, UNDEFINED)
DECLARE_FIELD_64_RW(0x200C, control_Executive_VMCS_pointer, UNDEFINED)
DECLARE_FIELD_64_RW(0x200E, control_PML_address, UNDEFINED)
DECLARE_FIELD_64_RW(0x2010, control_TSC_offset, UNDEFINED)
DECLARE_FIELD_64_RW(0x2012, control_virtual_APIC_address, UNDEFINED)
DECLARE_FIELD_64_RW(0x2014, control_APIC_access_address, UNDEFINED)
DECLARE_FIELD_64_RW(0x2016, control_posted_interrupt_desc_address, UNDEFINED)
DECLARE_FIELD_64_RW(0x2018, control_VM_function_controls, UNDEFINED)
DECLARE_FIELD_64_RW(0x201A, control_EPT_pointer, UNDEFINED)
DECLARE_FIELD_64_RW(0x201C, control_EOI_exit_bitmap_0, UNDEFINED)
DECLARE_FIELD_64_RW(0x201E, control_EOI_exit_bitmap_1, UNDEFINED)
DECLARE_FIELD_64_RW(0x2020, control_EOI_exit_bitmap_2, UNDEFINED)
DECLARE_FIELD_64_RW(0x2022, control_EOI_exit_bitmap_3, UNDEFINED)
DECLARE_FIELD_64_RW(0x2024, control_EPTP_list_address, UNDEFINED)
DECLARE_FIELD_64_RW(0x2026, control_VMREAD_bitmap_address, UNDEFINED)
DECLARE_FIELD_64_RW(0x2028, control_VMWRITE_bitmap_address, UNDEFINED)
DECLARE_FIELD_64_RW(0x202A, control_virt_exception_info_address, UNDEFINED)
DECLARE_FIELD_64_RW(0x202C, control_XSS_exiting_bitmap, UNDEFINED)
DECLARE_FIELD_64_RW(0x202E, control_ENCLS_exiting_bitmap, UNDEFINED)
DECLARE_FIELD_64_RW(0x2030, control_subpage_permission_table_pointer, UNDEFINED)
DECLARE_FIELD_64_RW(0x2032, control_TSC_multiplier, UNDEFINED)
DECLARE_FIELD_64_RW(0x2034, control_tertiary_proc_based_VMexec_ctls, UNDEFINED)
DECLARE_FIELD_64_RW(0x2036, control_ENCLV_exiting_bitmap, UNDEFINED)

/* 64-Bit Read-Only Data Field */
DECLARE_FIELD_64_RO(0x2400, guest_paddr, UNDEFINED)

/* 64-Bit Guest-State Fields */
DECLARE_FIELD_64_RW(0x2800, guest_VMCS_link_pointer, UNDEFINED)
DECLARE_FIELD_64_RW(0x2802, guest_IA32_DEBUGCTL, UNDEFINED)
DECLARE_FIELD_64_RW(0x2804, guest_IA32_PAT, UNDEFINED)
DECLARE_FIELD_64_RW(0x2806, guest_IA32_EFER, UNDEFINED)
DECLARE_FIELD_64_RW(0x2808, guest_IA32_PERF_GLOBAL_CTRL, UNDEFINED)
DECLARE_FIELD_64_RW(0x280A, guest_PDPTE0, UNDEFINED)
DECLARE_FIELD_64_RW(0x280C, guest_PDPTE1, UNDEFINED)
DECLARE_FIELD_64_RW(0x280E, guest_PDPTE2, UNDEFINED)
DECLARE_FIELD_64_RW(0x2810, guest_PDPTE3, UNDEFINED)
DECLARE_FIELD_64_RW(0x2812, guest_IA32_BNDCFGS, UNDEFINED)
DECLARE_FIELD_64_RW(0x2814, guest_IA32_RTIT_CTL, UNDEFINED)
DECLARE_FIELD_64_RW(0x2818, guest_IA32_PKRS, UNDEFINED)

/* 64-Bit Host-State Fields */
DECLARE_FIELD_64_RW(0x2C00, host_IA32_PAT, UNDEFINED)
DECLARE_FIELD_64_RW(0x2C02, host_IA32_EFER, UNDEFINED)
DECLARE_FIELD_64_RW(0x2C04, host_IA32_PERF_GLOBAL_CTRL, UNDEFINED)
DECLARE_FIELD_64_RW(0x2C06, host_IA32_PKRS, UNDEFINED)

/* 32-Bit Control Fields */
DECLARE_FIELD_32_RW(0x4000, control_VMX_pin_based, UNDEFINED)
DECLARE_FIELD_32_RW(0x4002, control_VMX_cpu_based, UNDEFINED)
DECLARE_FIELD_32_RW(0x4004, control_exception_bitmap, UNDEFINED)
DECLARE_FIELD_32_RW(0x4006, control_pagefault_errorcode_mask, UNDEFINED)
DECLARE_FIELD_32_RW(0x4008, control_pagefault_errorcode_match, UNDEFINED)
DECLARE_FIELD_32_RW(0x400A, control_CR3_target_count, UNDEFINED)
DECLARE_FIELD_32_RW(0x400C, control_VM_exit_controls, UNDEFINED)
DECLARE_FIELD_32_RW(0x400E, control_VM_exit_MSR_store_count, UNDEFINED)
DECLARE_FIELD_32_RW(0x4010, control_VM_exit_MSR_load_count, UNDEFINED)
DECLARE_FIELD_32_RW(0x4012, control_VM_entry_controls, UNDEFINED)
DECLARE_FIELD_32_RW(0x4014, control_VM_entry_MSR_load_count, UNDEFINED)
DECLARE_FIELD_32_RW(0x4016, control_VM_entry_interruption_information, UNDEFINED)
DECLARE_FIELD_32_RW(0x4018, control_VM_entry_exception_errorcode, UNDEFINED)
DECLARE_FIELD_32_RW(0x401A, control_VM_entry_instruction_length, UNDEFINED)
DECLARE_FIELD_32_RW(0x401C, control_Task_PRivilege_Threshold, UNDEFINED)
DECLARE_FIELD_32_RW(0x401E, control_VMX_seccpu_based, UNDEFINED)
DECLARE_FIELD_32_RW(0x4020, control_PLE_gap, UNDEFINED)
DECLARE_FIELD_32_RW(0x4022, control_PLE_window, UNDEFINED)

/* 32-Bit Read-Only Data Fields */
DECLARE_FIELD_32_RO(0x4400, info_vminstr_error, UNDEFINED)
DECLARE_FIELD_32_RO(0x4402, info_vmexit_reason, UNDEFINED)
DECLARE_FIELD_32_RO(0x4404, info_vmexit_interrupt_information, UNDEFINED)
DECLARE_FIELD_32_RO(0x4406, info_vmexit_interrupt_error_code, UNDEFINED)
DECLARE_FIELD_32_RO(0x4408, info_IDT_vectoring_information, UNDEFINED)
DECLARE_FIELD_32_RO(0x440A, info_IDT_vectoring_error_code, UNDEFINED)
DECLARE_FIELD_32_RO(0x440C, info_vmexit_instruction_length, UNDEFINED)
DECLARE_FIELD_32_RO(0x440E, info_vmx_instruction_information, UNDEFINED)

/* 32-Bit Guest-State Fields */
DECLARE_FIELD_32_RW(0x4800, guest_ES_limit, UNDEFINED)
DECLARE_FIELD_32_RW(0x4802, guest_CS_limit, UNDEFINED)
DECLARE_FIELD_32_RW(0x4804, guest_SS_limit, UNDEFINED)
DECLARE_FIELD_32_RW(0x4806, guest_DS_limit, UNDEFINED)
DECLARE_FIELD_32_RW(0x4808, guest_FS_limit, UNDEFINED)
DECLARE_FIELD_32_RW(0x480A, guest_GS_limit, UNDEFINED)
DECLARE_FIELD_32_RW(0x480C, guest_LDTR_limit, UNDEFINED)
DECLARE_FIELD_32_RW(0x480E, guest_TR_limit, UNDEFINED)
DECLARE_FIELD_32_RW(0x4810, guest_GDTR_limit, UNDEFINED)
DECLARE_FIELD_32_RW(0x4812, guest_IDTR_limit, UNDEFINED)
DECLARE_FIELD_32_RW(0x4814, guest_ES_access_rights, UNDEFINED)
DECLARE_FIELD_32_RW(0x4816, guest_CS_access_rights, UNDEFINED)
DECLARE_FIELD_32_RW(0x4818, guest_SS_access_rights, UNDEFINED)
DECLARE_FIELD_32_RW(0x481A, guest_DS_access_rights, UNDEFINED)
DECLARE_FIELD_32_RW(0x481C, guest_FS_access_rights, UNDEFINED)
DECLARE_FIELD_32_RW(0x481E, guest_GS_access_rights, UNDEFINED)
DECLARE_FIELD_32_RW(0x4820, guest_LDTR_access_rights, UNDEFINED)
DECLARE_FIELD_32_RW(0x4822, guest_TR_access_rights, UNDEFINED)
DECLARE_FIELD_32_RW(0x4824, guest_interruptibility, UNDEFINED)
DECLARE_FIELD_32_RW(0x4826, guest_activity_state, UNDEFINED)
DECLARE_FIELD_32_RW(0x4828, guest_SMBASE, UNDEFINED)
DECLARE_FIELD_32_RW(0x482A, guest_SYSENTER_CS, UNDEFINED)
DECLARE_FIELD_32_RW(0x482E, guest_VMX_preemption_timer_value, UNDEFINED)

/* 32-Bit Host-State Field */
DECLARE_FIELD_32_RW(0x4C00, host_IA32_SYSENTER_CS, UNDEFINED)

/* Natural-Width Control Fields */
DECLARE_FIELD_NW_RW(0x6000, control_CR0_mask, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6002, control_CR4_mask, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6004, control_CR0_shadow, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6006, control_CR4_shadow, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6008, control_CR3_target0, UNDEFINED)
DECLARE_FIELD_NW_RW(0x600A, control_CR3_target1, UNDEFINED)
DECLARE_FIELD_NW_RW(0x600C, control_CR3_target2, UNDEFINED)
DECLARE_FIELD_NW_RW(0x600E, control_CR3_target3, UNDEFINED)

/* Natural-Width Read-Only Data Fields */
DECLARE_FIELD_NW_RW(0x6400, info_exit_qualification, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6402, info_IO_RCX, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6404, info_IO_RSI, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6406, info_IO_RDI, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6408, info_IO_RIP, UNDEFINED)
DECLARE_FIELD_NW_RW(0x640A, info_guest_linear_address, UNDEFINED)

/* Natural-Width Guest-State Fields */
DECLARE_FIELD_NW_RW(0x6800, guest_CR0, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6802, guest_CR3, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6804, guest_CR4, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6806, guest_ES_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6808, guest_CS_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x680A, guest_SS_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x680C, guest_DS_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x680E, guest_FS_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6810, guest_GS_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6812, guest_LDTR_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6814, guest_TR_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6816, guest_GDTR_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6818, guest_IDTR_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x681A, guest_DR7, UNDEFINED)
DECLARE_FIELD_NW_RW(0x681C, guest_RSP, UNDEFINED)
DECLARE_FIELD_NW_RW(0x681E, guest_RIP, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6820, guest_RFLAGS, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6822, guest_pending_debug_x, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6824, guest_SYSENTER_ESP, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6826, guest_SYSENTER_EIP, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6828, guest_IA32_S_CET, UNDEFINED)
DECLARE_FIELD_NW_RW(0x682A, guest_SSP, UNDEFINED)
DECLARE_FIELD_NW_RW(0x682C, guest_IA32_INTERRUPT_SSP_TABLE_ADDR, UNDEFINED)

/* Natural-Width Host-State Fields */
DECLARE_FIELD_NW_RW(0x6C00, host_CR0, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6C02, host_CR3, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6C04, host_CR4, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6C06, host_FS_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6C08, host_GS_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6C0A, host_TR_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6C0C, host_GDTR_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6C0E, host_IDTR_base, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6C10, host_SYSENTER_ESP, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6C12, host_SYSENTER_EIP, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6C14, host_RSP, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6C16, host_RIP, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6C18, host_IA32_S_CET, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6C1A, host_SSP, UNDEFINED)
DECLARE_FIELD_NW_RW(0x6C1C, host_IA32_INTERRUPT_SSP_TABLE_ADDR, UNDEFINED)

#undef DECLARE_FIELD_16_RO
#undef DECLARE_FIELD_32_RO
#undef DECLARE_FIELD_64_RO
#undef DECLARE_FIELD_NW_RO
#undef DECLARE_FIELD_16_RW
#undef DECLARE_FIELD_32_RW
#undef DECLARE_FIELD_64_RW
#undef DECLARE_FIELD_NW_RW

#ifdef DECLARE_FIELD_16
#undef DECLARE_FIELD_16
#endif

#ifdef DECLARE_FIELD_32
#undef DECLARE_FIELD_32
#endif

#ifdef DECLARE_FIELD_64
#undef DECLARE_FIELD_64
#endif

#ifdef DECLARE_FIELD_NW
#undef DECLARE_FIELD_NW
#endif

