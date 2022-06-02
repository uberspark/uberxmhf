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

//vmx.h - Intel VMX definitions
//author: amit vasudevan (amitvasudevan@acm.org)

#define VMXON_SIZE		(4096)
#define VMCS_SIZE			(8192)

//VM Exit Interruption-information format
#define INTR_INFO_VECTOR_MASK           (0x000000ff)        // 7:0
#define INTR_INFO_INTR_TYPE_MASK        (0x00000700)        // 10:8
#define INTR_INFO_DELIVER_CODE_MASK     (0x00000800)        // 11
#define INTR_INFO_VALID_MASK            (0x80000000)      	// 31

#define VECTORING_INFO_VECTOR_MASK           	INTR_INFO_VECTOR_MASK
#define VECTORING_INFO_TYPE_MASK        			INTR_INFO_INTR_TYPE_MASK
#define VECTORING_INFO_DELIVER_CODE_MASK    	INTR_INFO_DELIVER_CODE_MASK
#define VECTORING_INFO_VALID_MASK       			INTR_INFO_VALID_MASK

#define INTR_TYPE_HW_INTERRUPT         	 (0UL << 8) // hardware/external interrupt
#define INTR_TYPE_NMI										 (2UL << 8)	// NMI
#define INTR_TYPE_HW_EXCEPTION           (3UL << 8) // processor exception
#define INTR_TYPE_SW_INTERRUPT         	 (4UL << 8) // software interrupt
#define INTR_TYPE_SW_EXCEPTION           (6UL << 8) // software exception (INTO, INT3)

//
#define VMX_EVENT_CANCEL  (0)
#define VMX_EVENT_INJECT  (1)

//
#define DF_VECTOR 	8
#define INT1_VECTOR	0x1
#define NMI_VECTOR	0x2
#define INT3_VECTOR	0x3
#define GP_VECTOR 	13
#define PF_VECTOR 	14

#define INTERCEPT_EXCEPTIONS_00 (0x00)
#define INTERCEPT_EXCEPTIONS_01 (0x01)
#define INTERCEPT_EXCEPTIONS_02 (0x02)
#define INTERCEPT_EXCEPTIONS_03 (0x03)
#define INTERCEPT_EXCEPTIONS_04 (0x04)
#define INTERCEPT_EXCEPTIONS_05 (0x05)
#define INTERCEPT_EXCEPTIONS_06 (0x06)
#define INTERCEPT_EXCEPTIONS_07 (0x07)
#define INTERCEPT_EXCEPTIONS_08 (0x08)
#define INTERCEPT_EXCEPTIONS_09 (0x09)
#define INTERCEPT_EXCEPTIONS_0A (0x0A)
#define INTERCEPT_EXCEPTIONS_0B (0x0B)
#define INTERCEPT_EXCEPTIONS_0C (0x0C)
#define INTERCEPT_EXCEPTIONS_0D (0x0D)
#define INTERCEPT_EXCEPTIONS_0E (0x0E)
#define INTERCEPT_EXCEPTIONS_0F (0x0F)
#define INTERCEPT_EXCEPTIONS_10 (0x10)
#define INTERCEPT_EXCEPTIONS_11 (0x11)
#define INTERCEPT_EXCEPTIONS_12 (0x12)
#define INTERCEPT_EXCEPTIONS_13 (0x13)
#define INTERCEPT_EXCEPTIONS_14 (0x14)
#define INTERCEPT_EXCEPTIONS_15 (0x15)
#define INTERCEPT_EXCEPTIONS_16 (0x16)
#define INTERCEPT_EXCEPTIONS_17 (0x17)
#define INTERCEPT_EXCEPTIONS_18 (0x18)
#define INTERCEPT_EXCEPTIONS_19 (0x19)
#define INTERCEPT_EXCEPTIONS_1A (0x1A)
#define INTERCEPT_EXCEPTIONS_1B (0x1B)
#define INTERCEPT_EXCEPTIONS_1C (0x1C)
#define INTERCEPT_EXCEPTIONS_1D (0x1D)
#define INTERCEPT_EXCEPTIONS_1E (0x1E)
#define INTERCEPT_EXCEPTIONS_1F (0x1F)
#define INTERCEPT_EXCEPTIONS_20 (0x20)


#define INTERCEPT_INVLPG          0x21
#define INTERCEPT_CR3_READ        0x22
#define INTERCEPT_CR3_WRITE       0x23
#define INTERCEPT_CR0_SEL_WRITE   0x24
#define INTERCEPT_CR4_WRITE       0x25
#define INTERCEPT_MSR             0x26
#define INTERCEPT_IOIO            0x27
#define INTERCEPT_VMMCALL         0x28
#define INTERCEPT_EXCEPTIONS      0x29

#define VMX_VMEXIT_EXCEPTION      0
#define VMX_VMEXIT_INVLPG         14
#define VMX_VMEXIT_NMI_WINDOW     8
#define VMX_VMEXIT_MONITOR_TRAP   37

#define VMX_VMEXIT_CRX_ACCESS 0x1C

#define VMX_CRX_ACCESS_FROM	0x1
#define VMX_CRX_ACCESS_TO		0x0

#define VMX_VMEXIT_CR3_READ 28
#define VMX_VMEXIT_CR3_WRITE  28
#define VMX_VMEXIT_CR0_SEL_WRITE 28
#define VMX_VMEXIT_CR4_WRITE 28
#define VMX_VMEXIT_CRX_READWRITE 28
#define VMX_VMEXIT_MSR_READ   31
#define VMX_VMEXIT_MSR_WRITE 32
#define VMX_VMEXIT_IOIO 30
#define VMX_VMEXIT_VMCALL 18
#define VMX_VMEXIT_HLT 12
#define VMX_VMEXIT_INVLPG 14
#define VMX_VMEXIT_RDMSR	0x1f
#define VMX_VMEXIT_WRMSR	0x20
#define VMX_VMEXIT_CPUID	0x0a
#define VMX_VMEXIT_INIT   0x3
#define VMX_VMEXIT_EPT_VIOLATION  0x30
#define VMX_VMEXIT_TASKSWITCH	0x9
#define	VMX_VMEXIT_WBINVD		54
#define VMX_VMEXIT_XSETBV		55

#define VMX_VMEXIT_EPT_VIOLATON	48
#define VMX_VMEXIT_EPT_MISCONFIGURATION 49

//VMEXIT_IOIO defines
#define	IO_SIZE_BYTE	0x0
#define IO_SIZE_WORD	0x1
#define IO_SIZE_DWORD	0x3

#define IO_TYPE_IN		0x1
#define IO_TYPE_OUT		0x0

#define IO_INSN_STRING	0x1
#define IO_INSN_NORMAL	0x0
#define IO_INSN_REP			0x1
#define IO_INSN_OPCODE_IMM	0x1


#ifndef __ASSEMBLY__


typedef struct {
  u32 writable;
  u32 encoding;
  u32 addressofvariable;
} __attribute__ ((packed)) VMCSENCODINGS;


typedef struct {
	u32 type: 4;
	u32 desctype: 1; //0=system, 1=code or data
	u32 dpl: 2;
	u32 p: 1;
	u32 res1: 4;
	u32 avl: 1;
	u32 csmode: 1;
	u32 s: 1; //0=16-bit segment, 1=32-bit segment
	u32 g: 1;
	u32 usable: 1; //0=usable, 1=unusable
	u32 res2: 15;
} __attribute__ ((packed)) segment_desc_accessrights;


/* cf. IA32_SDM_Vol3B table 24-7 */
enum EPTViolationCode
{
	EPT_ERRORCODE_READ	   = 1 << 0,
	EPT_ERRORCODE_WRITE	   = 1 << 1,
	EPT_ERRORCODE_EXEC	   = 1 << 2,
	EPT_ERRORCODE_READABLE = 1 << 3,
	EPT_ERRORCODE_WRITABLE = 1 << 4,
	EPT_ERRORCODE_EXECABLE = 1 << 5,
	EPT_ERRORCODE_RESERVED = 1 << 6,
	EPT_ERRORCODE_VADDR_VALID = 1 << 7,
	EPT_ERRORCODE_TABLEWALK= 1 << 8,
};
#define  EPT_ERRORCODE_PRESENT ((EPT_ERRORCODE_READABLE)+(EPT_ERRORCODE_WRITABLE)+(EPT_ERRORCODE_EXECABLE))

#define	EPT_PROT_READ		(1UL << 0)
#define EPT_PROT_WRITE	(1UL << 1)
#define EPT_PROT_EXEC		(1UL << 2)

#define EPT_PML4_SIZE 512
#define EPT_PDPT_SIZE 512
#define EPT_PD_SIZE 512
#define EPT_PT_SIZE 512

/* max bits used in physical devices. processor-dependent. */
#define M 47

/* PML4E bit fields */
#define EPT_PML4E_IGN0_HI 63
#define EPT_PML4E_IGN0_LO 52
#define EPT_PML4E_RSVD0_HI 51
#define EPT_PML4E_RSVD0_LO M
#define EPT_PML4E_PDPT_HI (M-1)
#define EPT_PML4E_PDPT_LO 12
#define EPT_PML4E_IGN1_HI 11
#define EPT_PML4E_IGN1_LO 8
#define EPT_PML4E_RSVD2_HI 7
#define EPT_PML4E_RSVD2_LO 3
#define EPT_PML4E_X_HI 2
#define EPT_PML4E_X_LO 2
#define EPT_PML4E_W_HI 1
#define EPT_PML4E_W_LO 1
#define EPT_PML4E_R_HI 0
#define EPT_PML4E_R_LO 0
#define EPT_PML4E_NP_HI 2 /* not-present */
#define EPT_PML4E_NP_LO 0


/* PDPTE bit fields */
#define EPT_PDPTE_IGN0_HI 63
#define EPT_PDPTE_IGN0_LO 52
#define EPT_PDPTE_RSVD0_HI 51
#define EPT_PDPTE_RSVD0_LO M
/****** when ISPAGE==0 ********************/
  #define EPT_PDPTE_PD_HI (M-1)
  #define EPT_PDPTE_PD_LO 12
/******* when ISPAGE==1********************/
  #define EPT_PDPTE_PAGE_HI (M-1)
  #define EPT_PDPTE_PAGE_LO 30
  #define EPT_PDPTE_RSVD1_HI 29
  #define EPT_PDPTE_RSVD1_LO 12
/******************************************/
#define EPT_PDPTE_IGN1_HI 11
#define EPT_PDPTE_IGN1_LO 8
#define EPT_PDPTE_ISPAGE_HI 7
#define EPT_PDPTE_ISPAGE_LO 7
/****** when ISPAGE==0 ********************/
  #define EPT_PDPTE_RSVD2_HI 6
  #define EPT_PDPTE_RSVD2_LO 3
/****** when ISPAGE==1 ********************/
  #define EPT_PDPTE_IPAT_HI 6
  #define EPT_PDPTE_IPAT_LO 6
  #define EPT_PDPTE_EPTMT_HI 5
  #define EPT_PDPTE_EPTMT_LO 3
/******************************************/
#define EPT_PDPTE_X_HI 2
#define EPT_PDPTE_X_LO 2
#define EPT_PDPTE_W_HI 1
#define EPT_PDPTE_W_LO 1
#define EPT_PDPTE_R_HI 0
#define EPT_PDPTE_R_LO 0
#define EPT_PDPTE_NP_HI 2 /* not-present */
#define EPT_PDPTE_NP_LO 0
#define EPT_PDPTE_PROT_HI 2
#define EPT_PDPTE_PROT_LO 0

/* PDE bit fields */
#define EPT_PDE_IGN0_HI 63
#define EPT_PDE_IGN0_LO 52
#define EPT_PDE_RSVD0_HI 51
#define EPT_PDE_RSVD0_LO M
/****** when ISPAGE==0 ********************/
  #define EPT_PDE_PT_HI (M-1)
  #define EPT_PDE_PT_LO 12
/******* when ISPAGE==1********************/
  #define EPT_PDE_PAGE_HI (M-1)
  #define EPT_PDE_PAGE_LO 21
  #define EPT_PDE_RSVD1_HI 20
  #define EPT_PDE_RSVD1_LO 12
/******************************************/
#define EPT_PDE_IGN1_HI 11
#define EPT_PDE_IGN1_LO 8
#define EPT_PDE_ISPAGE_HI 7
#define EPT_PDE_ISPAGE_LO 7
/****** when ISPAGE==0 ********************/
  #define EPT_PDE_RSVD2_HI 6
  #define EPT_PDE_RSVD2_LO 3
/****** when ISPAGE==1 ********************/
  #define EPT_PDE_IPAT_HI 6
  #define EPT_PDE_IPAT_LO 6
  #define EPT_PDE_EPTMT_HI 5
  #define EPT_PDE_EPTMT_LO 3
/******************************************/
#define EPT_PDE_X_HI 2
#define EPT_PDE_X_LO 2
#define EPT_PDE_W_HI 1
#define EPT_PDE_W_LO 1
#define EPT_PDE_R_HI 0
#define EPT_PDE_R_LO 0
#define EPT_PDE_NP_HI 2 /* not-present */
#define EPT_PDE_NP_LO 0
#define EPT_PDE_PROT_HI 2
#define EPT_PDE_PROT_LO 0

/* PTE bit fields */
#define EPT_PTE_IGN0_HI 63
#define EPT_PTE_IGN0_LO 52
#define EPT_PTE_RSVD0_HI 51
#define EPT_PTE_RSVD0_LO M
#define EPT_PTE_PAGE_HI (M-1)
#define EPT_PTE_PAGE_LO 12
#define EPT_PTE_IGN1_HI 11
#define EPT_PTE_IGN1_LO 7
#define EPT_PTE_IPAT_HI 6
#define EPT_PTE_IPAT_LO 6
#define EPT_PTE_EPTMT_HI 5
#define EPT_PTE_EPTMT_LO 3
#define EPT_PTE_X_HI 2
#define EPT_PTE_X_LO 2
#define EPT_PTE_W_HI 1
#define EPT_PTE_W_LO 1
#define EPT_PTE_R_HI 0
#define EPT_PTE_R_LO 0
#define EPT_PTE_NP_HI 2 /* not-present */
#define EPT_PTE_NP_LO 0
#define EPT_PTE_PROT_HI 2
#define EPT_PTE_PROT_LO 0

/* guest physical address */
#define EPT_GPA_PML4_I_HI 47
#define EPT_GPA_PML4_I_LO 39
#define EPT_GPA_PDPT_I_HI 38
#define EPT_GPA_PDPT_I_LO 30
#define EPT_GPA_PD_I_HI 29
#define EPT_GPA_PD_I_LO 21
#define EPT_GPA_PT_I_HI 20
#define EPT_GPA_PT_I_LO 12
#define EPT_GPA_OFFSET_HI 11
#define EPT_GPA_OFFSET_LO 0

enum {
  TASK_SWITCH_CALL = 0,
  TASK_SWITCH_IRET = 1,
  TASK_SWITCH_JMP = 2,
  TASK_SWITCH_GATE = 3,
};


typedef struct msr_entry {
	u32 index;
	u32 reserved;
	u64 data;
} __attribute__((packed)) msr_entry_t;


//VMX VMCS fields
struct _vmx_vmcsfields {
#if defined(__NESTED_PAGING__)
  //16-bit control fields
  u16       control_vpid;
#endif
  // Natural 32-bit Control fields
  u32       control_VMX_pin_based;
  u32       control_VMX_cpu_based;
//#if defined(__NESTED_PAGING__)
  u32       control_VMX_seccpu_based;
//#endif
  u32       control_exception_bitmap;
  u32       control_pagefault_errorcode_mask;
  u32       control_pagefault_errorcode_match;
  u32       control_CR3_target_count;
  u32       control_VM_exit_controls;
  u32       control_VM_exit_MSR_store_count;
  u32       control_VM_exit_MSR_load_count;
  u32       control_VM_entry_controls;
  u32       control_VM_entry_MSR_load_count;
  u32       control_VM_entry_interruption_information;
  u32       control_VM_entry_exception_errorcode;
  u32       control_VM_entry_instruction_length;
  u32       control_Task_PRivilege_Threshold;
  // Natural 64-bit Control fields
  ulong_t   control_CR0_mask;
  ulong_t   control_CR4_mask;
  ulong_t   control_CR0_shadow;
  ulong_t   control_CR4_shadow;
#ifndef __DEBUG_QEMU__
  ulong_t   control_CR3_target0;
  ulong_t   control_CR3_target1;
  ulong_t   control_CR3_target2;
  ulong_t   control_CR3_target3;
#endif /* !__DEBUG_QEMU__ */
  // Full 64-bit Control fields
  union {
    u64     control_IO_BitmapA_address;
    struct {
      u32   control_IO_BitmapA_address_full;
      u32   control_IO_BitmapA_address_high;
    };
  };
  union {
    u64     control_IO_BitmapB_address;
    struct {
      u32   control_IO_BitmapB_address_full;
      u32   control_IO_BitmapB_address_high;
    };
  };
  union {
    u64     control_MSR_Bitmaps_address;
    struct {
      u32   control_MSR_Bitmaps_address_full;
      u32   control_MSR_Bitmaps_address_high;
    };
  };
  union {
    u64     control_VM_exit_MSR_store_address;
    struct {
      u32   control_VM_exit_MSR_store_address_full;
      u32   control_VM_exit_MSR_store_address_high;
    };
  };
  union {
    u64     control_VM_exit_MSR_load_address;
    struct {
      u32   control_VM_exit_MSR_load_address_full;
      u32   control_VM_exit_MSR_load_address_high;
    };
  };
  union {
    u64     control_VM_entry_MSR_load_address;
    struct {
      u32   control_VM_entry_MSR_load_address_full;
      u32   control_VM_entry_MSR_load_address_high;
    };
  };
#ifndef __DEBUG_QEMU__
  union {
    u64     control_Executive_VMCS_pointer;
    struct {
      u32   control_Executive_VMCS_pointer_full;
      u32   control_Executive_VMCS_pointer_high;
    };
  };
#endif /* !__DEBUG_QEMU__ */
  union {
    u64     control_TSC_offset;
    struct {
      u32   control_TSC_offset_full;
      u32   control_TSC_offset_high;
    };
  };
  union {
    u64     control_virtual_APIC_page_address;
    struct {
      u32   control_virtual_APIC_page_address_full;
      u32   control_virtual_APIC_page_address_high;
    };
  };
#if defined(__NESTED_PAGING__)
  union {
    u64     control_EPT_pointer;
    struct {
      u32   control_EPT_pointer_full;
      u32   control_EPT_pointer_high;
    };
  };
#endif
  // Natural 64-bit Host-State fields
  ulong_t   host_CR0;
  ulong_t   host_CR3;
  ulong_t   host_CR4;
  ulong_t   host_FS_base;
  ulong_t   host_GS_base;
  ulong_t   host_TR_base;
  ulong_t   host_GDTR_base;
  ulong_t   host_IDTR_base;
  ulong_t   host_SYSENTER_ESP;
  ulong_t   host_SYSENTER_EIP;
  ulong_t   host_RSP;
  ulong_t   host_RIP;
  // Natural 32-bit Host-State fields
  u32       host_SYSENTER_CS;
  // Natural 16-bit Host-State fields
  u16       host_ES_selector;
  u16       host_CS_selector;
  u16       host_SS_selector;
  u16       host_DS_selector;
  u16       host_FS_selector;
  u16       host_GS_selector;
  u16       host_TR_selector;
  // Natural 64-bit Guest-State fields
  ulong_t   guest_CR0;
  ulong_t   guest_CR3;
  ulong_t   guest_CR4;
  ulong_t   guest_ES_base;
  ulong_t   guest_CS_base;
  ulong_t   guest_SS_base;
  ulong_t   guest_DS_base;
  ulong_t   guest_FS_base;
  ulong_t   guest_GS_base;
  ulong_t   guest_LDTR_base;
  ulong_t   guest_TR_base;
  ulong_t   guest_GDTR_base;
  ulong_t   guest_IDTR_base;
  ulong_t   guest_DR7;
  ulong_t   guest_RSP;
  ulong_t   guest_RIP;
  ulong_t   guest_RFLAGS;
  ulong_t   guest_pending_debug_x;
  ulong_t   guest_SYSENTER_ESP;
  ulong_t   guest_SYSENTER_EIP;
  // Natural 32-bit Guest-State fields
  u32       guest_ES_limit;
  u32       guest_CS_limit;
  u32       guest_SS_limit;
  u32       guest_DS_limit;
  u32       guest_FS_limit;
  u32       guest_GS_limit;
  u32       guest_LDTR_limit;
  u32       guest_TR_limit;
  u32       guest_GDTR_limit;
  u32       guest_IDTR_limit;
  u32       guest_ES_access_rights;
  u32       guest_CS_access_rights;
  u32       guest_SS_access_rights;
  u32       guest_DS_access_rights;
  u32       guest_FS_access_rights;
  u32       guest_GS_access_rights;
  u32       guest_LDTR_access_rights;
  u32       guest_TR_access_rights;
  u32       guest_interruptibility;
  u32       guest_activity_state;
#ifndef __DEBUG_QEMU__
  u32       guest_SMBASE;
#endif /* !__DEBUG_QEMU__ */
  u32       guest_SYSENTER_CS;
  // Natural 16-bit Guest-State fields
  u16       guest_ES_selector;
  u16       guest_CS_selector;
  u16       guest_SS_selector;
  u16       guest_DS_selector;
  u16       guest_FS_selector;
  u16       guest_GS_selector;
  u16       guest_LDTR_selector;
  u16       guest_TR_selector;
  // Full 64-bit Guest-State fields
  union {
    u64     guest_VMCS_link_pointer;
    struct {
      u32   guest_VMCS_link_pointer_full;
      u32   guest_VMCS_link_pointer_high;
    };
  };
  union {
    u64     guest_IA32_DEBUGCTL;
    struct {
      u32   guest_IA32_DEBUGCTL_full;
      u32   guest_IA32_DEBUGCTL_high;
    };
  };
#if defined(__NESTED_PAGING__)
  union {
    u64     guest_paddr;
    struct {
      u32   guest_paddr_full;
      u32   guest_paddr_high;
    };
  };
  union {
    u64     guest_PDPTE0;
    struct {
      u32   guest_PDPTE0_full;
      u32   guest_PDPTE0_high;
    };
  };
  union {
    u64     guest_PDPTE1;
    struct {
      u32   guest_PDPTE1_full;
      u32   guest_PDPTE1_high;
    };
  };
  union {
    u64     guest_PDPTE2;
    struct {
      u32   guest_PDPTE2_full;
      u32   guest_PDPTE2_high;
    };
  };
  union {
    u64     guest_PDPTE3;
    struct {
      u32   guest_PDPTE3_full;
      u32   guest_PDPTE3_high;
    };
  };
#endif
  //Read-Only Fields
  u32       info_vminstr_error;
  u32       info_vmexit_reason;
  u32       info_vmexit_interrupt_information;
  u32       info_vmexit_interrupt_error_code;
  u32       info_IDT_vectoring_information;
  u32       info_IDT_vectoring_error_code;
  u32       info_vmexit_instruction_length;
  u32       info_vmx_instruction_information;
  ulong_t   info_exit_qualification;
#ifndef __DEBUG_QEMU__
  ulong_t   info_IO_RCX;
  ulong_t   info_IO_RSI;
  ulong_t   info_IO_RDI;
  ulong_t   info_IO_RIP;
#endif /* !__DEBUG_QEMU__ */
  ulong_t   info_guest_linear_address;
};


struct _vmx_vmcsrofields_encodings	{
 unsigned int  encoding;
 unsigned int  fieldoffset;
 unsigned int  membersize;
};

struct _vmx_vmcsrwfields_encodings	{
 unsigned int  encoding;
 unsigned int  fieldoffset;
 unsigned int  membersize;
};

/* VM-Entry Interruption-Information Field */
struct _vmx_event_injection {
    u32 vector:      8;
    u32 type:        3;
    u32 errorcode:   1;
    u32 reserved:   19;
    u32 valid:       1;
} __attribute__ ((packed));

//VMX functions
static inline void __vmx_vmxon(u64 vmxonRegion){
  __asm__("vmxon %0\n\t"
	  : //no outputs
	  : "m"(vmxonRegion)
	  : "cc");
}

static inline u32 __vmx_vmwrite(unsigned long encoding, unsigned long value){
  u32 status;
  __asm__("vmwrite %2, %1 \r\n"
          "jbe 1f \r\n"
          "movl $1, %0 \r\n"
          "jmp 2f \r\n"
          "1: movl $0, %0 \r\n"
          "2: \r\n"
	  : "=g"(status)
	  : "r"(encoding), "g"(value)
      : "cc"
    );
	return status;
}

/* Write 16-bit VMCS field, never fails */
static inline void __vmx_vmwrite16(unsigned long encoding, u16 value) {
	HALT_ON_ERRORCOND((encoding >> 12) == 0UL);
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding, value));
}

/* Write 64-bit VMCS field, never fails */
static inline void __vmx_vmwrite64(unsigned long encoding, u64 value) {
	HALT_ON_ERRORCOND((encoding >> 12) == 2UL);
	HALT_ON_ERRORCOND((encoding & 0x1) == 0x0);
#ifdef __AMD64__
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding, value));
#elif defined(__I386__)
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding, value));
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding + 1, value >> 32));
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
}

/* Write 32-bit VMCS field, never fails */
static inline void __vmx_vmwrite32(unsigned long encoding, u32 value) {
	HALT_ON_ERRORCOND((encoding >> 12) == 4UL);
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding, value));
}

/* Write natural width (NW) VMCS field, never fails */
static inline void __vmx_vmwriteNW(unsigned long encoding, ulong_t value) {
	HALT_ON_ERRORCOND((encoding >> 12) == 6UL);
	HALT_ON_ERRORCOND(__vmx_vmwrite(encoding, value));
}

static inline u32 __vmx_vmread(unsigned long encoding, unsigned long *value){
	u32 status;
	__asm__ __volatile__("vmread %2, %0 \r\n"
                       "jbe 1f \r\n"
                       "movl $1, %1 \r\n"
                       "jmp 2f \r\n"
                       "1: movl $0, %1 \r\n"
                       "2: \r\n"
	  : "=g"(*value), "=g"(status)
	  : "r"(encoding)
	  : "cc");
	return status;
}

/* Read 16-bit VMCS field, never fails */
static inline u16 __vmx_vmread16(unsigned long encoding) {
	unsigned long value;
	HALT_ON_ERRORCOND((encoding >> 12) == 0UL);
	HALT_ON_ERRORCOND(__vmx_vmread(encoding, &value));
	HALT_ON_ERRORCOND(value == (unsigned long)(u16)value);
	return value;
}

static inline u64 __vmx_vmread64(unsigned long encoding) {
#ifdef __AMD64__
	unsigned long value;
	HALT_ON_ERRORCOND((encoding >> 12) == 2UL);
	HALT_ON_ERRORCOND(__vmx_vmread(encoding, &value));
	return value;
#elif defined(__I386__)
	union {
		struct {
			unsigned long low, high;
		};
		u64 full;
	} ans;
	_Static_assert(sizeof(u32) == sizeof(unsigned long));
	HALT_ON_ERRORCOND((encoding >> 12) == 2UL);
	HALT_ON_ERRORCOND((encoding & 0x1) == 0x0);
	HALT_ON_ERRORCOND(__vmx_vmread(encoding, &ans.low));
	HALT_ON_ERRORCOND(__vmx_vmread(encoding + 1, &ans.high));
	return ans.full;
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
}

/* Read 32-bit VMCS field, never fails */
static inline u32 __vmx_vmread32(unsigned long encoding) {
	unsigned long value;
	HALT_ON_ERRORCOND((encoding >> 12) == 4UL);
	HALT_ON_ERRORCOND(__vmx_vmread(encoding, &value));
	HALT_ON_ERRORCOND(value == (unsigned long)(u32)value);
	return value;
}

/* Read natural width (NW) VMCS field, never fails */
static inline ulong_t __vmx_vmreadNW(unsigned long encoding) {
	unsigned long value;
	HALT_ON_ERRORCOND((encoding >> 12) == 6UL);
	HALT_ON_ERRORCOND(__vmx_vmread(encoding, &value));
	HALT_ON_ERRORCOND(value == (unsigned long)(ulong_t)value);
	return value;
}

static inline u32 __vmx_vmclear(u64 vmcs){
  u32 status;
  __asm__("vmclear %1			\r\n"
	   	"jbe	1f    		\r\n"
      "movl $1, %%eax \r\n"
      "jmp  2f  \r\n"
      "1: movl $0, %%eax \r\n"
      "2: movl %%eax, %0 \r\n"
    : "=m" (status)
    : "m"(vmcs)
    : "%eax", "cc"
  );
  return status;
}

static inline u32 __vmx_vmptrld(u64 vmcs){
  u32 status;
  __asm__("vmptrld %1			\r\n"
	   	"jbe	1f    		\r\n"
      "movl $1, %%eax \r\n"
      "jmp  2f  \r\n"
      "1: movl $0, %%eax \r\n"
      "2: movl %%eax, %0 \r\n"
    : "=m" (status)
    : "m"(vmcs)
    : "%eax", "cc"
  );
  return status;
}

// VMX instruction INVVPID
//		Invalidate Translations Based on VPID
// INVVPID r32, m128
//returns 1 on success, 0 on failure

#define	VMX_INVVPID_INDIVIDUALADDRESS		0
#define VMX_INVVPID_SINGLECONTEXT			1
#define VMX_INVVPID_ALLCONTEXTS				2
#define VMX_INVVPID_SINGLECONTEXTGLOBAL		3

static inline u32 __vmx_invvpid(int invalidation_type, u16 vpid, u32 linearaddress){
	//return status (1 or 0)
	u32 status;

	//invvpid descriptor
	struct {
		u64 vpid 	 : 16;
		u64 reserved : 48;
		u64 linearaddress;
    } invvpiddescriptor = { vpid, 0, linearaddress };

	//issue invvpid instruction
	//note: GCC does not seem to support this instruction directly
	//so we encode it as hex
	__asm__(".byte 0x66, 0x0f, 0x38, 0x81, 0x08 \r\n"
          "movl $1, %%eax \r\n"
		  "ja	1f    	  \r\n"
		  "movl $0, %%eax \r\n"
		  "1: movl %%eax, %0 \r\n"
    : "=m" (status)
    : "a"(&invvpiddescriptor), "c"(invalidation_type)
	: "cc", "memory");

	return status;
}


// VMX instruction INVEPT
//		Invalidate Translations Derived from EPT
// INVEPT r32, m128
//returns 1 on success, 0 on failure

#define	VMX_INVEPT_SINGLECONTEXT			1
#define VMX_INVEPT_GLOBAL					2

static inline u32 __vmx_invept(int invalidation_type, u64 eptp){
	//return status (1 or 0)
	u32 status;

	//invvpid descriptor
	struct {
		u64 eptp;
		u64 reserved;
    } inveptdescriptor = { eptp, 0};

	//issue invept instruction
	//note: GCC does not seem to support this instruction directly
	//so we encode it as hex
	__asm__(".byte 0x66, 0x0f, 0x38, 0x80, 0x08 \r\n"
          "movl $1, %%eax \r\n"
		  "ja	1f    	  \r\n"
		  "movl $0, %%eax \r\n"
		  "1: movl %%eax, %0 \r\n"
    : "=m" (status)
    : "a"(&inveptdescriptor), "c"(invalidation_type)
	: "cc", "memory");

	return status;
}




#endif
