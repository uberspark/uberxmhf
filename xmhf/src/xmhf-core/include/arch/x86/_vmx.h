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

//Guest Interruptibility state
#define VMX_GUEST_INTR_BLOCK_STI    (1U << 0)   // Blocking by STI
#define VMX_GUEST_INTR_BLOCK_MOVSS  (1U << 1)   // Blocking by MOV SS
#define VMX_GUEST_INTR_BLOCK_SMI    (1U << 2)   // Blocking by SMI
#define VMX_GUEST_INTR_BLOCK_NMI    (1U << 3)   // Blocking by NMI
#define VMX_GUEST_INTR_ENCLV_INT    (1U << 4)   // Enclave interruption

//VM Exit Interruption-information format
#define INTR_INFO_VECTOR_MASK           (0x000000ff)        // 7:0
#define INTR_INFO_INTR_TYPE_MASK        (0x00000700)        // 10:8
#define INTR_INFO_DELIVER_CODE_MASK     (0x00000800)        // 11
#define INTR_INFO_VALID_MASK            (0x80000000)        // 31

#define VECTORING_INFO_VECTOR_MASK            INTR_INFO_VECTOR_MASK
#define VECTORING_INFO_TYPE_MASK              INTR_INFO_INTR_TYPE_MASK
#define VECTORING_INFO_DELIVER_CODE_MASK      INTR_INFO_DELIVER_CODE_MASK
#define VECTORING_INFO_VALID_MASK             INTR_INFO_VALID_MASK

#define INTR_TYPE_HW_INTERRUPT        (0U << 8)  // hardware/external interrupt
#define INTR_TYPE_NMI                 (2U << 8)  // NMI
#define INTR_TYPE_HW_EXCEPTION        (3U << 8)  // processor exception
#define INTR_TYPE_SW_INTERRUPT        (4U << 8)  // software interrupt
#define INTR_TYPE_PRIV_SW_EXCEPTION   (5U << 8)  // privleged software exception (INT1)
#define INTR_TYPE_SW_EXCEPTION        (6U << 8)  // software exception (INTO, INT3)

/* Used in bitfields (BF) */
#define INTR_TYPE_BF_HW_INTERRUPT       (0U)  // hardware/external interrupt
#define INTR_TYPE_BF_NMI                (2U)  // NMI
#define INTR_TYPE_BF_HW_EXCEPTION       (3U)  // processor exception
#define INTR_TYPE_BF_SW_INTERRUPT       (4U)  // software interrupt
#define INTR_TYPE_BF_PRIV_SW_EXCEPTION  (5U)  // privleged software exception (INT1)
#define INTR_TYPE_BF_SW_EXCEPTION       (6U)  // software exception (INTO, INT3)

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

/* Exception or non-maskable interrupt (NMI) */
#define VMX_VMEXIT_EXCEPTION            0
/* External interrupt */
#define VMX_VMEXIT_EXT_INTERRUPT        1
/* Triple fault */
#define VMX_VMEXIT_TRIPLE_FAULT         2
/* INIT signal. An INIT signal arrived */
#define VMX_VMEXIT_INIT                 3
/* Start-up IPI (SIPI) */
#define VMX_VMEXIT_SIPI                 4
/* I/O system-management interrupt (SMI) */
#define VMX_VMEXIT_IO_SMI               5
/* Other SMI */
#define VMX_VMEXIT_OTHER_SMI            6
/* Interrupt window */
#define VMX_VMEXIT_INTERRUPT_WINDOW     7
/* NMI window */
#define VMX_VMEXIT_NMI_WINDOW           8
/* Task switch */
#define VMX_VMEXIT_TASKSWITCH           9
/* CPUID */
#define VMX_VMEXIT_CPUID                10
/* GETSEC */
#define VMX_VMEXIT_GETSEC               11
/* HLT */
#define VMX_VMEXIT_HLT                  12
/* INVD */
#define VMX_VMEXIT_INVD                 13
/* INVLPG */
#define VMX_VMEXIT_INVLPG               14
/* RDPMC */
#define VMX_VMEXIT_RDPMC                15
/* RDTSC */
#define VMX_VMEXIT_RDTSC                16
/* RSM */
#define VMX_VMEXIT_RSM                  17
/* VMCALL */
#define VMX_VMEXIT_VMCALL               18
/* VMCLEAR */
#define VMX_VMEXIT_VMCLEAR              19
/* VMLAUNCH */
#define VMX_VMEXIT_VMLAUNCH             20
/* VMPTRLD */
#define VMX_VMEXIT_VMPTRLD              21
/* VMPTRST */
#define VMX_VMEXIT_VMPTRST              22
/* VMREAD */
#define VMX_VMEXIT_VMREAD               23
/* VMRESUME */
#define VMX_VMEXIT_VMRESUME             24
/* VMWRITE */
#define VMX_VMEXIT_VMWRITE              25
/* VMXOFF */
#define VMX_VMEXIT_VMXOFF               26
/* VMXON */
#define VMX_VMEXIT_VMXON                27
/* Control-register accesses */
#define VMX_VMEXIT_CRX_ACCESS           28
/* MOV DR */
#define VMX_VMEXIT_MOV_DR               29
/* I/O instruction */
#define VMX_VMEXIT_IOIO                 30
/* RDMSR */
#define VMX_VMEXIT_RDMSR                31
/* WRMSR */
#define VMX_VMEXIT_WRMSR                32
/* VM-entry failure due to invalid guest state */
#define VMX_VMEXIT_EMTRY_FAIL_GUEST_ST  33
/* VM-entry failure due to MSR loading */
#define VMX_VMEXIT_ENTRY_FAIL_MSR       34
/* Not defined basic exit reason: 35 */
#define VMX_VMEXIT_UNDEFINED35          35
/* MWAIT */
#define VMX_VMEXIT_MWAIT                36
/* Monitor trap flag */
#define VMX_VMEXIT_MONITOR_TRAP         37
/* Not defined basic exit reason: 38 */
#define VMX_VMEXIT_UNDEFINED38          38
/* MONITOR */
#define VMX_VMEXIT_MONITOR              39
/* PAUSE */
#define VMX_VMEXIT_PAUSE                40
/* VM-entry failure due to machine-check event */
#define VMX_VMEXIT_ENTRY_FAIL_MC        41
/* Not defined basic exit reason: 42 */
#define VMX_VMEXIT_UNDEFINED42          42
/* TPR below threshold */
#define VMX_VMEXIT_TPR_BELOW_THRESHOLD  43
/* APIC access */
#define VMX_VMEXIT_APIC_ACCESS          44
/* Virtualized EOI */
#define VMX_VMEXIT_VIRTUALIZED_EOI      45
/* Access to GDTR or IDTR */
#define VMX_VMEXIT_ACCESS_GDTR_IDTR     46
/* Access to LDTR or TR */
#define VMX_VMEXIT_ACCESS_LDTR_TR       47
/* EPT violation */
#define VMX_VMEXIT_EPT_VIOLATION        48
/* EPT misconfiguration */
#define VMX_VMEXIT_EPT_MISCONFIGURATION 49
/* INVEPT */
#define VMX_VMEXIT_INVEPT               50
/* RDTSCP */
#define VMX_VMEXIT_RDTSCP               51
/* VMX-preemption timer expired */
#define VMX_VMEXIT_PREEMPTION_TIMER     52
/* INVVPID */
#define VMX_VMEXIT_INVVPID              53
/* WBINVD or WBNOINVD */
#define VMX_VMEXIT_WBINVD               54
/* XSETBV */
#define VMX_VMEXIT_XSETBV               55
/* APIC write */
#define VMX_VMEXIT_APIC_WRITE           56
/* RDRAND */
#define VMX_VMEXIT_RDRAND               57
/* INVPCID */
#define VMX_VMEXIT_INVPCID              58
/* VMFUNC */
#define VMX_VMEXIT_VMFUNC               59
/* ENCLS */
#define VMX_VMEXIT_ENCLS                60
/* RDSEED */
#define VMX_VMEXIT_RDSEED               61
/* Page-modification log full */
#define VMX_VMEXIT_PAGE_MODIF_LOG_FULL  62
/* XSAVES */
#define VMX_VMEXIT_XSAVES               63
/* XRSTORS */
#define VMX_VMEXIT_XRSTORS              64
/* Not defined basic exit reason: 65 */
#define VMX_VMEXIT_UNDEFINED65          65
/* SPP-related event */
#define VMX_VMEXIT_SPP                  66
/* UMWAIT */
#define VMX_VMEXIT_UMWAIT               67
/* TPAUSE */
#define VMX_VMEXIT_TPAUSE               68
/* LOADIWKEY */
#define VMX_VMEXIT_LOADIWKEY            69

#define VMX_CRX_ACCESS_FROM	0x1
#define VMX_CRX_ACCESS_TO		0x0

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
enum _vmcs_encodings {
#define DECLARE_FIELD_16(encoding, name, ...) \
  VMCSENC_##name = encoding,
#define DECLARE_FIELD_64(...) DECLARE_FIELD_16(__VA_ARGS__)
#define DECLARE_FIELD_32(...) DECLARE_FIELD_16(__VA_ARGS__)
#define DECLARE_FIELD_NW(...) DECLARE_FIELD_16(__VA_ARGS__)
#include "_vmx_vmcs_fields.h"
};

struct _vmx_vmcsfields {
#define DECLARE_FIELD_16(encoding, name, ...) \
  u16 name;
#define DECLARE_FIELD_64(encoding, name, ...) \
  u64 name;
#define DECLARE_FIELD_32(encoding, name, ...) \
  u32 name;
#define DECLARE_FIELD_NW(encoding, name, ...) \
  ulong_t name;
#include "_vmx_vmcs_fields.h"
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
  __asm__ __volatile__("vmxon %0\n\t"
    : //no outputs
    : "m"(vmxonRegion)
    : "cc");
}

static inline u32 __vmx_vmwrite(unsigned long encoding, unsigned long value){
  u32 status;
  __asm__ __volatile__("vmwrite %2, %1 \r\n"
                       "jbe 1f \r\n"
                       "movl $1, %0 \r\n"
                       "jmp 2f \r\n"
                       "1: movl $0, %0 \r\n"
                       "2: \r\n"
    : "=g"(status)
    : "r"(encoding), "rm"(value)
    : "cc");
  return status;
}

static inline u32 __vmx_vmread(unsigned long encoding, unsigned long *value){
  u32 status;
  __asm__ __volatile__("vmread %2, %0 \r\n"
                       "jbe 1f \r\n"
                       "movl $1, %1 \r\n"
                       "jmp 2f \r\n"
                       "1: movl $0, %1 \r\n"
                       "2: \r\n"
    : "=rm"(*value), "=g"(status)
    : "r"(encoding)
    : "cc");
  return status;
}

static inline u32 __vmx_vmclear(u64 vmcs){
  u32 status;
  __asm__ __volatile__("vmclear %1 \r\n"
                       "jbe 1f \r\n"
                       "movl $1, %0 \r\n"
                       "jmp 2f \r\n"
                       "1: movl $0, %0 \r\n"
                       "2: \r\n"
    : "=m" (status)
    : "m"(vmcs)
    : "cc");
  return status;
}

static inline u32 __vmx_vmptrld(u64 vmcs){
  u32 status;
  __asm__ __volatile__("vmptrld %1        \r\n"
                       "jbe  1f           \r\n"
                       "movl $1, %0       \r\n"
                       "jmp  2f           \r\n"
                       "1: movl $0, %0    \r\n"
                       "2:                \r\n"
    : "=m" (status)
    : "m"(vmcs)
    : "cc");
  return status;
}

static inline u32 __vmx_vmptrst(u64 *vmcs){
  u32 status;
  __asm__ __volatile__("vmptrst %1        \r\n"
                       "jbe  1f           \r\n"
                       "movl $1, %0       \r\n"
                       "jmp  2f           \r\n"
                       "1: movl $0, %0    \r\n"
                       "2:                \r\n"
    : "=m" (status), "=m"(*vmcs)
    :
    : "cc");
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

static inline u32 __vmx_invvpid(int invalidation_type, u16 vpid, uintptr_t linearaddress){
	//return status (1 or 0)
	u32 status;

	//invvpid descriptor
	volatile struct {
		u64 vpid : 16;
		u64 reserved : 48;
		u64 linearaddress;
	} invvpiddescriptor = { vpid, 0, linearaddress };

	//issue invvpid instruction
	//note: GCC does not seem to support this instruction directly
	//so we encode it as hex
	__asm__ __volatile__(".byte 0x66, 0x0f, 0x38, 0x81, 0x08 \r\n"
	                     "movl $1, %0 \r\n"
	                     "ja 1f \r\n"
	                     "movl $0, %0 \r\n"
	                     "1: \r\n"
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
	volatile struct {
		u64 eptp;
		u64 reserved;
	} inveptdescriptor = { eptp, 0};

	//issue invept instruction
	//note: GCC does not seem to support this instruction directly
	//so we encode it as hex
	__asm__ __volatile__(".byte 0x66, 0x0f, 0x38, 0x80, 0x08 \r\n"
	                     "movl $1, %0 \r\n"
	                     "ja 1f \r\n"
	                     "movl $0, %0 \r\n"
	                     "1: \r\n"
	  : "=m" (status)
	  : "a"(&inveptdescriptor), "c"(invalidation_type)
	  : "cc", "memory");

	return status;
}




#endif
