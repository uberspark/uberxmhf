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

//XMHF HWM CPU declarations
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHFHWM_CPU_H__
#define __XMHFHWM_CPU_H__

//////
// general
//////

#define CPU_VENDOR_INTEL 	0xAB
#define CPU_VENDOR_AMD 		0xCD
#define CPU_VENDOR_UNKNOWN	0xDE

#define AMD_STRING_DWORD1 0x68747541
#define AMD_STRING_DWORD2 0x69746E65
#define AMD_STRING_DWORD3 0x444D4163

#define INTEL_STRING_DWORD1	0x756E6547
#define INTEL_STRING_DWORD2	0x49656E69
#define INTEL_STRING_DWORD3	0x6C65746E

#define EFLAGS_CF	0x00000001 /* Carry Flag */
#define EFLAGS_PF	0x00000004 /* Parity Flag */
#define EFLAGS_AF	0x00000010 /* Auxillary carry Flag */
#define EFLAGS_ZF	0x00000040 /* Zero Flag */
#define EFLAGS_SF	0x00000080 /* Sign Flag */
#define EFLAGS_TF	0x00000100 /* Trap Flag */
#define EFLAGS_IF	0x00000200 /* Interrupt Flag */
#define EFLAGS_DF	0x00000400 /* Direction Flag */
#define EFLAGS_OF	0x00000800 /* Overflow Flag */
#define EFLAGS_IOPL	0x00003000 /* IOPL mask */
#define EFLAGS_NT	0x00004000 /* Nested Task */
#define EFLAGS_RF	0x00010000 /* Resume Flag */
#define EFLAGS_VM	0x00020000 /* Virtual Mode */
#define EFLAGS_AC	0x00040000 /* Alignment Check */
#define EFLAGS_VIF	0x00080000 /* Virtual Interrupt Flag */
#define EFLAGS_VIP	0x00100000 /* Virtual Interrupt Pending */
#define EFLAGS_ID	0x00200000 /* CPUID detection flag */

#define CR0_PE              0x00000001 /* Enable Protected Mode    (RW) */
#define CR0_MP              0x00000002 /* Monitor Coprocessor      (RW) */
#define CR0_EM              0x00000004 /* Require FPU Emulation    (RO) */
#define CR0_TS              0x00000008 /* Task Switched            (RW) */
#define CR0_ET              0x00000010 /* Extension type           (RO) */
#define CR0_NE              0x00000020 /* Numeric Error Reporting  (RW) */
#define CR0_WP              0x00010000 /* Supervisor Write Protect (RW) */
#define CR0_AM              0x00040000 /* Alignment Checking       (RW) */
#define CR0_NW              0x20000000 /* Not Write-Through        (RW) */
#define CR0_CD              0x40000000 /* Cache Disable            (RW) */
#define CR0_PG              0x80000000 /* Paging                   (RW) */

#define CR4_VME		0x0001	/* enable vm86 extensions */
#define CR4_PVI		0x0002	/* virtual interrupts flag enable */
#define CR4_TSD		0x0004	/* disable time stamp at ipl 3 */
#define CR4_DE		0x0008	/* enable debugging extensions */
#define CR4_PSE		0x0010	/* enable page size extensions */
#define CR4_PAE		0x0020	/* enable physical address extensions */
#define CR4_MCE		0x0040	/* Machine check enable */
#define CR4_PGE		0x0080	/* enable global pages */
#define CR4_PCE		0x0100	/* enable performance counters at ipl 3 */
#define CR4_OSFXSR		0x0200	/* enable fast FPU save and restore */
#define CR4_OSXMMEXCPT	0x0400	/* enable unmasked SSE exceptions */
#define CR4_VMXE		0x2000  /* enable VMX */
#define CR4_SMXE		0x4000  /* enable SMX */
#define CR4_OSXSAVE	(1UL << 18)	// XSAVE and Processor Extended States Enable bit
#define CR4_PCIDE   (1UL << 17) // process context identifiers

//CPUID related
#define EDX_PAE 6
#define EDX_NX 20
#define ECX_SVM 2
#define EDX_NP 0

#define SVM_CPUID_FEATURE       (1 << 2)

#define CPUID_X86_FEATURE_VMX    (1<<5)
#define CPUID_X86_FEATURE_SMX    (1<<6)

//CPU exception numbers
//(intel SDM vol 3a 6-27)
#define	CPU_EXCEPTION_DE				0			//divide error exception
#define CPU_EXCEPTION_DB				1			//debug exception
#define	CPU_EXCEPTION_NMI				2			//non-maskable interrupt
#define	CPU_EXCEPTION_BP				3			//breakpoint exception
#define	CPU_EXCEPTION_OF				4			//overflow exception
#define	CPU_EXCEPTION_BR				5			//bound-range exceeded
#define	CPU_EXCEPTION_UD				6			//invalid opcode
#define	CPU_EXCEPTION_NM				7			//device not available
#define	CPU_EXCEPTION_DF				8			//double fault exception (code)
#define	CPU_EXCEPTION_RESV9				9			//reserved
#define	CPU_EXCEPTION_TS				10			//invalid TSS (code)
#define	CPU_EXCEPTION_NP				11			//segment not present (code)
#define	CPU_EXCEPTION_SS				12			//stack fault (code)
#define	CPU_EXCEPTION_GP				13			//general protection (code)
#define CPU_EXCEPTION_PF				14			//page fault (code)
#define	CPU_EXCEPTION_RESV15			15			//reserved
#define CPU_EXCEPTION_MF				16			//floating-point exception
#define CPU_EXCEPTION_AC				17			//alignment check (code)
#define CPU_EXCEPTION_MC				18			//machine check
#define CPU_EXCEPTION_XM				19			//SIMD floating point exception


//extended control registers
#define XCR_XFEATURE_ENABLED_MASK       0x00000000


#ifndef __ASSEMBLY__

//x86 GPR set definition (follows the order enforced by PUSHAD/POPAD
//SDM Vol 2B. 4-427)

struct regs
{
  u64 edi;
  u64 esi;
  u64 ebp;
  u64 esp;
  u64 ebx;
  u64 edx;
  u64 ecx;
  u64 eax;
}__attribute__ ((packed));

typedef struct
{
  u32 edi;
  u32 esi;
  u32 ebp;
  u32 esp;
  u32 ebx;
  u32 edx;
  u32 ecx;
  u32 eax;
}__attribute__ ((packed)) x86regs_t;

typedef struct {
  u64 r8;
  u64 r9;
  u64 r10;
  u64 r11;
  u64 r12;
  u64 r13;
  u64 r14;
  u64 r15;
  u64 rax;
  u64 rbx;
  u64 rcx;
  u64 rdx;
  u64 rsi;
  u64 rdi;
  u64 rbp;
  u64 rsp;
}__attribute__ ((packed)) x86regs64_t;


typedef struct {
    u64 rip;
    u64 cs;
    u64 rflags;
    u64 rsp;
    u64 ss;
}__attribute__ ((packed)) x86idt64_stackframe_t;


typedef struct {
  u16 isrLow;
  u16 isrSelector;
  u8  count;
  u8  type;
  u16 isrHigh;
} __attribute__ ((packed)) idtentry_t;


typedef struct {
  u16 limit0_15;
  u16 baseAddr0_15;
  u8 baseAddr16_23;
  u8 attributes1;
  u8 limit16_19attributes2;
  u8 baseAddr24_31;
} __attribute__ ((packed)) TSSENTRY;


typedef struct {
	u32 selector;
	u32 base;
	u32 limit;
	u32 access_rights;
} x86desc_t;


typedef struct {
  u32 eip;
  u32 cs;
  u32 eflags;
} __attribute__((packed)) INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE;

typedef struct {
  u32 errorcode;
  u32 eip;
  u32 cs;
  u32 eflags;
} __attribute__((packed)) INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE;


typedef struct {
    u32 edi;
    u32 esi;
    u32 ebp;
    u32 esp;
    u32 ebx;
    u32 edx;
    u32 ecx;
    u32 eax;
    u32 vector;
    u32 error_code;
    u32 orig_rip;
    u32 orig_cs;
    u32 orig_rflags;
    u32 orig_rsp;
    u32 orig_ss;
} __attribute__((packed)) x86vmx_exception_frame_t;


typedef struct {
    u64 r8;
    u64 r9;
    u64 r10;
    u64 r11;
    u64 r12;
    u64 r13;
    u64 r14;
    u64 r15;
    u64 rax;
    u64 rbx;
    u64 rcx;
    u64 rdx;
    u64 rsi;
    u64 rdi;
    u64 rbp;
    u64 rsp;
    u64 vector;
    u64 errorcode;
    u64 orig_rip;
    u64 orig_cs;
    u64 orig_rflags;
    u64 orig_rsp;
    u64 orig_ss;
} __attribute__((packed)) x86vmx_exception_frame_errcode_t;


//x86 GDT descriptor type
typedef struct {
		u16 size;
		u32 base;
} __attribute__((packed)) arch_x86_gdtdesc_t;

//x86 IDT descriptor type
typedef struct {
		u16 size;
		u32 base;
} __attribute__((packed)) arch_x86_idtdesc_t;

//TSS descriptor (partial)
typedef struct __tss {
	u32 reserved;
	u32 esp0;
	u32 ss0;
	u32 esp1;
	u32 ss1;
	u32 esp2;
	u32 ss2;
	u32 cr3;
	u32 eip;
	u32 eflags;
	u32 eax;
	u32 ecx;
	u32 edx;
	u32 ebx;
	u32 esp;
	u32 ebp;
	u32 esi;
	u32 edi;
	u32 es;
	u32 cs;
	u32 ss;
	u32 ds;
	u32 fs;
	u32 gs;
	u32 ldt_sel;
	u16 t_bit;
	u16 iotbl_addr;
} __attribute__((packed)) tss_t;


#endif //__ASSEMBLY__






//////
// model-specific registers
//////

#define MSR_EFER 0xc0000080     // prevent write to efer.sce
#define MSR_K6_STAR                     0xc0000081
#define VM_CR_MSR 0xc0010114
#define VM_HSAVE_PA 0xc0010117  //this is critical
#define IGNNE 0xc0010115        //can be used to freeze/restart
#define SMM_CTL 0xc0010116      //SMRAM control

#define MSR_IA32_PAT	0x277	//Page Attribute Table MSR

#define MSR_AMD64_PATCH_LEVEL 0x0000008b //AMD-specific microcode patch level MSR
#define MSR_AMD64_PATCH_CLEAR 0xc0010021 //AMD-specific microcode patch clear

#define MSR_APIC_BASE 0x0000001B

// EFER bits
#define EFER_SCE 0  /* SYSCALL/SYSRET */
#define EFER_LME 8  /* Long Mode enable */
#define EFER_LMA 10 /* Long Mode Active (read-only) */
#define EFER_NXE 11  /* no execute */
#define EFER_SVME 12   /* SVM extensions enable */

// VM CR MSR bits
#define VM_CR_DPD 0
#define VM_CR_R_INIT 1
#define VM_CR_DIS_A20M 2
#define VM_CR_SVME_DISABLE 4


// debug and last branch record MSRs
#define MSR_LBR_SELECT		0x1C8

#define MSR_LASTBRANCH_TOS	0x1C9

#define MSR_IA32_DEBUGCTL	0x1D9

#define MSR_LASTBRANCH_0_FROM_IP	0x680
#define MSR_LASTBRANCH_1_FROM_IP	0x681
#define MSR_LASTBRANCH_2_FROM_IP	0x682
#define MSR_LASTBRANCH_3_FROM_IP	0x683
#define MSR_LASTBRANCH_4_FROM_IP	0x684
#define MSR_LASTBRANCH_5_FROM_IP	0x685
#define MSR_LASTBRANCH_6_FROM_IP	0x686
#define MSR_LASTBRANCH_7_FROM_IP	0x687
#define MSR_LASTBRANCH_8_FROM_IP	0x688
#define MSR_LASTBRANCH_9_FROM_IP	0x689
#define MSR_LASTBRANCH_10_FROM_IP	0x68a
#define MSR_LASTBRANCH_11_FROM_IP	0x68b
#define MSR_LASTBRANCH_12_FROM_IP	0x68c
#define MSR_LASTBRANCH_13_FROM_IP	0x68d
#define MSR_LASTBRANCH_14_FROM_IP	0x68e
#define MSR_LASTBRANCH_15_FROM_IP	0x68f


#define MSR_LASTBRANCH_0_TO_IP	0x6c0
#define MSR_LASTBRANCH_1_TO_IP	0x6c1
#define MSR_LASTBRANCH_2_TO_IP	0x6c2
#define MSR_LASTBRANCH_3_TO_IP	0x6c3
#define MSR_LASTBRANCH_4_TO_IP	0x6c4
#define MSR_LASTBRANCH_5_TO_IP	0x6c5
#define MSR_LASTBRANCH_6_TO_IP	0x6c6
#define MSR_LASTBRANCH_7_TO_IP	0x6c7
#define MSR_LASTBRANCH_8_TO_IP	0x6c8
#define MSR_LASTBRANCH_9_TO_IP	0x6c9
#define MSR_LASTBRANCH_10_TO_IP	0x6ca
#define MSR_LASTBRANCH_11_TO_IP	0x6cb
#define MSR_LASTBRANCH_12_TO_IP	0x6cc
#define MSR_LASTBRANCH_13_TO_IP	0x6cd
#define MSR_LASTBRANCH_14_TO_IP	0x6ce
#define MSR_LASTBRANCH_15_TO_IP	0x6cf



// VMX capabilities MSR
#define IA32_VMX_BASIC_MSR            0x480
#define IA32_VMX_PINBASED_CTLS_MSR    0x481
#define IA32_VMX_PROCBASED_CTLS_MSR   0x482
#define IA32_VMX_EXIT_CTLS_MSR        0x483
#define IA32_VMX_ENTRY_CTLS_MSR       0x484
#define IA32_VMX_MISC_MSR       	    0x485
#define IA32_VMX_CR0_FIXED0_MSR       0x486
#define IA32_VMX_CR0_FIXED1_MSR       0x487
#define IA32_VMX_CR4_FIXED0_MSR       0x488
#define IA32_VMX_CR4_FIXED1_MSR       0x489
#define IA32_VMX_VMCS_ENUM_MSR        0x48A
#define IA32_VMX_PROCBASED_CTLS2_MSR  0x48B

//sysenter/sysexit MSRs
#define IA32_SYSENTER_CS_MSR	         0x174
#define IA32_SYSENTER_EIP_MSR	         0x176
#define IA32_SYSENTER_ESP_MSR	         0x175

//syscall/sysret MSRs
#define IA32_LSTAR_MSR                  0xC0000082
#define IA32_FMASK_MSR                  0xC0000084
#define IA32_STAR_MSR                   0xC0000081


//only for 64-bit LM
#define IA32_MSR_FS_BASE               0xC0000100
#define IA32_MSR_GS_BASE               0xC0000101

#define MSR_EFCR   0x0000003A	        // index for Extended Feature Control

//#define MSR_IA32_FEATURE_CONTROL               0x03a tboot version trumped by our own
#define IA32_FEATURE_CONTROL_MSR_LOCK                 0x1
#define IA32_FEATURE_CONTROL_MSR_ENABLE_VMX_IN_SMX    0x2
#define IA32_FEATURE_CONTROL_MSR_SENTER_PARAM_CTL     0x7f00
#define IA32_FEATURE_CONTROL_MSR_ENABLE_SENTER        0x8000


//MTRRs
#define	IA32_MTRRCAP	0x000000fe
#define IA32_MTRR_DEF_TYPE 	0x000002ff

//fixed range MTRRs
#define IA32_MTRR_FIX64K_00000	0x00000250	//64-bits, 8 ranges (8bits/range) from 00000-7FFFF
#define IA32_MTRR_FIX16K_80000	0x00000258	//64-bits, 8 ranges (8bits/range) from 80000-9FFFF
#define IA32_MTRR_FIX16K_A0000	0x00000259	//64-bits, 8 ranges (8bits/range) from A0000-BFFFF
#define IA32_MTRR_FIX4K_C0000		0x00000268	//64-bits, 8 ranges (8bits/range) from C0000-C7FFF
#define IA32_MTRR_FIX4K_C8000		0x00000269	//64-bits, 8 ranges (8bits/range) from C8000-CFFFF
#define IA32_MTRR_FIX4K_D0000		0x0000026a	//64-bits, 8 ranges (8bits/range) from D0000-D7FFF
#define IA32_MTRR_FIX4K_D8000		0x0000026b	//64-bits, 8 ranges (8bits/range) from D8000-DFFFF
#define IA32_MTRR_FIX4K_E0000		0x0000026c	//64-bits, 8 ranges (8bits/range) from E0000-E7FFF
#define IA32_MTRR_FIX4K_E8000		0x0000026d	//64-bits, 8 ranges (8bits/range) from E8000-EFFFF
#define IA32_MTRR_FIX4K_F0000		0x0000026e	//64-bits, 8 ranges (8bits/range) from F0000-F7FFF
#define IA32_MTRR_FIX4K_F8000		0x0000026f	//64-bits, 8 ranges (8bits/range) from F8000-FFFFF

//variable range MTRRs
#define IA32_MTRR_PHYSBASE0			0x00000200
#define IA32_MTRR_PHYSMASK0			0x00000201
#define IA32_MTRR_PHYSBASE1			0x00000202
#define IA32_MTRR_PHYSMASK1			0x00000203
#define IA32_MTRR_PHYSBASE2			0x00000204
#define IA32_MTRR_PHYSMASK2			0x00000205
#define IA32_MTRR_PHYSBASE3			0x00000206
#define IA32_MTRR_PHYSMASK3			0x00000207
#define IA32_MTRR_PHYSBASE4			0x00000208
#define IA32_MTRR_PHYSMASK4			0x00000209
#define IA32_MTRR_PHYSBASE5			0x0000020a
#define IA32_MTRR_PHYSMASK5			0x0000020b
#define IA32_MTRR_PHYSBASE6			0x0000020c
#define IA32_MTRR_PHYSMASK6			0x0000020d
#define IA32_MTRR_PHYSBASE7			0x0000020e
#define IA32_MTRR_PHYSMASK7			0x0000020f

#define MTRR_TYPE_UC   0x0
#define MTRR_TYPE_WC   0x1
#define MTRR_TYPE_WT   0x4
#define MTRR_TYPE_WP   0x5
#define MTRR_TYPE_WB   0x6
#define MTRR_TYPE_RESV  0x7


/* current procs only have 8, so this should hold us for a while */
#define MAX_VARIABLE_MTRRS      16

#define MAX_MEMORYTYPE_ENTRIES    98    //8*11 fixed MTRRs and 10 variable MTRRs
#define MAX_FIXED_MEMORYTYPE_ENTRIES  88
#define MAX_VARIABLE_MEMORYTYPE_ENTRIES 10

//total number of FIXED and VARIABLE MTRRs on current x86 platforms
#define NUM_MTRR_MSRS		31


#ifndef __ASSEMBLY__

enum fix_mtrr_t {
    MTRR_FIX64K_00000 = 0x250,
    MTRR_FIX16K_80000 = 0x258,
    MTRR_FIX16K_A0000 = 0x259,
    MTRR_FIX4K_C0000  = 0x268,
    MTRR_FIX4K_C8000  = 0x269,
    MTRR_FIX4K_D0000  = 0x26A,
    MTRR_FIX4K_D8000  = 0x26B,
    MTRR_FIX4K_E0000  = 0x26C,
    MTRR_FIX4K_E8000  = 0x26D,
    MTRR_FIX4K_F0000  = 0x26E,
    MTRR_FIX4K_F8000  = 0x26F
};

typedef union {
    uint64_t raw;
    uint8_t  type[8];
} __attribute__((packed)) mtrr_fix_types_t;

enum var_mtrr_t {
    MTRR_PHYS_BASE0_MSR = 0x200,
    MTRR_PHYS_MASK0_MSR = 0x201,
    MTRR_PHYS_BASE1_MSR = 0x202,
    MTRR_PHYS_MASK1_MSR = 0x203,
    MTRR_PHYS_BASE2_MSR = 0x204,
    MTRR_PHYS_MASK2_MSR = 0x205,
    MTRR_PHYS_BASE3_MSR = 0x206,
    MTRR_PHYS_MASK3_MSR = 0x207,
    MTRR_PHYS_BASE4_MSR = 0x208,
    MTRR_PHYS_MASK4_MSR = 0x209,
    MTRR_PHYS_BASE5_MSR = 0x20A,
    MTRR_PHYS_MASK5_MSR = 0x20B,
    MTRR_PHYS_BASE6_MSR = 0x20C,
    MTRR_PHYS_MASK6_MSR = 0x20D,
    MTRR_PHYS_BASE7_MSR = 0x20E,
    MTRR_PHYS_MASK7_MSR = 0x20F
};


typedef struct {
    u32 vcnt        ; //: 8;    // num variable MTRR pairs
    u32 fix         ; //: 1;    // fixed range MTRRs are supported
    u32 reserved1   ; //: 1;
    u32 wc          ; //: 1;    // write-combining mem type supported
    u32 reserved2   ; //: 32;
    u32 reserved3   ; //: 21;
} __attribute__((packed)) mtrr_cap_t;

#define pack_mtrr_cap_t(s) \
    (u64)( \
    (((u64)(s)->reserved3 & 0x00000000001FFFFFULL) << 43) | \
    (((u64)(s)->reserved2 & 0x00000000FFFFFFFFULL) << 11) | \
    (((u64)(s)->wc & 0x0000000000000001ULL) << 10) | \
    (((u64)(s)->reserved1 & 0x0000000000000001ULL) << 9) | \
    (((u64)(s)->fix & 0x0000000000000001ULL) << 8) | \
    (((u64)(s)->vcnt & 0x00000000000000FFULL) << 0) \
    )

#define unpack_mtrr_cap_t(s, value) \
    (s)->reserved3 = (u32)(((u64)value >> 43) & 0x00000000001FFFFFULL); \
    (s)->reserved2 = (u32)(((u64)value >> 11) & 0x00000000FFFFFFFFULL); \
    (s)->wc = (u32)(((u64)value >> 10) & 0x0000000000000001ULL); \
    (s)->reserved1 = (u32)(((u64)value >> 9) & 0x0000000000000001ULL); \
    (s)->fix = (u32)(((u64)value >> 8) & 0x0000000000000001ULL); \
    (s)->vcnt = (u32)(((u64)value >> 0) & 0x00000000000000FFULL);


typedef struct {
    u32 type        ; //: 8;
    u32 reserved1   ; //: 2;
    u32 fe          ; //: 1;    // fixed MTRR enable
    u32 e           ; //: 1;    // (all) MTRR enable
    u32 reserved2   ; //: 32;
    u32 reserved3   ; //: 20;
} __attribute__((packed)) mtrr_def_type_t;

#define pack_mtrr_def_type_t(s) \
    (u64)( \
    (((u64)(s)->reserved3 & 0x00000000000FFFFFULL) << 44) | \
    (((u64)(s)->reserved2 & 0x00000000FFFFFFFFULL) << 12) | \
    (((u64)(s)->e & 0x0000000000000001ULL) << 11) | \
    (((u64)(s)->fe & 0x0000000000000001ULL) << 10) | \
    (((u64)(s)->reserved1 & 0x0000000000000003ULL) << 8) | \
    (((u64)(s)->type & 0x00000000000000FFULL) << 0) \
    )

#define unpack_mtrr_def_type_t(s, value) \
    (s)->reserved3 = (u32)(((u64)value >> 44) & 0x00000000000FFFFFULL); \
    (s)->reserved2 = (u32)(((u64)value >> 12) & 0x00000000FFFFFFFFULL); \
    (s)->e = (u32)(((u64)value >> 11) & 0x0000000000000001ULL); \
    (s)->fe = (u32)(((u64)value >> 10) & 0x0000000000000001ULL); \
    (s)->reserved1 = (u32)(((u64)value >> 8) & 0x0000000000000003ULL); \
    (s)->type = (u32)(((u64)value >> 0) & 0x00000000000000FFULL);


typedef struct {
    u32 type      ; //: 8;
    u32 reserved1 ; //: 4;
    // TBD: the end of base really depends on MAXPHYADDR, but since
    // the MTRRs are set for SINIT and it must be <4GB, can use 24b
    u32 base      ; //: 24;
    u32 reserved2 ; //: 28;
} __attribute__((packed)) mtrr_physbase_t;

#define pack_mtrr_physbase_t(s) \
    (u64)( \
    (((u64)(s)->reserved2 & 0x000000000FFFFFFFULL) << 36) | \
    (((u64)(s)->base & 0x0000000000FFFFFFULL) << 12) | \
    (((u64)(s)->reserved1 & 0x000000000000000FULL) << 8) | \
    (((u64)(s)->type & 0x00000000000000FFULL) << 0) \
    )

#define unpack_mtrr_physbase_t(s, value) \
    (s)->reserved2 = (u32)(((u64)value >> 36) & 0x000000000FFFFFFFULL); \
    (s)->base = (u32)(((u64)value >> 12) & 0x0000000000FFFFFFULL); \
    (s)->reserved1 = (u32)(((u64)value >> 8) & 0x000000000000000FULL); \
    (s)->type = (u32)(((u64)value >> 0) & 0x00000000000000FFULL);


typedef struct {
    u32 reserved1 ; //: 11;
    u32 v         ; //: 1;      // valid
    // TBD: the end of mask really depends on MAXPHYADDR, but since
    // the MTRRs are set for SINIT and it must be <4GB, can use 24b
    u32 mask      ; //: 24;
    u32 reserved2 ; //: 28;
} __attribute__((packed)) mtrr_physmask_t;

#define pack_mtrr_physmask_t(s) \
    (u64)( \
    (((u64)(s)->reserved2 & 0x000000000FFFFFFFULL) << 36) | \
    (((u64)(s)->mask & 0x0000000000FFFFFFULL) << 12) | \
    (((u64)(s)->v & 0x0000000000000001ULL) << 11) | \
    (((u64)(s)->reserved1 & 0x00000000000007FFULL) << 0) \
    )

#define unpack_mtrr_physmask_t(s, value) \
    (s)->reserved2 = (u32)(((u64)value >> 36) & 0x000000000FFFFFFFULL); \
    (s)->mask = (u32)(((u64)value >> 12) & 0x0000000000FFFFFFULL); \
    (s)->v = (u32)(((u64)value >> 11) & 0x0000000000000001ULL); \
    (s)->reserved1 = (u32)(((u64)value >> 0) & 0x00000000000007FFULL);


#endif //__ASSEMBLY__


/*
 * from: @(#)specialreg.h     7.1 (Berkeley) 5/9/91
 * $FreeBSD: src/sys/i386/include/specialreg.h,v 1.53.2.1.2.2 2009/11/06 17:09:04 attilio Exp $
 */

#define MSR_APICBASE                           0x01b
#define MSR_IA32_FEATURE_CONTROL               0x03a
#define MSR_IA32_SMM_MONITOR_CTL               0x09b
#define MSR_MTRRcap                            0x0fe
#define MSR_MCG_CAP                            0x179
#define MSR_MCG_STATUS                         0x17a
#define MSR_IA32_MISC_ENABLE                   0x1a0
#define MSR_MTRRdefType                        0x2ff
#define MSR_MC0_STATUS                         0x401
#define MSR_IA32_VMX_BASIC_MSR                 0x480
#define MSR_IA32_VMX_PINBASED_CTLS_MSR         0x481
#define MSR_IA32_VMX_PROCBASED_CTLS_MSR        0x482
#define MSR_IA32_VMX_EXIT_CTLS_MSR             0x483
#define MSR_IA32_VMX_ENTRY_CTLS_MSR            0x484

/*
 * Constants related to MSR's.
 */
#define APICBASE_BSP                                  0x00000100
#define MSR_IA32_APICBASE_ENABLE                      (1<<11)

#define MSR_IA32_SMM_MONITOR_CTL_VALID                1
#define MSR_IA32_SMM_MONITOR_CTL_MSEG_BASE(x)         (x>>12)

/* MSRs & bits used for VMX enabling */
#define IA32_FEATURE_CONTROL_MSR_LOCK                 0x1
#define IA32_FEATURE_CONTROL_MSR_ENABLE_VMX_IN_SMX    0x2
#define IA32_FEATURE_CONTROL_MSR_SENTER_PARAM_CTL     0x7f00
#define IA32_FEATURE_CONTROL_MSR_ENABLE_SENTER        0x8000

/* AMD64 MSR's */
#define MSR_EFER        0xc0000080      /* extended features */

/* EFER bits */
#define _EFER_LME     8               /* Long mode enable */

#define MTRR_TYPE_UNCACHABLE     0
#define MTRR_TYPE_WRTHROUGH      4
#define MTRR_TYPE_WRBACK         6






//////
// MMU/paging
//////

//physical memory limit
#ifndef __ASSEMBLY__
#define ADDR_4GB 0x100000000ULL
#else
#define ADDR_4GB 0x100000000
#endif

// page sizes
#ifndef __ASSEMBLY__
#define PAGE_SIZE_4K (1UL << 12)
#define PAGE_SIZE_2M (1UL << 21)
#define PAGE_SIZE_4M (1UL << 22)
#else
#define PAGE_SIZE_4K (1 << 12)
#define PAGE_SIZE_2M (1 << 21)
#define PAGE_SIZE_4M (1 << 22)
#endif

#define PAGE_SHIFT_4K 12
#define PAGE_SHIFT_2M 21
#define PAGE_SHIFT_4M 22

#define PAGE_ALIGN_UP4K(size)	(((size) + PAGE_SIZE_4K - 1) & ~(PAGE_SIZE_4K - 1))
#define PAGE_ALIGN_UP2M(size)	(((size) + PAGE_SIZE_2M - 1) & ~(PAGE_SIZE_2M - 1))
#define PAGE_ALIGN_UP4M(size)	(((size) + PAGE_SIZE_4M - 1) & ~(PAGE_SIZE_4M - 1))

#define PAGE_ALIGN_4K(size)	((size) & ~(PAGE_SIZE_4K - 1))
#define PAGE_ALIGN_2M(size)	((size) & ~(PAGE_SIZE_2M - 1))
#define PAGE_ALIGN_4M(size)	((size) & ~(PAGE_SIZE_4M - 1))

#define PAGE_ALIGNED_4K(size) (PAGE_ALIGN_4K(size) == size)
#define PAGE_ALIGNED_2M(size) (PAGE_ALIGN_2M(size) == size)
#define PAGE_ALIGNED_4M(size) (PAGE_ALIGN_4M(size) == size)

// non-PAE mode specific definitions
#define NPAE_PTRS_PER_PDT       1024
#define NPAE_PTRS_PER_PT        1024
#define NPAE_PAGETABLE_SHIFT    12
#define NPAE_PAGEDIR_SHIFT      22
#define NPAE_PAGE_DIR_MASK      0xffc00000
#define NPAE_PAGE_TABLE_MASK    0x003ff000

// PAE mode specific definitions
#define PAE_PTRS_PER_PML4T       1
#define PAE_MAXPTRS_PER_PML4T    512

#define PAE_PTRS_PER_PDPT  4
#define PAE_MAXPTRS_PER_PDPT  512

#define PAE_PTRS_PER_PDT   512
#define PAE_PTRS_PER_PT    512

#define PAE_PT_SHIFT       12
#define PAE_PDT_SHIFT      21
#define PAE_PDPT_SHIFT     30
#define PAE_PML4T_SHIFT    39


#define PAE_PT_MASK        0x00000000001ff000ULL
#define PAE_PDT_MASK       0x000000003fe00000ULL
#define PAE_PDPT_MASK      0x0000007fc0000000ULL
#define PAE_PMl4T_MASK     0x0000ff8000000000ULL


#define PAE_ENTRY_SIZE     8

// various paging flags
#define _PAGE_BIT_PRESENT	0
#define _PAGE_BIT_RW		1
#define _PAGE_BIT_USER		2
#define _PAGE_BIT_PWT		3
#define _PAGE_BIT_PCD		4
#define _PAGE_BIT_ACCESSED	5
#define _PAGE_BIT_DIRTY		6
#define _PAGE_BIT_PSE		7
#define _PAGE_BIT_GLOBAL	8
#define _PAGE_BIT_UNUSED1	9
#define _PAGE_BIT_UNUSED2	10
#define _PAGE_BIT_UNUSED3	11
#define _PAGE_BIT_NX		63

#define _PAGE_PRESENT	0x001
#define _PAGE_RW	0x002
#define _PAGE_USER	0x004
#define _PAGE_PWT	0x008
#define _PAGE_PCD	0x010
#define _PAGE_ACCESSED	0x020
#define _PAGE_DIRTY	0x040
#define _PAGE_PSE	0x080
#define _PAGE_GLOBAL	0x100
#define _PAGE_UNUSED1	0x200
#define _PAGE_UNUSED2	0x400
#define _PAGE_UNUSED3	0x800

#ifndef __ASSEMBLY__
#define _PAGE_NX	(1ULL<<_PAGE_BIT_NX)
#else
#define _PAGE_NX  (1 << _PAGE_BIT_NX)
#endif

#define PAGE_FAULT_BITS (_PAGE_PRESENT | _PAGE_RW | _PAGE_USER | _PAGE_NX)

#ifndef __ASSEMBLY__

typedef u64 pml4te_t;
typedef u64 pdpte_t;
typedef u64 pdte_t;
typedef u64 pte_t;

typedef pml4te_t *pml4t_t;
typedef pdpte_t *pdpt_t;
typedef pdte_t *pdt_t;
typedef pte_t *pt_t;

typedef u32 *npdt_t;
typedef u32 *npt_t;

/* make a pml4 entry from individual fields */
#define pae_make_pml4e(paddr, flags) \
  ((u64)(paddr) & (~(((u64)PAGE_SIZE_4K - 1) | _PAGE_NX))) | (u64)(flags)

/* make a page directory pointer entry from individual fields */
//#define pae_make_pdpe(paddr, flags) \
//  ((u64)(paddr) & (~(((u64)PAGE_SIZE_4K - 1) | _PAGE_NX))) | (u64)(flags)

#define pae_make_pdpe(paddr, flags) \
  ((u64)(paddr) & (0x7FFFFFFFFFFFF000ULL)) | (u64)(flags)


/* make a page directory entry for a 2MB page from individual fields */
//#define pae_make_pde_big(paddr, flags) \
//  ((u64)(paddr) & (~(((u64)PAGE_SIZE_2M - 1) | _PAGE_NX))) | (u64)(flags)

#define pae_make_pde_big(paddr, flags) \
  ((u64)(paddr) & (0x7FFFFFFFFFE00000ULL)) | (u64)(flags)


/* make a page directory entry for a 4KB page from individual fields */
//#define pae_make_pde(paddr, flags) \
//  ((u64)(paddr) & (~(((u64)PAGE_SIZE_4K - 1) | _PAGE_NX))) | (u64)(flags)

#define pae_make_pde(paddr, flags) \
  ((u64)(paddr) & (0x7FFFFFFFFFFFF000ULL)) | (u64)(flags)


/* make a page table entry from individual fields */
//#define pae_make_pte(paddr, flags) \
//  ((u64)(paddr) & (~(((u64)PAGE_SIZE_4K - 1) | _PAGE_NX))) | (u64)(flags)

#define pae_make_pte(paddr, flags) \
  ((u64)(paddr) & (0x7FFFFFFFFFFFF000ULL)) | (u64)(flags)


/* get address field from 32-bit cr3 (page directory pointer) in PAE mode */
#define pae_get_addr_from_32bit_cr3(entry) \
  ((u32)(entry) & (~((1UL << 5) - 1)))

/* get flags field from 32-bit cr3 (page directory pointer) in PAE mode */
#define pae_get_flags_from_32bit_cr3(entry) \
  ((u32)(entry) & ((1UL << 5) - 1))

/* get address field of a pdpe (page directory pointer entry) */
#define pae_get_addr_from_pdpe(entry) \
  ((u64)(entry) & (~(((u64)PAGE_SIZE_4K - 1) | _PAGE_NX)))

/* get flags field of a pdpe (page directory pointer entry) */
#define pae_get_flags_from_pdpe(entry) \
  ((u64)(entry) & (((u64)PAGE_SIZE_4K - 1) | _PAGE_NX))

/* get address field of a 2MB pdte (page directory entry) */
#define pae_get_addr_from_pde_big(entry) \
  ((u64)(entry) & (~(((u64)PAGE_SIZE_2M - 1) | _PAGE_NX)))

/* get flags field of a 2MB pdte (page directory entry) */
#define pae_get_flags_from_pde_big(entry) \
  ((u64)(entry) & (((u64)PAGE_SIZE_2M - 1) | _PAGE_NX))

/* get address field of a 4K pdte (page directory entry) */
#define pae_get_addr_from_pde(entry) \
  ((u64)(entry) & (~(((u64)PAGE_SIZE_4K - 1) | _PAGE_NX)))

/* get flags field of a 4K pdte (page directory entry) */
#define pae_get_flags_from_pde(entry) \
  ((u64)(entry) & (((u64)PAGE_SIZE_4K - 1) | _PAGE_NX))

/* get address field of a pte (page table entry) */
#define pae_get_addr_from_pte(entry) \
  ((u64)(entry) & (~(((u64)PAGE_SIZE_4K - 1) | _PAGE_NX)))

/* get flags field of a pte (page table entry) */
#define pae_get_flags_from_pte(entry) \
  ((u64)(entry) & (((u64)PAGE_SIZE_4K - 1) | _PAGE_NX))

/* make a page directory entry for a 4MB page from individual fields */
#define npae_make_pde_big(paddr, flags) \
  ((u32)(paddr) & (~(((u32)PAGE_SIZE_4M - 1)))) | (u32)(flags)

/* make a page directory entry for a 4KB page from individual fields */
#define npae_make_pde(paddr, flags) \
  ((u32)(paddr) & (~(((u32)PAGE_SIZE_4K - 1)))) | (u32)(flags)

/* get address field from NON-PAE cr3 (page directory pointer) */
#define npae_get_addr_from_32bit_cr3(entry) \
  ((u32)(entry) & (~((u32)PAGE_SIZE_4K - 1)))

/* get address field of a 4K non-PAE pdte (page directory entry) */
#define npae_get_addr_from_pde(entry) \
  ((u32)(entry) & (~((u32)PAGE_SIZE_4K - 1)))

/* get flags field of a 4K non-PAE pdte (page directory entry) */
#define npae_get_flags_from_pde(entry) \
  ((u32)(entry) & ((u32)PAGE_SIZE_4K - 1))

/* get address field of a 4M (non-PAE) pdte (page directory entry) */
#define npae_get_addr_from_pde_big(entry) \
  ((u32)(entry) & (~((u32)PAGE_SIZE_4M - 1)))

/* get flags field of a 4M (non-PAE) pdte (page directory entry) */
#define npae_get_flags_from_pde_big(entry) \
  ((u32)(entry) & ((u32)PAGE_SIZE_4M - 1))

/* get flags field of a pte (page table entry) */
#define npae_get_flags_from_pte(entry) \
  ((u32)(entry) & (((u32)PAGE_SIZE_4K - 1)))

/* get address field of a 4K (non-PAE) pte (page table entry) */
#define npae_get_addr_from_pte(entry) \
  ((u32)(entry) & (~((u32)PAGE_SIZE_4K - 1)))

/* get page offset field of a vaddr in a 4K page (PAE mode) */
#define pae_get_offset_4K_page(entry) \
  ((u32)(entry) & ((u32)PAGE_SIZE_4K - 1))

/* get page offset field of a vaddr in a 2M page */
#define pae_get_offset_big(entry) \
  ((u32)(entry) & ((u32)PAGE_SIZE_2M - 1))

/* get offset field of a vaddr in a 4K page (non-PAE mode) */
#define npae_get_offset_4K_page(vaddr) \
  ((u32)(vaddr) & ((u32)PAGE_SIZE_4K - 1))

/* get offset field of a vaddr in a 4M page */
#define npae_get_offset_big(vaddr) \
  ((u32)(vaddr) & ((u32)PAGE_SIZE_4M - 1))


/* get index field of a paddr in a pml4t level */
#define pae_get_pml4t_index(paddr)\
    (((paddr) & PAE_PML4T_MASK) >> PAE_PML4T_SHIFT)

/* get index field of a paddr in a pdp level */
#define pae_get_pdpt_index(paddr)\
    (((paddr) & PAE_PDPT_MASK) >> PAE_PDPT_SHIFT)

/* get index field of a paddr in a pd level */
#define pae_get_pdt_index(paddr)\
    (((paddr) & PAE_PDT_MASK) >> PAE_PDT_SHIFT)

/* get index field of a paddr in a pt level */
#define pae_get_pt_index(paddr)\
    (((paddr) & PAE_PT_MASK) >> PAE_PT_SHIFT)

/* get index field of a paddr in a pd level */
#define npae_get_pdt_index(paddr)\
    (((paddr) & NPAE_PAGE_DIR_MASK) >> NPAE_PAGEDIR_SHIFT)

/* get index field of a paddr in a pt level */
#define npae_get_pt_index(paddr)\
    (((paddr) & NPAE_PAGE_TABLE_MASK) >> NPAE_PAGETABLE_SHIFT)

/* returns 1 if addr is 4k page aligned */
#define is_page_4K_aligned(paddr)\
    ((((u32)PAGE_SIZE_4K - 1) & ((u32)paddr)) == 0)

#define set_exec(entry) (((u64)entry) &= (~((u64)_PAGE_NX)))
#define set_nonexec(entry) (((u64)entry) |= ((u64)_PAGE_NX))
#define set_readonly(entry) (((u64)entry) &= (~((u64)_PAGE_RW)))
#define set_readwrite(entry) (((u64)entry) |= ((u64)_PAGE_RW))
#define set_present(entry) (((u64)entry) |= ((u64)_PAGE_PRESENT))
#define set_not_present(entry) (((u64)entry) &= (~((u64)_PAGE_PRESENT)))

#define SAME_PAGE_PAE(addr1, addr2)		\
    (((addr1) >> PAE_PT_SHIFT) == ((addr2) >> PAE_PT_SHIFT))

#define SAME_PAGE_NPAE(addr1, addr2)		\
    (((addr1) >> NPAE_PAGETABLE_SHIFT) == ((addr2) >> NPAE_PAGETABLE_SHIFT))


#endif // __ASSEMBLY__






//////
// TXT (trusted execution technology)
//////


#ifndef __ASSEMBLY__

/*
 * TXT configuration registers (offsets from TXT_{PUB, PRIV}_CONFIG_REGS_BASE)
 */

#define TXT_PUB_CONFIG_REGS_BASE       0xfed30000
#define TXT_PRIV_CONFIG_REGS_BASE      0xfed20000

/* # pages for each config regs space - used by fixmap */
#define NR_TXT_CONFIG_PAGES            ((TXT_PUB_CONFIG_REGS_BASE - \
                                        TXT_PRIV_CONFIG_REGS_BASE) >>    \
                                        PAGE_SHIFT)

/* offsets to config regs (from either public or private _BASE) */
#define TXTCR_STS                   0x0000
#define TXTCR_ESTS                  0x0008
#define TXTCR_ERRORCODE             0x0030
#define TXTCR_CMD_RESET             0x0038
#define TXTCR_CMD_CLOSE_PRIVATE     0x0048
#define TXTCR_VER_FSBIF             0x0100
#define TXTCR_DIDVID                0x0110
#define TXTCR_VER_EMIF              0x0200
#define TXTCR_CMD_UNLOCK_MEM_CONFIG 0x0218
#define TXTCR_SINIT_BASE            0x0270
#define TXTCR_SINIT_SIZE            0x0278
#define TXTCR_MLE_JOIN              0x0290
#define TXTCR_HEAP_BASE             0x0300
#define TXTCR_HEAP_SIZE             0x0308
#define TXTCR_MSEG_BASE             0x0310
#define TXTCR_MSEG_SIZE             0x0318
#define TXTCR_DPR                   0x0330
#define TXTCR_CMD_OPEN_LOCALITY1    0x0380
#define TXTCR_CMD_CLOSE_LOCALITY1   0x0388
#define TXTCR_CMD_OPEN_LOCALITY2    0x0390
#define TXTCR_CMD_CLOSE_LOCALITY2   0x0398
#define TXTCR_CMD_SECRETS           0x08e0
#define TXTCR_CMD_NO_SECRETS        0x08e8
#define TXTCR_E2STS                 0x08f0


/*
* format of ERRORCODE register
*/
typedef struct {
        u32   type       ;//: 30;    //external-specific error code
        u32   external   ;//: 1;     // 0=from proc, 1=from external SW
        u32   valid      ;//: 1;     // 1=valid
} __attribute__((packed)) txt_errorcode_t;

#define pack_txt_errorcode_t(s) \
    (u64)( \
    (((u64)(s)->valid               & 0x000000003FFFFFFFULL) << 31) | \
    (((u64)(s)->external            & 0x0000000000000001ULL) << 1 ) | \
    (((u64)(s)->type                & 0x0000000000000001ULL) << 0 ) \
    )

#define unpack_txt_errorcode_t(s, value) \
    (s)->valid     = (u32)(((u64)value >> 31) & 0x000000003FFFFFFFULL); \
    (s)->external  = (u32)(((u64)value >> 1 ) & 0x0000000000000001ULL); \
    (s)->type      = (u32)(((u64)value >> 0 ) & 0x0000000000000001ULL);



/*
 * format of ESTS register
 */
typedef struct {
        u32   txt_reset_sts      ;//: 1;
        u32   reserved1          ;//: 5;
        u32   txt_wake_error_sts ;//: 1;
        u32   reserved2          ;//: 1;
} __attribute__((packed)) txt_ests_t;

#define pack_txt_ests_t(s) \
    (u64)( \
    (((u64)(s)->reserved2           & 0x0000000000000001ULL) << 7) | \
    (((u64)(s)->txt_wake_error_sts  & 0x0000000000000001ULL) << 6) | \
    (((u64)(s)->reserved1           & 0x000000000000001FULL) << 1) | \
    (((u64)(s)->txt_reset_sts       & 0x0000000000000001ULL) << 0) \
    )

#define unpack_txt_ests_t(s, value) \
   (s)->reserved2             = (u32)(((u64)value >> 7) & 0x0000000000000001ULL); \
   (s)->txt_wake_error_sts    = (u32)(((u64)value >> 6) & 0x0000000000000001ULL); \
   (s)->reserved1             = (u32)(((u64)value >> 1) & 0x000000000000001FULL); \
   (s)->txt_reset_sts         = (u32)(((u64)value >> 0) & 0x0000000000000001ULL);


/*
 * format of E2STS register
 */

typedef struct {
        u32   slp_entry_error_sts  ;//: 1;
        u32   secrets_sts          ;//: 1;
        u32   block_mem_sts        ;//: 1;
        u32   reset_sts            ;//: 1;
} __attribute__((packed)) txt_e2sts_t;

#define pack_txt_e2sts_t(s) \
    (u64)( \
    (((u64)(s)->reset_sts           & 0x0000000000000001ULL) << 3) | \
    (((u64)(s)->block_mem_sts       & 0x0000000000000001ULL) << 2) | \
    (((u64)(s)->secrets_sts         & 0x0000000000000001ULL) << 1) | \
    (((u64)(s)->slp_entry_error_sts & 0x0000000000000001ULL) << 0) \
    )

#define unpack_txt_e2sts_t(s, value) \
    (s)->reset_sts             = (u32)(((u64)value >> 3) & 0x0000000000000001ULL); \
    (s)->block_mem_sts         = (u32)(((u64)value >> 2) & 0x0000000000000001ULL); \
    (s)->secrets_sts           = (u32)(((u64)value >> 1) & 0x0000000000000001ULL); \
    (s)->slp_entry_error_sts   = (u32)(((u64)value >> 0) & 0x0000000000000001ULL);


/*
 * format of STS register
 */
typedef struct {
    u32   senter_done_sts         ; //: 1;
    u32   sexit_done_sts          ; //: 1;
    u32   reserved1               ; //: 2;
    u32   mem_unlock_sts          ; //: 1;
    u32   reserved2               ; //: 1;
    u32   mem_config_lock_sts     ; //: 1;
    u32   private_open_sts        ; //: 1;
    u32   reserved3               ; //: 3;
    u32   mem_config_ok_sts       ; //: 1;
} __attribute__((packed)) txt_sts_t;

#define pack_txt_sts_t(s) \
    (u64)( \
    (((u64)(s)->mem_config_ok_sts & 0x0000000000000001ULL) << 11) | \
    (((u64)(s)->reserved3 & 0x0000000000000007ULL) << 8) | \
    (((u64)(s)->private_open_sts & 0x0000000000000001ULL) << 7) | \
    (((u64)(s)->mem_config_lock_sts & 0x0000000000000001ULL) << 6) | \
    (((u64)(s)->reserved2 & 0x0000000000000001ULL) << 5) | \
    (((u64)(s)->mem_unlock_sts & 0x0000000000000001ULL) << 4) | \
    (((u64)(s)->reserved1 & 0x0000000000000003ULL) << 2) | \
    (((u64)(s)->sexit_done_sts & 0x0000000000000001ULL) << 1) | \
    (((u64)(s)->senter_done_sts & 0x0000000000000001ULL) << 0) \
    )

#define unpack_txt_sts_t(s, value) \
    (s)->mem_config_ok_sts = (u32)(((u64)value >> 11) & 0x0000000000000001ULL); \
    (s)->reserved3 = (u32)(((u64)value >> 8) & 0x0000000000000007ULL); \
    (s)->private_open_sts = (u32)(((u64)value >> 7) & 0x0000000000000001ULL); \
    (s)->mem_config_lock_sts = (u32)(((u64)value >> 6) & 0x0000000000000001ULL); \
    (s)->reserved2 = (u32)(((u64)value >> 5) & 0x0000000000000001ULL); \
    (s)->mem_unlock_sts = (u32)(((u64)value >> 4) & 0x0000000000000001ULL); \
    (s)->reserved1 = (u32)(((u64)value >> 2) & 0x0000000000000003ULL); \
    (s)->sexit_done_sts = (u32)(((u64)value >> 1) & 0x0000000000000001ULL); \
    (s)->senter_done_sts = (u32)(((u64)value >> 0) & 0x0000000000000001ULL);


/*
 * format of DIDVID register
 */
typedef struct {
        u32  vendor_id; //16
        u32  device_id; //16
        u32  revision_id; //16
        u32  reserved; //16
} __attribute__((packed)) txt_didvid_t;

#define pack_txt_didvid_t(s) \
    (u64)( \
    (((u64)(s)->reserved    & 0x000000000000FFFFULL) << 48) | \
    (((u64)(s)->revision_id & 0x000000000000FFFFULL) << 32) | \
    (((u64)(s)->device_id   & 0x000000000000FFFFULL) << 16) | \
    (((u64)(s)->vendor_id   & 0x000000000000FFFFULL) << 0 ) \
    )

#define unpack_txt_didvid_t(s, value) \
    (s)->reserved       = (u32)(((u64)value >> 48) & 0x000000000000FFFFULL); \
    (s)->revision_id    = (u32)(((u64)value >> 32) & 0x000000000000FFFFULL); \
    (s)->device_id      = (u32)(((u64)value >> 16) & 0x000000000000FFFFULL); \
    (s)->vendor_id      = (u32)(((u64)value >> 0 ) & 0x000000000000FFFFULL);



/*
 * format of VER.FSBIF and VER.EMIF registers
 */
typedef struct {
    u32  reserved       ;//: 31;
    u32  prod_fused     ;//: 1;
} __attribute__((packed)) txt_ver_fsbif_emif_t;

#define pack_txt_ver_fsbif_emif_t(s) \
    (u64)( \
    (((u64)(s)->prod_fused  & 0x0000000000000001ULL) << 31) | \
    (((u64)(s)->reserved    & 0x000000007FFFFFFFULL) << 0 ) \
    )

#define unpack_txt_ver_fsbif_emif_t(s, value) \
    (s)->prod_fused     = (u32)(((u64)value >> 31) & 0x0000000000000001ULL); \
    (s)->reserved       = (u32)(((u64)value >> 0 ) & 0x000000007FFFFFFFULL);



/*
 * RLP JOIN structure for GETSEC[WAKEUP] and MLE_JOIN register
 */
typedef struct {
    uint32_t	gdt_limit;
    uint32_t	gdt_base;
    uint32_t	seg_sel;               /* cs (ds, es, ss are seg_sel+8) */
    uint32_t	entry_point;           /* phys addr */
} mle_join_t;

/*
 * format of MSEG header
 */
typedef struct {
    uint32_t    revision_id;
    uint32_t    smm_mon_feat;
    uint32_t    gdtr_limit;
    uint32_t    gdtr_base_offset;
    uint32_t    cs_sel;
    uint32_t    eip_offset;
    uint32_t    esp_offset;
    uint32_t    cr3_offset;
} mseg_hdr_t;



/*
 * format of TXT ERRORCODE SW register
 */

typedef struct {
        uint32_t  err1    ;//: 15;     //pecific to src
        uint32_t  src     ;//: 1;      // 0=ACM, 1=other
        uint32_t  err2    ;//: 14;     // specific to src
} __attribute__((packed)) txt_errorcode_sw_t;


#define pack_txt_errorcode_sw_t(s) \
    (u32)( \
    (((u32)(s)->err2    & 0x00003FFFUL) << 16) | \
    (((u32)(s)->src     & 0x00000001UL) << 15) | \
    (((u32)(s)->err1    & 0x00007FFFUL) << 0 ) \
    )

#define unpack_txt_errorcode_sw_t(s, value) \
    (s)->err2    = (u32)(((u32)value >> 16) & 0x00003FFFUL); \
    (s)->src     = (u32)(((u32)value >> 15) & 0x00000001UL); \
    (s)->err1    = (u32)(((u32)value >> 0 ) & 0x00007FFFUL);



/*
 * ACM errors (txt_errorcode_sw_t.src=0), format of err field
 */

typedef struct {
        uint32_t acm_type  ;//: 4;  // 0000=BIOS ACM, 0001=SINIT,
                                 // 0010-1111=reserved
        uint32_t progress  ;//: 6;
        uint32_t error     ;//: 4;
        uint32_t reserved  ;//: 1;
        uint32_t src       ;//: 1;  // above value
        uint32_t error2    ;//: 14; // sub-error
} __attribute__((packed)) acmod_error_t;

#define pack_acmod_error_t(s) \
    (u32)( \
    (((u32)(s)->error2      & 0x00000001UL) << 16) | \
    (((u32)(s)->src         & 0x00000001UL) << 15) | \
    (((u32)(s)->reserved    & 0x00000001UL) << 14) | \
    (((u32)(s)->error       & 0x0000000FUL) << 10) | \
    (((u32)(s)->progress    & 0x0000003FUL) << 4 ) | \
    (((u32)(s)->acm_type    & 0x0000000FUL) << 0 ) \
    )

#define unpack_acmod_error_t(s, value) \
    (s)->error2     = (u32)(((u32)value >> 16) & 0x00000001UL); \
    (s)->src        = (u32)(((u32)value >> 15) & 0x00000001UL); \
    (s)->reserved   = (u32)(((u32)value >> 14) & 0x00000001UL); \
    (s)->error      = (u32)(((u32)value >> 10) & 0x0000000FUL); \
    (s)->progress   = (u32)(((u32)value >> 4 ) & 0x0000003FUL); \
    (s)->acm_type   = (u32)(((u32)value >> 0 ) & 0x0000000FUL);



/*
 * SINIT/MLE capabilities
 */
typedef uint32_t txt_caps_t;

#define TXT_CAPS_T_RLP_WAKE_GETSEC      (1UL << 0)
#define TXT_CAPS_T_RLP_WAKE_MONITOR     (1UL << 1)
#define TXT_CAPS_T_ECX_PGTBL            (1UL << 2)


/* taken from tboot-20101005/include/uuid.h */
typedef struct __packed {
  uint32_t    data1;
  uint16_t    data2;
  uint16_t    data3;
  uint16_t    data4;
  uint8_t     data5[6];
} uuid_t;

/*
 * MLE header structure
 *   describes an MLE for SINIT and OS/loader SW
 */
typedef struct {
    uuid_t      uuid;
    uint32_t    length;
    uint32_t    version;
    uint32_t    entry_point;
    uint32_t    first_valid_page;
    uint32_t    mle_start_off;
    uint32_t    mle_end_off;
    txt_caps_t  capabilities;
    uint32_t    cmdline_start_off;
    uint32_t    cmdline_end_off;
} __attribute__((packed)) mle_hdr_t;

#define MLE_HDR_UUID      {0x9082ac5a, 0x476f, 0x74a7, 0x5c0f, \
                              {0x55, 0xa2, 0xcb, 0x51, 0xb6, 0x42}}

/*
 * values supported by current version of tboot
 */
#define MLE_HDR_VER       0x00020001     /* 2.1 */
#define MLE_HDR_CAPS      0x00000007     /* rlp_wake_{getsec, monitor} = 1,
                                            ecx_pgtbl = 1 */

/* from tboot-20101005/include/tb_error.h */
typedef enum {
    TB_ERR_NONE                = 0,         /* succeed */
    TB_ERR_FIXED               = 1,         /* previous error has been fixed */

    TB_ERR_GENERIC,                         /* non-fatal generic error */

    TB_ERR_TPM_NOT_READY,                   /* tpm not ready */
    TB_ERR_SMX_NOT_SUPPORTED,               /* smx not supported */
    TB_ERR_VMX_NOT_SUPPORTED,               /* vmx not supported */
    TB_ERR_TXT_NOT_SUPPORTED,               /* txt not supported */

    TB_ERR_MODULE_VERIFICATION_FAILED,      /* module failed to verify against
                                               policy */
    TB_ERR_MODULES_NOT_IN_POLICY,           /* modules in mbi but not in
                                               policy */
    TB_ERR_POLICY_INVALID,                  /* policy is invalid */
    TB_ERR_POLICY_NOT_PRESENT,              /* no policy in TPM NV */

    TB_ERR_SINIT_NOT_PRESENT,               /* SINIT ACM not provided */
    TB_ERR_ACMOD_VERIFY_FAILED,             /* verifying AC module failed */

    TB_ERR_POST_LAUNCH_VERIFICATION,        /* verification of post-launch
                                               failed */
    TB_ERR_S3_INTEGRITY,                    /* creation or verification of
                                               S3 integrity measurements
                                               failed */

    TB_ERR_FATAL,                           /* generic fatal error */
    TB_ERR_MAX
} tb_error_t;



/*
 * GETSEC[] instructions
 */

/* GETSEC instruction opcode */
#define IA32_GETSEC_OPCODE		".byte 0x0f,0x37"

/* GETSEC leaf function codes */
#define IA32_GETSEC_CAPABILITIES	0
#define IA32_GETSEC_SENTER		4
#define IA32_GETSEC_SEXIT		5
#define IA32_GETSEC_PARAMETERS		6
#define IA32_GETSEC_SMCTRL		7
#define IA32_GETSEC_WAKEUP		8

/*
 * GETSEC[] leaf functions
 */

typedef struct {
        uint32_t chipset_present    ;//: 1;
        uint32_t undefined1	        ;//: 1;
        uint32_t enteraccs	        ;//: 1;
        uint32_t exitac	            ;//: 1;
        uint32_t senter	            ;//: 1;
        uint32_t sexit	            ;//: 1;
        uint32_t parameters	        ;//: 1;
        uint32_t smctrl	            ;//: 1;
        uint32_t wakeup	            ;//: 1;
        uint32_t undefined9	        ;//: 22;
        uint32_t extended_leafs     ;//: 1;
} __attribute__((packed)) capabilities_t;

#define pack_capabilities_t(s) \
    (u32)( \
    (((u32)(s)->extended_leafs      & 0x00000001UL) << 31) | \
    (((u32)(s)->undefined9          & 0x003FFFFFUL) << 9 ) | \
    (((u32)(s)->wakeup              & 0x00000001UL) << 8 ) | \
    (((u32)(s)->smctrl              & 0x00000001UL) << 7 ) | \
    (((u32)(s)->parameters          & 0x00000001UL) << 6 ) | \
    (((u32)(s)->sexit               & 0x00000001UL) << 5 ) | \
    (((u32)(s)->senter              & 0x00000001UL) << 4 ) | \
    (((u32)(s)->exitac              & 0x00000001UL) << 3 ) | \
    (((u32)(s)->enteraccs           & 0x00000001UL) << 2 ) | \
    (((u32)(s)->undefined1          & 0x00000001UL) << 1 ) | \
    (((u32)(s)->chipset_present     & 0x00000001UL) << 0 ) \
    )

#define unpack_capabilities_t(s, value) \
    (s)->extended_leafs      = (u32)(((u32)value >> 31) & 0x00000001UL); \
    (s)->undefined9          = (u32)(((u32)value >> 9 ) & 0x003FFFFFUL); \
    (s)->wakeup              = (u32)(((u32)value >> 8 ) & 0x00000001UL); \
    (s)->smctrl              = (u32)(((u32)value >> 7 ) & 0x00000001UL); \
    (s)->parameters          = (u32)(((u32)value >> 6 ) & 0x00000001UL); \
    (s)->sexit               = (u32)(((u32)value >> 5 ) & 0x00000001UL); \
    (s)->senter              = (u32)(((u32)value >> 4 ) & 0x00000001UL); \
    (s)->exitac              = (u32)(((u32)value >> 3 ) & 0x00000001UL); \
    (s)->enteraccs           = (u32)(((u32)value >> 2 ) & 0x00000001UL); \
    (s)->undefined1          = (u32)(((u32)value >> 1 ) & 0x00000001UL); \
    (s)->chipset_present     = (u32)(((u32)value >> 0 ) & 0x00000001UL);


/* helper fn. for getsec_capabilities */
/* this is arbitrary and can be increased when needed */
#define MAX_SUPPORTED_ACM_VERSIONS      16

typedef struct {
    struct {
        uint32_t mask;
        uint32_t version;
    } acm_versions[MAX_SUPPORTED_ACM_VERSIONS];
    int n_versions;
    uint32_t acm_max_size;
    uint32_t acm_mem_types;
    uint32_t senter_controls;
    bool proc_based_scrtm;
    bool preserve_mce;
} getsec_parameters_t;





#define MTRR_TYPE_MIXED         -1
#define MMIO_APIC_BASE          0xFEE00000
#define NR_MMIO_APIC_PAGES      1
#define NR_MMIO_IOAPIC_PAGES    1
#define NR_MMIO_PCICFG_PAGES    1


typedef u8   txt_heap_t;

/*
 * data-passing structures contained in TXT heap:
 *   - BIOS
 *   - OS/loader to MLE
 *   - OS/loader to SINIT
 *   - SINIT to MLE
 */

/*
 * BIOS structure
 */
typedef struct {
    uint32_t  version;              /* WB = 2, current = 3 */
    uint32_t  bios_sinit_size;
    uint64_t  lcp_pd_base;
    uint64_t  lcp_pd_size;
    uint32_t  num_logical_procs;
    /* versions >= 3 */
    uint64_t  flags;
} __attribute__ ((packed)) bios_data_t;


/*
 * OS/loader to SINIT structure
 */
typedef struct {
    uint32_t    version;           /* currently 4, 5 */
    uint32_t    reserved;
    uint64_t    mle_ptab;
    uint64_t    mle_size;
    uint64_t    mle_hdr_base;
    uint64_t    vtd_pmr_lo_base;
    uint64_t    vtd_pmr_lo_size;
    uint64_t    vtd_pmr_hi_base;
    uint64_t    vtd_pmr_hi_size;
    uint64_t    lcp_po_base;
    uint64_t    lcp_po_size;
    txt_caps_t  capabilities;
    /* versions >= 5 */
    uint64_t    efi_rsdt_ptr;
} __attribute__ ((packed)) os_sinit_data_t;

/*
 * SINIT to MLE structure
 */
#define MDR_MEMTYPE_GOOD                0x00
#define MDR_MEMTYPE_SMM_OVERLAY         0x01
#define MDR_MEMTYPE_SMM_NONOVERLAY      0x02
#define MDR_MEMTYPE_PCIE_CONFIG_SPACE   0x03
#define MDR_MEMTYPE_PROTECTED           0x04

typedef struct __attribute__ ((packed)) {
    uint64_t  base;
    uint64_t  length;
    uint8_t   mem_type;
    uint8_t   reserved[7];
} __attribute__ ((packed)) sinit_mdr_t;

#define SHA1_SIZE      20
typedef uint8_t   sha1_hash_t[SHA1_SIZE];

typedef struct {
    uint32_t     version;             /* currently 6-8 */
    sha1_hash_t  bios_acm_id;
    uint32_t     edx_senter_flags;
    uint64_t     mseg_valid;
    sha1_hash_t  sinit_hash;
    sha1_hash_t  mle_hash;
    sha1_hash_t  stm_hash;
    sha1_hash_t  lcp_policy_hash;
    uint32_t     lcp_policy_control;
    uint32_t     rlp_wakeup_addr;
    uint32_t     reserved;
    uint32_t     num_mdrs;
    uint32_t     mdrs_off;
    uint32_t     num_vtd_dmars;
    uint32_t     vtd_dmars_off;
    /* versions >= 8 */
    uint32_t     proc_scrtm_status;
} __attribute__ ((packed)) sinit_mle_data_t;


#endif //__ASSEMBLY__









//////
// VMX (virtualization extensions)
//////

//---platform
#define IA32_VMX_MSRCOUNT   								12

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
#define NMI_VECTOR	0x2
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


#define VMX_VMEXIT_CRX_ACCESS 0x1C

#define VMX_CRX_ACCESS_FROM	0x1
#define VMX_CRX_ACCESS_TO		0x0

#define VMX_VMEXIT_EXCEPTION    0
#define VMX_VMEXIT_INVLPG 14
#define	VMX_VMEXIT_SIPI	4
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


typedef struct {
	u16 sel;
	u64 base;
	u32 limit;
	union{
		segment_desc_accessrights ar;
		u32 aru32;
	};
} __attribute__ ((packed)) segment_desc;


typedef struct msr_entry {
	u32 index;
	u32 reserved;
	u64 data;
} __attribute__((packed)) msr_entry_t;


typedef struct {
  u32 id;
  u32 vmxonSize;
  u32 physicalAddressWidth;
  u32 vmcsMemoryType;
  u32 ioCapability;
  u64 cr0fixed0;
  u64 cr0fixed1;
  u64 cr4fixed0;
  u64 cr4fixed1;
  u64 pinbasedctls;
  u64 procbasedctls;
  u64 procbasedctls2;
u64 exitctls;
u64 entryctls;
}__attribute__ ((packed)) VMXINFO;


//VMX VMCS fields
struct _vmx_vmcsfields {
	//16-bit control fields
	unsigned int control_vpid;
  // Natural 32-bit Control fields
  unsigned int  control_VMX_pin_based;
  unsigned int  control_VMX_cpu_based;
	unsigned int  control_VMX_seccpu_based;
  unsigned int  control_exception_bitmap;
  unsigned int  control_pagefault_errorcode_mask;
  unsigned int  control_pagefault_errorcode_match;
  unsigned int  control_CR3_target_count;
  unsigned int  control_VM_exit_controls;
  unsigned int  control_VM_exit_MSR_store_count;
  unsigned int  control_VM_exit_MSR_load_count;
  unsigned int  control_VM_entry_controls;
  unsigned int  control_VM_entry_MSR_load_count;
  unsigned int  control_VM_entry_interruption_information;
  unsigned int  control_VM_entry_exception_errorcode;
  unsigned int  control_VM_entry_instruction_length;
  unsigned int  control_Task_PRivilege_Threshold;
  // Natural 64-bit Control fields
  unsigned long long  control_CR0_mask;
  unsigned long long  control_CR4_mask;
  unsigned long long  control_CR0_shadow;
  unsigned long long  control_CR4_shadow;
  unsigned long long  control_CR3_target0;
  unsigned long long  control_CR3_target1;
  unsigned long long  control_CR3_target2;
  unsigned long long  control_CR3_target3;
  // Full 64-bit Control fields
  unsigned int  control_IO_BitmapA_address_full;
  unsigned int  control_IO_BitmapA_address_high;
  unsigned int  control_IO_BitmapB_address_full;
  unsigned int  control_IO_BitmapB_address_high;
  unsigned int  control_MSR_Bitmaps_address_full;
  unsigned int  control_MSR_Bitmaps_address_high;
  unsigned int  control_VM_exit_MSR_store_address_full;
  unsigned int  control_VM_exit_MSR_store_address_high;
  unsigned int  control_VM_exit_MSR_load_address_full;
  unsigned int  control_VM_exit_MSR_load_address_high;
  unsigned int  control_VM_entry_MSR_load_address_full;
  unsigned int  control_VM_entry_MSR_load_address_high;
  unsigned int  control_Executive_VMCS_pointer_full;
  unsigned int  control_Executive_VMCS_pointer_high;
  unsigned int  control_TSC_offset_full;
  unsigned int  control_TSC_offset_high;
  unsigned int  control_virtual_APIC_page_address_full;
  unsigned int  control_virtual_APIC_page_address_high;
	unsigned int control_EPT_pointer_full;
	unsigned int control_EPT_pointer_high;
  // Natural 64-bit Host-State fields
  unsigned long long  host_CR0;
  unsigned long long  host_CR3;
  unsigned long long  host_CR4;
  unsigned long long  host_FS_base;
  unsigned long long  host_GS_base;
  unsigned long long  host_TR_base;
  unsigned long long  host_GDTR_base;
  unsigned long long  host_IDTR_base;
  unsigned long long  host_SYSENTER_ESP;
  unsigned long long  host_SYSENTER_EIP;
  unsigned long long  host_RSP;
  unsigned long long  host_RIP;
  // Natural 32-bit Host-State fields
  unsigned int  host_SYSENTER_CS;
  // Natural 16-bit Host-State fields
  unsigned int  host_ES_selector;
  unsigned int  host_CS_selector;
  unsigned int  host_SS_selector;
  unsigned int  host_DS_selector;
  unsigned int  host_FS_selector;
  unsigned int  host_GS_selector;
  unsigned int  host_TR_selector;
  // Natural 64-bit Guest-State fields
  unsigned long long  guest_CR0;
  unsigned long long  guest_CR3;
  unsigned long long  guest_CR4;
  unsigned long long  guest_ES_base;
  unsigned long long  guest_CS_base;
  unsigned long long  guest_SS_base;
  unsigned long long  guest_DS_base;
  unsigned long long  guest_FS_base;
  unsigned long long  guest_GS_base;
  unsigned long long  guest_LDTR_base;
  unsigned long long  guest_TR_base;
  unsigned long long  guest_GDTR_base;
  unsigned long long  guest_IDTR_base;
  unsigned long long  guest_DR7;
  unsigned long long  guest_RSP;
  unsigned long long  guest_RIP;
  unsigned long long  guest_RFLAGS;
  unsigned long long  guest_pending_debug_x;
  unsigned long long  guest_SYSENTER_ESP;
  unsigned long long  guest_SYSENTER_EIP;
  // Natural 32-bit Guest-State fields
  unsigned int  guest_ES_limit;
  unsigned int  guest_CS_limit;
  unsigned int  guest_SS_limit;
  unsigned int  guest_DS_limit;
  unsigned int  guest_FS_limit;
  unsigned int  guest_GS_limit;
  unsigned int  guest_LDTR_limit;
  unsigned int  guest_TR_limit;
  unsigned int  guest_GDTR_limit;
  unsigned int  guest_IDTR_limit;
  unsigned int  guest_ES_access_rights;
  unsigned int  guest_CS_access_rights;
  unsigned int  guest_SS_access_rights;
  unsigned int  guest_DS_access_rights;
  unsigned int  guest_FS_access_rights;
  unsigned int  guest_GS_access_rights;
  unsigned int  guest_LDTR_access_rights;
  unsigned int  guest_TR_access_rights;
  unsigned int  guest_interruptibility;
  unsigned int  guest_activity_state;
  unsigned int  guest_SMBASE;
  unsigned int  guest_SYSENTER_CS;
  // Natural 16-bit Guest-State fields
  unsigned int  guest_ES_selector;
  unsigned int  guest_CS_selector;
  unsigned int  guest_SS_selector;
  unsigned int  guest_DS_selector;
  unsigned int  guest_FS_selector;
  unsigned int  guest_GS_selector;
  unsigned int  guest_LDTR_selector;
  unsigned int  guest_TR_selector;
  // Full 64-bit Guest-State fields
  unsigned int  guest_VMCS_link_pointer_full;
  unsigned int  guest_VMCS_link_pointer_high;
  unsigned int  guest_IA32_DEBUGCTL_full;
  unsigned int  guest_IA32_DEBUGCTL_high;
    unsigned int 	guest_paddr_full;
    unsigned int 	guest_paddr_high;
    unsigned int  guest_PDPTE0_full;
	  unsigned int  guest_PDPTE0_high;
    unsigned int  guest_PDPTE1_full;
	  unsigned int  guest_PDPTE1_high;
    unsigned int  guest_PDPTE2_full;
	  unsigned int  guest_PDPTE2_high;
    unsigned int  guest_PDPTE3_full;
	  unsigned int  guest_PDPTE3_high;
  //Read-Only Fields
  unsigned int  info_vminstr_error;
  unsigned int  info_vmexit_reason;
  unsigned int  info_vmexit_interrupt_information;
  unsigned int  info_vmexit_interrupt_error_code;
  unsigned int  info_IDT_vectoring_information;
  unsigned int  info_IDT_vectoring_error_code;
  unsigned int  info_vmexit_instruction_length;
  unsigned int  info_vmx_instruction_information;
  unsigned long long  info_exit_qualification;
  unsigned long long  info_IO_RCX;
  unsigned long long  info_IO_RSI;
  unsigned long long  info_IO_RDI;
  unsigned long long  info_IO_RIP;
  unsigned long long  info_guest_linear_address;
} __attribute__((packed));



//VMX VMCS read-only field encodings
#define VMCS_INFO_VMINSTR_ERROR  				0x4400
#define VMCS_INFO_VMEXIT_REASON 				0x4402
#define VMCS_INFO_VMEXIT_INTERRUPT_INFORMATION	0x4404
#define VMCS_INFO_VMEXIT_INTERRUPT_ERROR_CODE 	0x4406
#define VMCS_INFO_IDT_VECTORING_INFORMATION 	0x4408
#define VMCS_INFO_IDT_VECTORING_ERROR_CODE 		0x440a
#define VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH 	0x440c
#define VMCS_INFO_VMX_INSTRUCTION_INFORMATION 	0x440e
#define VMCS_INFO_EXIT_QUALIFICATION 			0x6400
#define VMCS_INFO_IO_RCX 						0x6402
#define VMCS_INFO_IO_RSI 						0x6404
#define VMCS_INFO_IO_RDI 						0x6406
#define VMCS_INFO_IO_RIP 						0x6408
#define VMCS_INFO_GUEST_PADDR_FULL 				0x2400
#define VMCS_INFO_GUEST_PADDR_HIGH 				0x2401
#define VMCS_INFO_GUEST_LINEAR_ADDRESS			0x640a

//VMX VMCS read-write field encodings
#define VMCS_CONTROL_VPID 								0x0000

#define VMCS_CONTROL_VMX_PIN_BASED 						0x4000
#define VMCS_CONTROL_VMX_CPU_BASED 						0x4002
#define VMCS_CONTROL_VMX_SECCPU_BASED 					0x401E
#define VMCS_CONTROL_EXCEPTION_BITMAP 					0x4004
#define VMCS_CONTROL_PAGEFAULT_ERRORCODE_MASK 			0x4006
#define VMCS_CONTROL_PAGEFAULT_ERRORCODE_MATCH 			0x4008
#define VMCS_CONTROL_CR3_TARGET_COUNT 					0x400A
#define VMCS_CONTROL_VM_EXIT_CONTROLS 					0x400C
#define VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT 			0x400E
#define VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT 			0x4010
#define VMCS_CONTROL_VM_ENTRY_CONTROLS 					0x4012
#define VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT 			0x4014
#define VMCS_CONTROL_VM_ENTRY_INTERRUPTION_INFORMATION 	0x4016
#define VMCS_CONTROL_VM_ENTRY_EXCEPTION_ERRORCODE 		0x4018
#define VMCS_CONTROL_VM_ENTRY_INSTRUCTION_LENGTH 		0x401A
#define VMCS_CONTROL_TASK_PRIVILEGE_THRESHOLD 			0x401C

#define VMCS_CONTROL_CR0_MASK 							0x6000
#define VMCS_CONTROL_CR4_MASK 							0x6002
#define VMCS_CONTROL_CR0_SHADOW 						0x6004
#define VMCS_CONTROL_CR4_SHADOW 						0x6006
#define VMCS_CONTROL_CR3_TARGET0 						0x6008
#define VMCS_CONTROL_CR3_TARGET1 						0x600A
#define VMCS_CONTROL_CR3_TARGET2 						0x600C
#define VMCS_CONTROL_CR3_TARGET3 						0x600E

#define VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL 0x2000
#define VMCS_CONTROL_IO_BITMAPA_ADDRESS_HIGH 0x2001
#define VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL 0x2002
#define VMCS_CONTROL_IO_BITMAPB_ADDRESS_HIGH 0x2003
#define VMCS_CONTROL_MSR_BITMAPS_ADDRESS_FULL 0x2004
#define VMCS_CONTROL_MSR_BITMAPS_ADDRESS_HIGH 0x2005
#define VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL 0x2006
#define VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_HIGH 0x2007
#define VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL 0x2008
#define VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_HIGH 0x2009
#define VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL 0x200A
#define VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_HIGH 0x200B
#define VMCS_CONTROL_EXECUTIVE_POINTER_FULL 0x200C
#define VMCS_CONTROL_EXECUTIVE_POINTER_HIGH 0x200D
#define VMCS_CONTROL_TSC_OFFSET_FULL 0x2010
#define VMCS_CONTROL_TSC_OFFSET_HIGH 0x2011
#define VMCS_CONTROL_VIRTUAL_APIC_PAGE_ADDRESS_FULL 0x2012
#define VMCS_CONTROL_VIRTUAL_APIC_PAGE_ADDRESS_HIGH 0x2013
#define VMCS_CONTROL_EPT_POINTER_FULL 0x201A
#define VMCS_CONTROL_EPT_POINTER_HIGH 0x201B

#define VMCS_HOST_CR0 0x6C00
#define VMCS_HOST_CR3 0x6C02
#define VMCS_HOST_CR4 0x6C04
#define VMCS_HOST_FS_BASE 0x6C06
#define VMCS_HOST_GS_BASE 0x6C08
#define VMCS_HOST_TR_BASE 0x6C0A
#define VMCS_HOST_GDTR_BASE 0x6C0C
#define VMCS_HOST_IDTR_BASE 0x6C0E
#define VMCS_HOST_SYSENTER_ESP 0x6C10
#define VMCS_HOST_SYSENTER_EIP 0x6C12
#define VMCS_HOST_RSP 0x6C14
#define VMCS_HOST_RIP 0x6C16

#define VMCS_HOST_SYSENTER_CS 0x4C00
#define VMCS_HOST_IA32_EFER_FULL 0x2C02

#define VMCS_HOST_ES_SELECTOR 0x0C00
#define VMCS_HOST_CS_SELECTOR 0x0C02
#define VMCS_HOST_SS_SELECTOR 0x0C04
#define VMCS_HOST_DS_SELECTOR 0x0C06
#define VMCS_HOST_FS_SELECTOR 0x0C08
#define VMCS_HOST_GS_SELECTOR 0x0C0A
#define VMCS_HOST_TR_SELECTOR 0x0C0C

#define VMCS_GUEST_CR0 0x6800
#define VMCS_GUEST_CR3 0x6802
#define VMCS_GUEST_CR4 0x6804
#define VMCS_GUEST_ES_BASE 0x6806
#define VMCS_GUEST_CS_BASE 0x6808
#define VMCS_GUEST_SS_BASE 0x680A
#define VMCS_GUEST_DS_BASE 0x680C
#define VMCS_GUEST_FS_BASE 0x680E
#define VMCS_GUEST_GS_BASE 0x6810
#define VMCS_GUEST_LDTR_BASE 0x6812
#define VMCS_GUEST_TR_BASE 0x6814
#define VMCS_GUEST_GDTR_BASE 0x6816
#define VMCS_GUEST_IDTR_BASE 0x6818
#define VMCS_GUEST_DR7 0x681A
#define VMCS_GUEST_RSP 0x681C
#define VMCS_GUEST_RIP 0x681E
#define VMCS_GUEST_RFLAGS 0x6820
#define VMCS_GUEST_PENDING_DEBUG_X 0x6822
#define VMCS_GUEST_SYSENTER_ESP 0x6824
#define VMCS_GUEST_SYSENTER_EIP 0x6826
#define VMCS_GUEST_IA32_EFER_FULL 0x2806
#define VMCS_GUEST_PDPTE0_FULL 0x280A
#define VMCS_GUEST_PDPTE0_HIGH 0x280B
#define VMCS_GUEST_PDPTE1_FULL 0x280C
#define VMCS_GUEST_PDPTE1_HIGH 0x280D
#define VMCS_GUEST_PDPTE2_FULL 0x280E
#define VMCS_GUEST_PDPTE2_HIGH 0x280F
#define VMCS_GUEST_PDPTE3_FULL 0x2810
#define VMCS_GUEST_PDPTE3_HIGH 0x2811

#define VMCS_GUEST_ES_LIMIT 0x4800
#define VMCS_GUEST_CS_LIMIT 0x4802
#define VMCS_GUEST_SS_LIMIT 0x4804
#define VMCS_GUEST_DS_LIMIT 0x4806
#define VMCS_GUEST_FS_LIMIT 0x4808
#define VMCS_GUEST_GS_LIMIT 0x480A
#define VMCS_GUEST_LDTR_LIMIT 0x480C
#define VMCS_GUEST_TR_LIMIT 0x480E
#define VMCS_GUEST_GDTR_LIMIT 0x4810
#define VMCS_GUEST_IDTR_LIMIT 0x4812
#define VMCS_GUEST_ES_ACCESS_RIGHTS 0x4814
#define VMCS_GUEST_CS_ACCESS_RIGHTS 0x4816
#define VMCS_GUEST_SS_ACCESS_RIGHTS 0x4818
#define VMCS_GUEST_DS_ACCESS_RIGHTS 0x481A
#define VMCS_GUEST_FS_ACCESS_RIGHTS 0x481C
#define VMCS_GUEST_GS_ACCESS_RIGHTS 0x481E
#define VMCS_GUEST_LDTR_ACCESS_RIGHTS 0x4820
#define VMCS_GUEST_TR_ACCESS_RIGHTS 0x4822
#define VMCS_GUEST_INTERRUPTIBILITY 0x4824
#define VMCS_GUEST_ACTIVITY_STATE 0x4826
#define VMCS_GUEST_SMBASE 0x4828
#define VMCS_GUEST_SYSENTER_CS 0x482A

#define VMCS_GUEST_ES_SELECTOR 0x0800
#define VMCS_GUEST_CS_SELECTOR 0x0802
#define VMCS_GUEST_SS_SELECTOR 0x0804
#define VMCS_GUEST_DS_SELECTOR 0x0806
#define VMCS_GUEST_FS_SELECTOR 0x0808
#define VMCS_GUEST_GS_SELECTOR 0x080A
#define VMCS_GUEST_LDTR_SELECTOR 0x080C
#define VMCS_GUEST_TR_SELECTOR 0x080E

#define VMCS_GUEST_VMCS_LINK_POINTER_FULL 0x2800
#define VMCS_GUEST_VMCS_LINK_POINTER_HIGH 0x2801
#define VMCS_GUEST_IA32_DEBUGCTL_FULL 0x2802
#define VMCS_GUEST_IA32_DEBUGCTL_HIGH  0x2803

struct _vmx_vmcsrofields_encodings	{
 unsigned int  encoding;
 unsigned int  fieldoffset;
} __attribute__((packed));

struct _vmx_vmcsrwfields_encodings	{
 unsigned int  encoding;
 unsigned int  fieldoffset;
} __attribute__((packed));



// VMX instruction INVVPID
//		Invalidate Translations Based on VPID
// INVVPID r32, m128
//returns 1 on success, 0 on failure

#define	VMX_INVVPID_INDIVIDUALADDRESS		0
#define VMX_INVVPID_SINGLECONTEXT			1
#define VMX_INVVPID_ALLCONTEXTS				2
#define VMX_INVVPID_SINGLECONTEXTGLOBAL		3


// VMX instruction INVEPT
//		Invalidate Translations Derived from EPT

#define	VMX_INVEPT_SINGLECONTEXT			1
#define VMX_INVEPT_GLOBAL					2




#endif //__ASSEMBLY__



#ifndef __ASSEMBLY__


//////
// external verification hooks for verification drivers
//////
extern void xmhfhwm_vdriver_sentinel(void);
extern void xmhfhwm_vdriver_slabep(void);
extern void xmhfhwm_vdriver_vhslabretaddr(void);
extern void xmhfhwm_vdriver_uhslabretaddr(void);
extern void hwm_vdriver_cpu_vmwrite(u32 encoding, u32 value);

//////
// cpu model variables and instruction implementations
//////
extern u32 xmhfhwm_cpu_gprs_eip;
extern u32 xmhfhwm_cpu_gprs_esp;
extern u32 xmhfhwm_cpu_gprs_ebp;

extern u32 xmhfhwm_cpu_gprs_eax;
extern u32 xmhfhwm_cpu_gprs_ebx;
extern u32 xmhfhwm_cpu_gprs_edx;
extern u32 xmhfhwm_cpu_gprs_ecx;
extern u32 xmhfhwm_cpu_gprs_esi;
extern u32 xmhfhwm_cpu_gprs_edi;

extern u32 xmhfhwm_cpu_eflags;

extern u32 xmhfhwm_cpu_cr3;

extern physmem_extent_t xmhfhwm_sysmemaccess_physmem_extents[32];
extern u32 xmhfhwm_sysmemaccess_physmem_extents_total;



extern void _impl_xmhfhwm_cpu_insn_hlt(void);
extern void _impl_xmhfhwm_cpu_insn_pushl_mesp(int index);
extern void _impl_xmhfhwm_cpu_insn_pushl_mem(u32 value);
extern u32 _impl_xmhfhwm_cpu_insn_popl_mem(void);

extern void _impl_xmhfhwm_cpu_insn_addl_imm_esp(u32 value);
extern void _impl_xmhfhwm_cpu_insn_movl_mesp_eax(u32 index);
extern void _impl_xmhfhwm_cpu_insn_movl_mesp_ebx(int index);
extern void _impl_xmhfhwm_cpu_insn_cmpl_imm_meax(u32 value, int index);
extern void _impl_xmhfhwm_cpu_insn_movl_imm_meax(u32 value, int index);
extern void _impl_xmhfhwm_cpu_insn_movl_meax_edx(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_meax_ecx(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_ecx_meax(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_edx_meax(int index);
extern void _impl_xmhfhwm_cpu_insn_bsrl_mesp_eax(int index);
extern void _impl_xmhfhwm_cpu_insn_pushl_ebx(void);
extern void _impl_xmhfhwm_cpu_insn_pushl_esi(void);
extern void _impl_xmhfhwm_cpu_insn_movl_mesp_ecx(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_mesp_edx(int index);

extern void _impl_xmhfhwm_cpu_insn_movl_mebx_ebx(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_mecx_ecx(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_medx_edx(int index);

extern void _impl_xmhfhwm_cpu_insn_cpuid(void);
extern void _impl_xmhfhwm_cpu_insn_movl_mesp_esi(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_eax_mesi(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_ebx_mesi(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_ecx_mesi(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_edx_mesi(int index);
extern void _impl_xmhfhwm_cpu_insn_popl_eax(void);
extern void _impl_xmhfhwm_cpu_insn_popl_esi(void);
extern void _impl_xmhfhwm_cpu_insn_popl_ebx(void);
extern void _impl_xmhfhwm_cpu_insn_cli(void);
extern void _impl_xmhfhwm_cpu_insn_sti(void);
extern void _impl_xmhfhwm_cpu_insn_subl_imm_esp(u32 value);
extern void _impl_xmhfhwm_cpu_insn_sgdt_mesp(int index);
extern void _impl_xmhfhwm_cpu_insn_xorl_eax_eax(void);
extern void _impl_xmhfhwm_cpu_insn_xorl_edx_edx(void);
extern void _impl_xmhfhwm_cpu_insn_sidt_mesp(int index);
extern void _impl_xmhfhwm_cpu_insn_getsec(void);
extern void _impl_xmhfhwm_cpu_insn_str_ax(void);
extern void _impl_xmhfhwm_cpu_insn_addl_eax_ecx(void);
extern void _impl_xmhfhwm_cpu_insn_movl_mecx_eax(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_mecx_edx(int index);
extern void _impl_xmhfhwm_cpu_insn_addl_imm_ecx(u32 value);
extern void _impl_xmhfhwm_cpu_insn_movl_edx_ecx(void);
extern void _impl_xmhfhwm_cpu_insn_andl_imm_edx(u32 value);
extern void _impl_xmhfhwm_cpu_insn_andl_imm_ecx(u32 value);
extern void _impl_xmhfhwm_cpu_insn_shl_imm_ecx(u32 value);
extern void _impl_xmhfhwm_cpu_insn_shr_imm_eax(u32 value);
extern void _impl_xmhfhwm_cpu_insn_orl_ecx_eax(void);
extern void _impl_xmhfhwm_cpu_insn_orl_edx_eax(void);
extern void _impl_xmhfhwm_cpu_insn_inb_dx_al(void);
extern void _impl_xmhfhwm_cpu_insn_inl_dx_eax(void);
extern void _impl_xmhfhwm_cpu_insn_movl_eax_mesp(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_imm_mesp(u32 value, int index);
extern void _impl_xmhfhwm_cpu_insn_invept_mesp_edx(int index);
extern void _impl_xmhfhwm_cpu_insn_movw_mesp_ax(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_imm_eax(u32 value);
extern void _impl_xmhfhwm_cpu_insn_invvpid_mesp_ecx(int index);
extern void _impl_xmhfhwm_cpu_insn_inw_dx_ax(void);
extern void _impl_xmhfhwm_cpu_insn_lgdt_mecx(int index);
extern void _impl_xmhfhwm_cpu_insn_lidt_mecx(int index);
extern void _impl_xmhfhwm_cpu_insn_ltr_ax(void);
extern void _impl_xmhfhwm_cpu_insn_outb_al_dx(void);
extern void _impl_xmhfhwm_cpu_insn_outl_eax_dx(void);
extern void _impl_xmhfhwm_cpu_insn_outw_ax_dx(void);
extern void _impl_xmhfhwm_cpu_insn_pause(void);
extern void _impl_xmhfhwm_cpu_insn_rdmsr(void);
extern void _impl_xmhfhwm_cpu_insn_rdtsc(void);
extern void _impl_xmhfhwm_cpu_insn_movl_cr0_eax(void);
extern void _impl_xmhfhwm_cpu_insn_movl_cr2_eax(void);
extern void _impl_xmhfhwm_cpu_insn_movl_cr3_eax(void);
extern void _impl_xmhfhwm_cpu_insn_movl_cr4_eax(void);
extern void _impl_xmhfhwm_cpu_insn_movl_esp_eax(void);
extern void _impl_xmhfhwm_cpu_insn_pushfl(void);

extern void _impl_xmhfhwm_cpu_insn_movl_cs_eax(void);
extern void _impl_xmhfhwm_cpu_insn_movl_ds_eax(void);
extern void _impl_xmhfhwm_cpu_insn_movl_es_eax(void);
extern void _impl_xmhfhwm_cpu_insn_movl_fs_eax(void);
extern void _impl_xmhfhwm_cpu_insn_movl_gs_eax(void);
extern void _impl_xmhfhwm_cpu_insn_movl_ss_eax(void);


extern void _impl_xmhfhwm_cpu_insn_btl_imm_mecx(u32 value, int index);
extern void _impl_xmhfhwm_cpu_insn_btrl_imm_mecx(u32 value, int index);
extern void _impl_xmhfhwm_cpu_insn_btsl_imm_mecx(u32 value, int index);


extern void _impl_xmhfhwm_cpu_insn_vmxon_mesp(int index);
extern void _impl_xmhfhwm_cpu_insn_vmwrite_eax_ecx(void);
extern void _impl_xmhfhwm_cpu_insn_vmread_ecx_eax(void);
extern void _impl_xmhfhwm_cpu_insn_vmclear_mesp(int index);
extern void _impl_xmhfhwm_cpu_insn_vmptrld_mesp(int index);


extern void _impl_xmhfhwm_cpu_insn_wbinvd(void);
extern void _impl_xmhfhwm_cpu_insn_movl_eax_cr0(void);
extern void _impl_xmhfhwm_cpu_insn_movl_eax_cr3(void);
extern void _impl_xmhfhwm_cpu_insn_movl_eax_cr4(void);
extern void _impl_xmhfhwm_cpu_insn_popfl(void);
extern void _impl_xmhfhwm_cpu_insn_wrmsr(void);

extern void _impl_xmhfhwm_cpu_insn_xgetbv(void);
extern void _impl_xmhfhwm_cpu_insn_xsetbv(void);

extern void _impl_xmhfhwm_cpu_insn_pushl_edi(void);
extern void _impl_xmhfhwm_cpu_insn_movl_mesp_edi(int index);

extern void _impl_xmhfhwm_cpu_insn_cld(void);
extern void _impl_xmhfhwm_cpu_insn_rep_movsb(void);
extern void _impl_xmhfhwm_cpu_insn_popl_edi(void);

extern void _impl_xmhfhwm_cpu_insn_andl_imm_eax(u32 value);

extern void _impl_xmhfhwm_cpu_insn_movl_mesi_eax(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_mesi_edx(int index);
extern void _impl_xmhfhwm_cpu_insn_movb_al_mesi(int index);
extern void _impl_xmhfhwm_cpu_insn_movw_ax_mesi(int index);

extern void _impl_xmhfhwm_cpu_insn_pushl_ebp(void);
extern void _impl_xmhfhwm_cpu_insn_movl_esp_edx(void);

extern void _impl_xmhfhwm_cpu_insn_pushl_eax(void);
extern void _impl_xmhfhwm_cpu_insn_pushl_edx(void);
extern void _impl_xmhfhwm_cpu_insn_pushl_edx(void);
extern void _impl_xmhfhwm_cpu_insn_movl_edx_esp(void);
extern void _impl_xmhfhwm_cpu_insn_popl_ebp(void);
extern void _impl_xmhfhwm_cpu_insn_pushl_ecx(void);
extern void _impl_xmhfhwm_cpu_insn_movl_eax_esp(void);
extern void _impl_xmhfhwm_cpu_insn_pushl_esp(void);
extern void _impl_xmhfhwm_cpu_insn_pushl_imm(u32 value);
extern void _impl_xmhfhwm_cpu_insn_popl_edx(void);
extern void _impl_xmhfhwm_cpu_insn_movl_esp_ecx(void);

extern void _impl_xmhfhwm_cpu_insn_vmlaunch(void);
extern void _impl_xmhfhwm_cpu_insn_pushal(void);
extern void _impl_xmhfhwm_cpu_insn_movw_imm_ax(u16 value);
extern void  _impl_xmhfhwm_cpu_insn_movw_ax_ds(void);
extern void  _impl_xmhfhwm_cpu_insn_movw_ax_es(void);


extern void _impl_xmhfhwm_cpu_insn_movl_meax_edi(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_meax_ebp(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_meax_ebx(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_meax_eax(int index);
extern void _impl_xmhfhwm_cpu_insn_movl_meax_esp(int index);
extern void  _impl_xmhfhwm_cpu_insn_vmresume(void);

extern void _impl_xmhfhwm_cpu_insn_movl_meax_esi(int index);
extern void _impl_xmhfhwm_cpu_insn_iretl(void);


//////
// CASM C to ASM call macros
//////

#define CASM_RET_EIP	0xDEADBEEF


#if defined (__XMHF_VERIFICATION__)
	#define CASM_FUNCCALL_PARAMSETUP(X)    ( \
		_impl_xmhfhwm_cpu_insn_pushl_mem((u32)X) \
		), \

	#define CASM_FUNCCALL_PARAMTEARDOWN(X)    ( \
		_impl_xmhfhwm_cpu_insn_addl_imm_esp(0x4) \
		), \

	#define CASM_FUNCCALL(fn_name, ...)   (\
	    PP_FOREACH(CASM_FUNCCALL_PARAMSETUP, (PP_REVERSEARGS(__VA_ARGS__))) \
	    (_impl_xmhfhwm_cpu_insn_pushl_mem((u32)CASM_RET_EIP)), \
	    fn_name(__VA_ARGS__), \
	    PP_FOREACH(CASM_FUNCCALL_PARAMTEARDOWN, (PP_REVERSEARGS(__VA_ARGS__))) \
	    (u64)(((u64)xmhfhwm_cpu_gprs_edx << 32) | xmhfhwm_cpu_gprs_eax) \
	    )\

#else

	#define CASM_FUNCCALL(fn_name, ...)   (\
	    fn_name(__VA_ARGS__) \
	    )\

#endif // defined



#endif //__ASSEMBLY__





//////
// CASM instruction macros
//////



// branch instructions
#define xmhfhwm_cpu_insn_jmp(x) __builtin_annot("jmp "#x" ");

#define xmhfhwm_cpu_insn_jmplabel(x) \
	__builtin_annot("jmp "#x" "); \
	if(1) goto x; \


#define xmhfhwm_cpu_insn_jmpl_eax() __builtin_annot("jmpl *%eax ");

#define xmhfhwm_cpu_insn_jc(x) \
	__builtin_annot("jc "#x" "); \
	if(xmhfhwm_cpu_eflags & EFLAGS_CF) goto x; \


#define xmhfhwm_cpu_insn_je(x) \
	__builtin_annot("je "#x" "); \
	if(xmhfhwm_cpu_eflags & EFLAGS_ZF) goto x; \


#define xmhfhwm_cpu_insn_jnc(x) \
	__builtin_annot("jnc "#x" "); \
	if(!(xmhfhwm_cpu_eflags & EFLAGS_CF)) goto x; \


#define xmhfhwm_cpu_insn_jnz(x) \
	__builtin_annot("jnz "#x" "); \
	if(!(xmhfhwm_cpu_eflags & EFLAGS_ZF)) goto x; \

#define xmhfhwm_cpu_insn_jbe(x) \
	__builtin_annot("jbe "#x" "); \
	if((xmhfhwm_cpu_eflags & EFLAGS_ZF) && (xmhfhwm_cpu_eflags & EFLAGS_CF)) goto x; \


#define xmhfhwm_cpu_insn_ja(x) \
	__builtin_annot("ja "#x" "); \
	if(!(xmhfhwm_cpu_eflags & EFLAGS_ZF) && !(xmhfhwm_cpu_eflags & EFLAGS_CF)) goto x; \

#define xmhfhwm_cpu_insn_int(x) __builtin_annot("int $"#x" ");

#define xmhfhwm_cpu_insn_call(x) __builtin_annot("call "#x" ");

#define xmhfhwm_cpu_insn_call_c_1p(fn_name, fn_p1_type) \
	__builtin_annot("call "#fn_name" "); \
	_impl_xmhfhwm_cpu_insn_pushl_mem(CASM_RET_EIP); \
	fn_name( (fn_p1_type) *((u32 *)(xmhfhwm_cpu_gprs_esp+4)) ); \

#define xmhfhwm_cpu_insn_call_c_2p(fn_name, fn_p1_type, fn_p2_type) \
	__builtin_annot("call "#fn_name" "); \
	_impl_xmhfhwm_cpu_insn_pushl_mem(CASM_RET_EIP); \
	fn_name( (fn_p1_type) *((u32 *)(xmhfhwm_cpu_gprs_esp+4)) , (fn_p2_type) *((u32 *)(xmhfhwm_cpu_gprs_esp+8)) ); \


#define xmhfhwm_cpu_insn_ret() \
	__builtin_annot("ret "); \
        xmhfhwm_cpu_gprs_eip = *(u32 *)xmhfhwm_cpu_gprs_esp; \
	xmhfhwm_cpu_gprs_esp += sizeof(u32); \
	return; \

#define xmhfhwm_cpu_insn_retu32() \
	__builtin_annot("ret "); \
        xmhfhwm_cpu_gprs_eip = *(u32 *)xmhfhwm_cpu_gprs_esp; \
	xmhfhwm_cpu_gprs_esp += sizeof(u32); \
	return xmhfhwm_cpu_gprs_eax; \

#define xmhfhwm_cpu_insn_retu64() \
	__builtin_annot("ret "); \
        xmhfhwm_cpu_gprs_eip = *(u32 *)xmhfhwm_cpu_gprs_esp; \
	xmhfhwm_cpu_gprs_esp += sizeof(u32); \
	return (u64)(((u64)xmhfhwm_cpu_gprs_edx << 32) | xmhfhwm_cpu_gprs_eax); \



#define xmhfhwm_cpu_insn_lret() __builtin_annot("lret ");


#define xmhfhwm_cpu_insn_jmpsentinel() \
	__builtin_annot("movl $0x02400000, %eax"); \
	__builtin_annot("jmpl *%eax "); \
	__builtin_annot("hlt "); \
	xmhfhwm_vdriver_sentinel(); \
	_impl_xmhfhwm_cpu_insn_hlt(); \


#define xmhfhwm_cpu_insn_jmpslabep() \
	__builtin_annot("jmpl *%eax "); \
	__builtin_annot("hlt "); \
	xmhfhwm_cpu_gprs_eip = xmhfhwm_cpu_gprs_eax; \
	xmhfhwm_vdriver_slabep(); \
	_impl_xmhfhwm_cpu_insn_hlt(); \


#define xmhfhwm_cpu_insn_jmpvhslabretaddr() \
	__builtin_annot("ret "); \
	__builtin_annot("hlt "); \
	xmhfhwm_cpu_gprs_eip = *(u32 *)xmhfhwm_cpu_gprs_esp; \
	xmhfhwm_cpu_gprs_esp += sizeof(u32); \
	xmhfhwm_vdriver_vhslabretaddr(); \
	_impl_xmhfhwm_cpu_insn_hlt(); \


#define xmhfhwm_cpu_insn_jmpuhslabretaddr() \
	__builtin_annot("sysexit "); \
	__builtin_annot("hlt "); \
	xmhfhwm_cpu_gprs_eip = xmhfhwm_cpu_gprs_edx; \
	xmhfhwm_cpu_gprs_esp = xmhfhwm_cpu_gprs_ecx; \
	xmhfhwm_vdriver_uhslabretaddr(); \
	_impl_xmhfhwm_cpu_insn_hlt(); \



// load/store instructions
#define xmhfhwm_cpu_insn_cld() \
	__builtin_annot("cld"); \
	_impl_xmhfhwm_cpu_insn_cld(); \

#define xmhfhwm_cpu_insn_rep_movsb() \
	__builtin_annot("rep movsb"); \
	_impl_xmhfhwm_cpu_insn_rep_movsb(); \


#define _xmhfhwm_cpu_insn_movl_imm_eax(x) \
	__builtin_annot("movl $"#x", %eax"); \
	_impl_xmhfhwm_cpu_insn_movl_imm_eax(x); \

#define xmhfhwm_cpu_insn_movl_imm_eax(x) _xmhfhwm_cpu_insn_movl_imm_eax(x)

#define _xmhfhwm_cpu_insn_movl_imm_ebx(x) __builtin_annot("movl $"#x", %ebx");
#define xmhfhwm_cpu_insn_movl_imm_ebx(x) _xmhfhwm_cpu_insn_movl_imm_ebx(x)

#define _xmhfhwm_cpu_insn_movl_imm_ecx(x) __builtin_annot("movl $"#x", %ecx");
#define xmhfhwm_cpu_insn_movl_imm_ecx(x) _xmhfhwm_cpu_insn_movl_imm_ecx(x)

#define _xmhfhwm_cpu_insn_movl_imm_edi(x) __builtin_annot("movl $"#x", %edi");
#define xmhfhwm_cpu_insn_movl_imm_edi(x) _xmhfhwm_cpu_insn_movl_imm_edi(x)


#define _xmhfhwm_cpu_insn_movw_imm_ax(x) \
	__builtin_annot("movw $"#x", %ax"); \
	_impl_xmhfhwm_cpu_insn_movw_imm_ax(x); \

#define xmhfhwm_cpu_insn_movw_imm_ax(x) _xmhfhwm_cpu_insn_movw_imm_ax(x)

#define xmhfhwm_cpu_insn_movl_imm_mesp(x,y) \
	__builtin_annot("movl $"#x", "#y"(%esp) "); \
	_impl_xmhfhwm_cpu_insn_movl_imm_mesp(x,y); \


#define _xmhfhwm_cpu_insn_movl_imm_meax(x,y) \
	__builtin_annot("movl $"#x", "#y"(%eax) "); \
	_impl_xmhfhwm_cpu_insn_movl_imm_meax(x,y); \

#define xmhfhwm_cpu_insn_movl_imm_meax(x,y) _xmhfhwm_cpu_insn_movl_imm_meax(x,y)

#define _xmhfhwm_cpu_insn_cmpl_imm_meax(x,y) \
	__builtin_annot("cmpl $"#x", "#y"(%eax) "); \
	_impl_xmhfhwm_cpu_insn_cmpl_imm_meax(x,y); \


#define xmhfhwm_cpu_insn_cmpl_imm_meax(x,y) _xmhfhwm_cpu_insn_cmpl_imm_meax(x,y)


#define xmhfhwm_cpu_insn_movl_ecx_meax(x) \
	__builtin_annot("movl %ecx, "#x"(%eax) "); \
	_impl_xmhfhwm_cpu_insn_movl_ecx_meax(x); \


#define xmhfhwm_cpu_insn_movl_edx_meax(x) \
	__builtin_annot("movl %edx, "#x"(%eax) "); \
        _impl_xmhfhwm_cpu_insn_movl_edx_meax(x); \



#define xmhfhwm_cpu_insn_movl_eax_mesp(x) \
	__builtin_annot("movl %eax, "#x"(%esp) "); \
	_impl_xmhfhwm_cpu_insn_movl_eax_mesp(x); \


#define xmhfhwm_cpu_insn_movl_eax_esp() \
	__builtin_annot("movl %eax, %esp "); \
	_impl_xmhfhwm_cpu_insn_movl_eax_esp(); \

#define xmhfhwm_cpu_insn_movl_edx_esp() \
	__builtin_annot("movl %edx, %esp "); \
        _impl_xmhfhwm_cpu_insn_movl_edx_esp(); \


#define xmhfhwm_cpu_insn_movl_mesp_eax(x) \
	__builtin_annot("movl "#x"(%esp), %eax "); \
	_impl_xmhfhwm_cpu_insn_movl_mesp_eax(x); \


#define xmhfhwm_cpu_insn_movw_mesp_ax(x) \
	__builtin_annot("movw "#x"(%esp), %ax ");\
	_impl_xmhfhwm_cpu_insn_movw_mesp_ax(x); \


#define xmhfhwm_cpu_insn_movl_mesp_ebx(x) \
	__builtin_annot("movl "#x"(%esp), %ebx "); \
	_impl_xmhfhwm_cpu_insn_movl_mesp_ebx(x); \


#define xmhfhwm_cpu_insn_movl_mesp_ecx(x) \
	__builtin_annot("movl "#x"(%esp), %ecx "); \
	_impl_xmhfhwm_cpu_insn_movl_mesp_ecx(x); \


#define xmhfhwm_cpu_insn_movl_mesp_edx(x) \
	__builtin_annot("movl "#x"(%esp), %edx "); \
	_impl_xmhfhwm_cpu_insn_movl_mesp_edx(x); \


#define xmhfhwm_cpu_insn_movl_mesp_esi(x) \
	__builtin_annot("movl "#x"(%esp), %esi "); \
	_impl_xmhfhwm_cpu_insn_movl_mesp_esi(x); \


#define xmhfhwm_cpu_insn_movl_mesp_edi(x) \
	__builtin_annot("movl "#x"(%esp), %edi "); \
	_impl_xmhfhwm_cpu_insn_movl_mesp_edi(x); \


#define xmhfhwm_cpu_insn_movl_mecx_eax(x) \
	__builtin_annot("movl "#x"(%ecx), %eax "); \
	_impl_xmhfhwm_cpu_insn_movl_mecx_eax(x); \

#define xmhfhwm_cpu_insn_movl_mecx_edx(x) \
	__builtin_annot("movl "#x"(%ecx), %edx "); \
	_impl_xmhfhwm_cpu_insn_movl_mecx_edx(x); \

#define xmhfhwm_cpu_insn_movl_eax_mecx(x) __builtin_annot("movl %eax, "#x"(%ecx) ");
#define xmhfhwm_cpu_insn_movl_edx_mecx(x) __builtin_annot("movl %edx, "#x"(%ecx) ");

#define xmhfhwm_cpu_insn_movl_eax_mesi(x) \
	__builtin_annot("movl %eax, "#x"(%esi) "); \
	_impl_xmhfhwm_cpu_insn_movl_eax_mesi(x); \


#define xmhfhwm_cpu_insn_movl_ebx_mesi(x) \
	__builtin_annot("movl %ebx, "#x"(%esi) "); \
	_impl_xmhfhwm_cpu_insn_movl_ebx_mesi(x); \

#define xmhfhwm_cpu_insn_movl_ecx_mesi(x) \
	__builtin_annot("movl %ecx, "#x"(%esi) "); \
	_impl_xmhfhwm_cpu_insn_movl_ecx_mesi(x); \


#define xmhfhwm_cpu_insn_movl_edx_mesi(x) \
	__builtin_annot("movl %edx, "#x"(%esi) "); \
	_impl_xmhfhwm_cpu_insn_movl_edx_mesi(x); \


#define xmhfhwm_cpu_insn_movl_meax_eax(x) \
	__builtin_annot("movl "#x"(%eax), %eax "); \
        _impl_xmhfhwm_cpu_insn_movl_meax_eax(x); \


#define xmhfhwm_cpu_insn_movl_meax_ebx(x) \
	__builtin_annot("movl "#x"(%eax), %ebx "); \
	_impl_xmhfhwm_cpu_insn_movl_meax_ebx(x); \


#define xmhfhwm_cpu_insn_movl_meax_ecx(x) \
	__builtin_annot("movl "#x"(%eax), %ecx "); \
	_impl_xmhfhwm_cpu_insn_movl_meax_ecx(x); \

#define xmhfhwm_cpu_insn_movl_meax_edx(x) \
	__builtin_annot("movl "#x"(%eax), %edx "); \
	_impl_xmhfhwm_cpu_insn_movl_meax_edx(x); \


#define xmhfhwm_cpu_insn_movl_meax_edi(x) \
	__builtin_annot("movl "#x"(%eax), %edi "); \
	_impl_xmhfhwm_cpu_insn_movl_meax_edi(x); \


#define xmhfhwm_cpu_insn_movl_meax_esi(x) \
	__builtin_annot("movl "#x"(%eax), %esi "); \
	_impl_xmhfhwm_cpu_insn_movl_meax_esi(x); \


#define xmhfhwm_cpu_insn_movl_meax_ebp(x) \
	__builtin_annot("movl "#x"(%eax), %ebp "); \
        _impl_xmhfhwm_cpu_insn_movl_meax_ebp(x); \

#define xmhfhwm_cpu_insn_movl_meax_esp(x) \
	__builtin_annot("movl "#x"(%eax), %esp "); \
        _impl_xmhfhwm_cpu_insn_movl_meax_esp(x); \


#define xmhfhwm_cpu_insn_movl_mebx_ebx(x) \
	__builtin_annot("movl "#x"(%ebx), %ebx "); \
	_impl_xmhfhwm_cpu_insn_movl_mebx_ebx(x); \


#define xmhfhwm_cpu_insn_movl_mecx_ecx(x) \
	__builtin_annot("movl "#x"(%ecx), %ecx "); \
	_impl_xmhfhwm_cpu_insn_movl_mecx_ecx(x); \


#define xmhfhwm_cpu_insn_movl_medx_edx(x) \
	__builtin_annot("movl "#x"(%edx), %edx "); \
	_impl_xmhfhwm_cpu_insn_movl_medx_edx(x); \

#define xmhfhwm_cpu_insn_movl_medi_edi(x) __builtin_annot("movl "#x"(%edi), %edi ");

//////

#define xmhfhwm_cpu_insn_movl_mesi_eax(x) \
	__builtin_annot("movl "#x"(%esi), %eax "); \
	_impl_xmhfhwm_cpu_insn_movl_mesi_eax(x); \

#define xmhfhwm_cpu_insn_movl_mesi_edx(x) \
	__builtin_annot("movl "#x"(%esi), %edx "); \
	_impl_xmhfhwm_cpu_insn_movl_mesi_edx(x); \

#define	xmhfhwm_cpu_insn_movb_al_mesi(x) \
	__builtin_annot("movb %al,"#x"(%esi)"); \
	_impl_xmhfhwm_cpu_insn_movb_al_mesi(x); \

#define	xmhfhwm_cpu_insn_movw_ax_mesi(x) \
	__builtin_annot("movw %ax,"#x"(%esi)"); \
	_impl_xmhfhwm_cpu_insn_movw_ax_mesi(x); \




//////

#define xmhfhwm_cpu_insn_movl_edx_ecx() \
	__builtin_annot("movl %edx, %ecx "); \
	_impl_xmhfhwm_cpu_insn_movl_edx_ecx(); \


#define xmhfhwm_cpu_insn_movl_edi_ebx() __builtin_annot("movl %edi, %ebx ");

#define xmhfhwm_cpu_insn_movl_esp_eax() \
	__builtin_annot("movl %esp, %eax "); \
	_impl_xmhfhwm_cpu_insn_movl_esp_eax(); \


#define xmhfhwm_cpu_insn_movl_esp_ecx() \
	__builtin_annot("movl %esp, %ecx "); \
	_impl_xmhfhwm_cpu_insn_movl_esp_ecx(); \


#define xmhfhwm_cpu_insn_movl_esp_edx() \
	__builtin_annot("movl %esp, %edx "); \
	_impl_xmhfhwm_cpu_insn_movl_esp_edx(); \


#define xmhfhwm_cpu_insn_movl_mebxeax_eax(x) __builtin_annot("movl (%ebx, %eax, "#x"), %eax ");




#define xmhfhwm_cpu_insn_pushl_ebp() \
	__builtin_annot("pushl %ebp "); \
	_impl_xmhfhwm_cpu_insn_pushl_ebp(); \


#define xmhfhwm_cpu_insn_pushl_edi() \
	__builtin_annot("pushl %edi "); \
	_impl_xmhfhwm_cpu_insn_pushl_edi(); \


#define xmhfhwm_cpu_insn_pushl_esi() \
	__builtin_annot("pushl %esi "); \
        _impl_xmhfhwm_cpu_insn_pushl_esi(); \

#define xmhfhwm_cpu_insn_pushl_eax() \
	__builtin_annot("pushl %eax "); \
	_impl_xmhfhwm_cpu_insn_pushl_eax(); \


#define xmhfhwm_cpu_insn_pushl_ebx() \
	__builtin_annot("pushl %ebx "); \
	_impl_xmhfhwm_cpu_insn_pushl_ebx(); \


#define xmhfhwm_cpu_insn_pushl_ecx() \
	__builtin_annot("pushl %ecx "); \
	_impl_xmhfhwm_cpu_insn_pushl_ecx(); \


#define xmhfhwm_cpu_insn_pushl_edx() \
	__builtin_annot("pushl %edx "); \
	_impl_xmhfhwm_cpu_insn_pushl_edx(); \

#define xmhfhwm_cpu_insn_pushl_esp() \
	__builtin_annot("pushl %esp "); \
	_impl_xmhfhwm_cpu_insn_pushl_esp(); \


#define xmhfhwm_cpu_insn_pushl_mesp(x) \
	__builtin_annot("pushl "#x"(%esp) ");\
	_impl_xmhfhwm_cpu_insn_pushl_mesp(x);\

#define xmhfhwm_cpu_insn_popl_eax() \
	__builtin_annot("popl %eax "); \
        _impl_xmhfhwm_cpu_insn_popl_eax(); \


#define xmhfhwm_cpu_insn_popl_ebx() \
	__builtin_annot("popl %ebx "); \
        _impl_xmhfhwm_cpu_insn_popl_ebx(); \


#define xmhfhwm_cpu_insn_popl_ecx() __builtin_annot("popl %ecx ");

#define xmhfhwm_cpu_insn_popl_edx() \
	__builtin_annot("popl %edx "); \
        _impl_xmhfhwm_cpu_insn_popl_edx(); \


#define xmhfhwm_cpu_insn_popl_esi() \
	__builtin_annot("popl %esi "); \
        _impl_xmhfhwm_cpu_insn_popl_esi(); \


#define xmhfhwm_cpu_insn_popl_edi() \
	__builtin_annot("popl %edi "); \
        _impl_xmhfhwm_cpu_insn_popl_edi(); \

#define xmhfhwm_cpu_insn_popl_ebp() \
	__builtin_annot("popl %ebp "); \
	_impl_xmhfhwm_cpu_insn_popl_ebp(); \


#define xmhfhwm_cpu_insn_pushl_imm(x) \
	__builtin_annot("pushl $"#x" "); \
	_impl_xmhfhwm_cpu_insn_pushl_imm(x); \


#define xmhfhwm_cpu_insn_pushl_mem(x) \
	__builtin_annot("pushl "#x" "); \
	_impl_xmhfhwm_cpu_insn_pushl_mem(x);\

#define xmhfhwm_cpu_insn_popl_mem(x) \
	__builtin_annot("popl "#x" "); \
	x = _impl_xmhfhwm_cpu_insn_popl_mem();\


// arithmetic/logical
#define xmhfhwm_cpu_insn_xorl_eax_eax() \
	__builtin_annot("xorl %eax, %eax "); \
	_impl_xmhfhwm_cpu_insn_xorl_eax_eax(); \

#define xmhfhwm_cpu_insn_xorl_ebx_ebx() __builtin_annot("xorl %ebx, %ebx ");

#define xmhfhwm_cpu_insn_xorl_edx_edx() \
	__builtin_annot("xorl %edx, %edx "); \
	_impl_xmhfhwm_cpu_insn_xorl_edx_edx(); \



#define xmhfhwm_cpu_insn_addl_mesp_ecx(x) __builtin_annot("addl "#x"(%esp), %ecx ");

#define xmhfhwm_cpu_insn_addl_imm_esp(x) \
	__builtin_annot("addl $"#x", %esp "); \
	_impl_xmhfhwm_cpu_insn_addl_imm_esp(x); \

#define xmhfhwm_cpu_insn_subl_imm_esp(x) \
	__builtin_annot("subl $"#x", %esp "); \
	_impl_xmhfhwm_cpu_insn_subl_imm_esp(x); \

#define xmhfhwm_cpu_insn_addl_eax_ecx() \
	__builtin_annot("addl %eax, %ecx"); \
	_impl_xmhfhwm_cpu_insn_addl_eax_ecx(); \

#define xmhfhwm_cpu_insn_addl_ecx_eax() __builtin_annot("addl %ecx, %eax");

#define xmhfhwm_cpu_insn_addl_imm_ecx(x) \
	__builtin_annot("addl $"#x", %ecx "); \
	_impl_xmhfhwm_cpu_insn_addl_imm_ecx(x); \


#define _xmhfhwm_cpu_insn_addl_imm_eax(x) __builtin_annot("addl $"#x", %eax ");
#define xmhfhwm_cpu_insn_addl_imm_eax(x) _xmhfhwm_cpu_insn_addl_imm_eax(x)

#define xmhfhwm_cpu_insn_andl_imm_edx(x) \
	__builtin_annot("andl $"#x", %edx "); \
	_impl_xmhfhwm_cpu_insn_andl_imm_edx(x); \


#define xmhfhwm_cpu_insn_andl_imm_ecx(x) \
	__builtin_annot("andl $"#x", %ecx "); \
	_impl_xmhfhwm_cpu_insn_andl_imm_ecx(x); \


#define xmhfhwm_cpu_insn_andl_imm_eax(x) \
	__builtin_annot("andl $"#x", %eax "); \
	_impl_xmhfhwm_cpu_insn_andl_imm_eax(x); \


#define xmhfhwm_cpu_insn_shl_imm_ecx(x) \
	__builtin_annot("shl $"#x", %ecx "); \
	_impl_xmhfhwm_cpu_insn_shl_imm_ecx(x); \

#define xmhfhwm_cpu_insn_shr_imm_eax(x) \
	__builtin_annot("shr $"#x", %eax "); \
	_impl_xmhfhwm_cpu_insn_shr_imm_eax(x); \


#define xmhfhwm_cpu_insn_orl_ecx_eax() \
	__builtin_annot("orl %ecx, %eax "); \
	_impl_xmhfhwm_cpu_insn_orl_ecx_eax(); \

#define xmhfhwm_cpu_insn_orl_edx_eax() \
	__builtin_annot("orl %edx, %eax "); \
	_impl_xmhfhwm_cpu_insn_orl_edx_eax(); \

#define xmhfhwm_cpu_insn_orl_imm_eax(x) __builtin_annot("orl $"#x", %eax ");
#define xmhfhwm_cpu_insn_orl_imm_ecx(x) __builtin_annot("orl $"#x", %ecx ");


#define xmhfhwm_cpu_insn_btl_imm_mecx(x,y) \
	__builtin_annot("btl $"#x", "#y"(%ecx) "); \
	_impl_xmhfhwm_cpu_insn_btl_imm_mecx(x,y); \

#define xmhfhwm_cpu_insn_btrl_imm_mecx(x,y) \
	__builtin_annot("btrl $"#x", "#y"(%ecx) "); \
	_impl_xmhfhwm_cpu_insn_btrl_imm_mecx(x,y); \

#define xmhfhwm_cpu_insn_btsl_imm_mecx(x,y) \
	__builtin_annot("btsl $"#x", "#y"(%ecx) "); \
	_impl_xmhfhwm_cpu_insn_btsl_imm_mecx(x,y); \


#define xmhfhwm_cpu_insn_bsrl_mesp_eax(x) \
	__builtin_annot("bsrl "#x"(%esp), %eax "); \
	_impl_xmhfhwm_cpu_insn_bsrl_mesp_eax(x); \


#define xmhfhwm_cpu_insn_mull_ecx() __builtin_annot("mull %ecx ");


//segment registers
#define xmhfhwm_cpu_insn_movl_cs_eax() \
	__builtin_annot("movl %cs, %eax "); \
	_impl_xmhfhwm_cpu_insn_movl_cs_eax(); \

#define xmhfhwm_cpu_insn_movl_ds_eax() \
	__builtin_annot("movl %ds, %eax "); \
	_impl_xmhfhwm_cpu_insn_movl_ds_eax(); \

#define xmhfhwm_cpu_insn_movl_es_eax() \
	__builtin_annot("movl %es, %eax "); \
	_impl_xmhfhwm_cpu_insn_movl_es_eax(); \

#define xmhfhwm_cpu_insn_movl_fs_eax() \
	__builtin_annot("movl %fs, %eax "); \
	_impl_xmhfhwm_cpu_insn_movl_fs_eax(); \

#define xmhfhwm_cpu_insn_movl_gs_eax() \
	__builtin_annot("movl %gs, %eax "); \
	_impl_xmhfhwm_cpu_insn_movl_gs_eax(); \

#define xmhfhwm_cpu_insn_movl_ss_eax() \
	__builtin_annot("movl %ss, %eax "); \
	_impl_xmhfhwm_cpu_insn_movl_ss_eax(); \

#define xmhfhwm_cpu_insn_movw_ds_ax() __builtin_annot("movw %ds, %ax ");
#define xmhfhwm_cpu_insn_movw_ax_ds() \
	__builtin_annot("movw %ax, %ds "); \
        _impl_xmhfhwm_cpu_insn_movw_ax_ds(); \

#define xmhfhwm_cpu_insn_movw_ax_es() \
	__builtin_annot("movw %ax, %es "); \
        _impl_xmhfhwm_cpu_insn_movw_ax_es(); \

#define xmhfhwm_cpu_insn_movw_ax_fs() __builtin_annot("movw %ax, %fs ");
#define xmhfhwm_cpu_insn_movw_ax_gs() __builtin_annot("movw %ax, %gs ");
#define xmhfhwm_cpu_insn_movw_ax_ss() __builtin_annot("movw %ax, %ss ");

//control registers
#define xmhfhwm_cpu_insn_movl_cr0_eax() \
	__builtin_annot("movl %cr0, %eax "); \
	_impl_xmhfhwm_cpu_insn_movl_cr0_eax(); \


#define xmhfhwm_cpu_insn_movl_eax_cr0() \
	__builtin_annot("movl %eax, %cr0 "); \
	_impl_xmhfhwm_cpu_insn_movl_eax_cr0(); \


#define xmhfhwm_cpu_insn_movl_cr2_eax() \
	__builtin_annot("movl %cr2, %eax "); \
	_impl_xmhfhwm_cpu_insn_movl_cr2_eax(); \

#define xmhfhwm_cpu_insn_movl_cr3_eax() \
	__builtin_annot("movl %cr3, %eax "); \
	_impl_xmhfhwm_cpu_insn_movl_cr3_eax(); \


#define xmhfhwm_cpu_insn_movl_eax_cr3() \
	__builtin_annot("movl %eax, %cr3 "); \
	_impl_xmhfhwm_cpu_insn_movl_eax_cr3(); \

#define xmhfhwm_cpu_insn_movl_ebx_cr3() __builtin_annot("movl %ebx, %cr3 ");

#define xmhfhwm_cpu_insn_movl_cr4_eax() \
	__builtin_annot("movl %cr4, %eax "); \
	_impl_xmhfhwm_cpu_insn_movl_cr4_eax(); \

#define xmhfhwm_cpu_insn_movl_eax_cr4() \
	__builtin_annot("movl %eax, %cr4 "); \
	_impl_xmhfhwm_cpu_insn_movl_eax_cr4(); \


//other instructions
#define xmhfhwm_cpu_insn_pause() \
	__builtin_annot("pause "); \
	_impl_xmhfhwm_cpu_insn_pause(); \


#define xmhfhwm_cpu_insn_cpuid() \
	__builtin_annot("cpuid "); \
	_impl_xmhfhwm_cpu_insn_cpuid(); \

#define xmhfhwm_cpu_insn_pushfl() \
	__builtin_annot("pushfl "); \
	_impl_xmhfhwm_cpu_insn_pushfl(); \


#define xmhfhwm_cpu_insn_popfl() \
	__builtin_annot("popfl "); \
	_impl_xmhfhwm_cpu_insn_popfl(); \


#define xmhfhwm_cpu_insn_rdtsc() \
	__builtin_annot("rdtsc "); \
	_impl_xmhfhwm_cpu_insn_rdtsc(); \


#define xmhfhwm_cpu_insn_pushal() \
	__builtin_annot("pushal "); \
	_impl_xmhfhwm_cpu_insn_pushal(); \


#define xmhfhwm_cpu_insn_popal() __builtin_annot("popal ");

// system instructions
#define xmhfhwm_cpu_insn_hlt() \
	__builtin_annot("hlt "); \
	_impl_xmhfhwm_cpu_insn_hlt() \

#define xmhfhwm_cpu_insn_cli() \
	__builtin_annot("cli "); \
	_impl_xmhfhwm_cpu_insn_cli(); \

#define xmhfhwm_cpu_insn_sti() \
	__builtin_annot("sti "); \
	_impl_xmhfhwm_cpu_insn_sti(); \

#define xmhfhwm_cpu_insn_inb_dx_al() \
	__builtin_annot("inb %dx, %al "); \
	_impl_xmhfhwm_cpu_insn_inb_dx_al(); \

#define xmhfhwm_cpu_insn_inw_dx_ax() \
	__builtin_annot("inw %dx, %ax "); \
	_impl_xmhfhwm_cpu_insn_inw_dx_ax(); \


#define xmhfhwm_cpu_insn_inl_dx_eax() \
	__builtin_annot("inl %dx, %eax "); \
	_impl_xmhfhwm_cpu_insn_inl_dx_eax(); \


#define xmhfhwm_cpu_insn_outb_al_dx() \
	__builtin_annot("outb %al, %dx "); \
	_impl_xmhfhwm_cpu_insn_outb_al_dx(); \


#define xmhfhwm_cpu_insn_outw_ax_dx() \
	__builtin_annot("outw %ax, %dx "); \
	_impl_xmhfhwm_cpu_insn_outw_ax_dx(); \


#define xmhfhwm_cpu_insn_outl_eax_dx() \
	__builtin_annot("outl %eax, %dx "); \
	_impl_xmhfhwm_cpu_insn_outl_eax_dx(); \


#define xmhfhwm_cpu_insn_rdmsr() \
	__builtin_annot("rdmsr "); \
	_impl_xmhfhwm_cpu_insn_rdmsr(); \


#define xmhfhwm_cpu_insn_wrmsr() \
	__builtin_annot("wrmsr "); \
	_impl_xmhfhwm_cpu_insn_wrmsr(); \


#define xmhfhwm_cpu_insn_wbinvd() \
	__builtin_annot("wbinvd "); \
	_impl_xmhfhwm_cpu_insn_wbinvd(); \

#define xmhfhwm_cpu_insn_invlpg_mesp(x) __builtin_annot("invlpg "#x"(%esp) ");

#define xmhfhwm_cpu_insn_sgdt_mesp(x) \
	__builtin_annot("sgdt "#x"(%esp) "); \
	_impl_xmhfhwm_cpu_insn_sgdt_mesp(x); \


#define xmhfhwm_cpu_insn_str_ax() \
	__builtin_annot("str %ax "); \
	_impl_xmhfhwm_cpu_insn_str_ax(); \


#define xmhfhwm_cpu_insn_sidt_mesp(x) \
	__builtin_annot("sidt "#x"(%esp) "); \
	_impl_xmhfhwm_cpu_insn_sidt_mesp(x); \


#define xmhfhwm_cpu_insn_lidt_mecx(x) \
	__builtin_annot("lidt "#x"(%ecx) "); \
	_impl_xmhfhwm_cpu_insn_lidt_mecx(x); \


#define xmhfhwm_cpu_insn_ltr_ax() \
	__builtin_annot("ltr %ax "); \
	_impl_xmhfhwm_cpu_insn_ltr_ax(); \


#define xmhfhwm_cpu_insn_lgdt_mecx(x) \
	__builtin_annot("lgdt "#x"(%ecx) "); \
	_impl_xmhfhwm_cpu_insn_lgdt_mecx(x); \

#define xmhfhwm_cpu_insn_lock() \
	__builtin_annot("lock "); \

#define xmhfhwm_cpu_insn_xsetbv() \
	__builtin_annot("xsetbv "); \
	_impl_xmhfhwm_cpu_insn_xsetbv(); \

#define xmhfhwm_cpu_insn_xgetbv() \
	__builtin_annot("xgetbv "); \
	_impl_xmhfhwm_cpu_insn_xgetbv(); \

#define xmhfhwm_cpu_insn_iretl() \
	__builtin_annot("iretl "); \
	_impl_xmhfhwm_cpu_insn_iretl();

#define xmhfhwm_cpu_insn_sysexit() \
	__builtin_annot("sysexit "); \
	xmhfhwm_cpu_gprs_eip = xmhfhwm_cpu_gprs_edx; \
	xmhfhwm_cpu_gprs_esp = xmhfhwm_cpu_gprs_ecx; \
	xmhfhwm_vdriver_slabep(); \
	_impl_xmhfhwm_cpu_insn_hlt(); \

#define xmhfhwm_cpu_insn_sysenter() __builtin_annot("sysenter ");


//TXT
#define xmhfhwm_cpu_insn_getsec() \
	__builtin_annot(IA32_GETSEC_OPCODE); \
	_impl_xmhfhwm_cpu_insn_getsec(); \



// vmx instructions
#define xmhfhwm_cpu_insn_vmlaunch() \
	__builtin_annot("vmlaunch "); \
        _impl_xmhfhwm_cpu_insn_vmlaunch(); \

#define xmhfhwm_cpu_insn_vmxon_mesp(x) \
	__builtin_annot("vmxon "#x"(%esp) "); \
	_impl_xmhfhwm_cpu_insn_vmxon_mesp(x); \

#define xmhfhwm_cpu_insn_vmwrite_eax_ecx() \
	__builtin_annot("vmwrite %eax, %ecx "); \
	_impl_xmhfhwm_cpu_insn_vmwrite_eax_ecx(); \

#define xmhfhwm_cpu_insn_vmread_ecx_eax() \
	__builtin_annot("vmread %ecx, %eax"); \
        _impl_xmhfhwm_cpu_insn_vmread_ecx_eax(); \


#define xmhfhwm_cpu_insn_vmclear_mesp(x) \
	__builtin_annot("vmclear "#x"(%esp) "); \
	_impl_xmhfhwm_cpu_insn_vmclear_mesp(x); \


#define xmhfhwm_cpu_insn_vmptrld_mesp(x) \
	__builtin_annot("vmptrld "#x"(%esp) "); \
	_impl_xmhfhwm_cpu_insn_vmptrld_mesp(x); \


#define xmhfhwm_cpu_insn_invvpid_mesp_ecx(x) \
	__builtin_annot("invvpid "#x"(%esp), %ecx"); \
	_impl_xmhfhwm_cpu_insn_invvpid_mesp_ecx(x); \


#define xmhfhwm_cpu_insn_invept_mesp_edx(x) \
	__builtin_annot("invept "#x"(%esp), %edx "); \
	_impl_xmhfhwm_cpu_insn_invept_mesp_edx(x); \


#define xmhfhwm_cpu_insn_vmresume() \
	__builtin_annot("vmresume "); \
        _impl_xmhfhwm_cpu_insn_vmresume(); \



#endif /* __XMHFHWM_CPU_H__ */


