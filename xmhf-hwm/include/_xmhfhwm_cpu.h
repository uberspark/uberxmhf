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


/*typedef union {
    u64	raw;
    struct {
        u32 vcnt        : 8;    // num variable MTRR pairs
        u32 fix         : 1;    // fixed range MTRRs are supported
        u32 reserved1   : 1;
        u32 wc          : 1;    // write-combining mem type supported
        u32 reserved2   : 32;
        u32 reserved3   : 21;
    } __attribute__((packed)) fields;
} __attribute__((packed)) mtrr_cap_t;
*/

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


/*typedef union {
    u64	raw;
    struct {
        u32 type        : 8;
        u32 reserved1   : 2;
        u32 fe          : 1;    // fixed MTRR enable
        u32 e           : 1;    // (all) MTRR enable
        u32 reserved2   : 32;
        u32 reserved3   : 20;
    } __attribute__((packed)) fields;
} __attribute__((packed)) mtrr_def_type_t;
*/

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



/*typedef union {
    u64	raw;
    struct {
        u32 type      : 8;
        u32 reserved1 : 4;
        // TBD: the end of base really depends on MAXPHYADDR, but since
        // the MTRRs are set for SINIT and it must be <4GB, can use 24b
        u32 base      : 24;
        u32 reserved2 : 28;
    } __attribute__((packed)) fields;
} __attribute__((packed)) mtrr_physbase_t;
*/

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




/*typedef union {
    u64	raw;
    struct {
        u32 reserved1 : 11;
        u32 v         : 1;      // valid
        // TBD: the end of mask really depends on MAXPHYADDR, but since
        // the MTRRs are set for SINIT and it must be <4GB, can use 24b
        u32 mask      : 24;
        u32 reserved2 : 28;
    } __attribute__((packed)) fields;
} __attribute__((packed)) mtrr_physmask_t;
*/

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



/* current procs only have 8, so this should hold us for a while */
#define MAX_VARIABLE_MTRRS      16



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

//*
/*
x86_64
typedef struct {
  u16 isrLow;
  u16 isrSelector;
  u8  count;
  u8  type;
  u16 isrHigh;
  u32 offset3263;
  u32 reserved;
} __attribute__ ((packed)) idtentry_t;
*/

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


//arch. specific
//---platform
#define MAX_MEMORYTYPE_ENTRIES    98    //8*11 fixed MTRRs and 10 variable MTRRs
#define MAX_FIXED_MEMORYTYPE_ENTRIES  88
#define MAX_VARIABLE_MEMORYTYPE_ENTRIES 10


//---platform
//total number of FIXED and VARIABLE MTRRs on current x86 platforms
#define NUM_MTRR_MSRS		31

#ifndef __ASSEMBLY__

typedef struct {
  u32 eip;
  u32 cs;
  u32 eflags;
} __attribute__((packed)) INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE;

//---platform
typedef struct {
  u32 errorcode;
  u32 eip;
  u32 cs;
  u32 eflags;
} __attribute__((packed)) INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE;

#endif //__ASSEMBLY__

//---platform
#define IA32_VMX_MSRCOUNT   								12


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

/* x86_64
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
*/

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




/* x86_64
//*
//x86 GDT descriptor type
typedef struct {
		u16 size;
		u64 base;
} __attribute__((packed)) arch_x86_gdtdesc_t;

//*
//x86 IDT descriptor type
typedef struct {
		u16 size;
		u64 base;
} __attribute__((packed)) arch_x86_idtdesc_t;

//*
//TSS descriptor (partial)
typedef struct __tss {
	u32 reserved;
	u64 rsp0;
} __attribute__((packed)) tss_t;
*/


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
} __attribute__((packed)) tss_t;





//////


// branch instructions
#define xmhfhwm_cpu_insn_jmp(x) __builtin_annot("jmp "#x" ");
#define xmhfhwm_cpu_insn_jmpl_eax() __builtin_annot("jmpl *%eax ");
#define xmhfhwm_cpu_insn_jc(x) __builtin_annot("jc "#x" ");
#define xmhfhwm_cpu_insn_je(x) __builtin_annot("je "#x" ");
#define xmhfhwm_cpu_insn_jnc(x) __builtin_annot("jnc "#x" ");
#define xmhfhwm_cpu_insn_jnz(x) __builtin_annot("jnz "#x" ");
#define xmhfhwm_cpu_insn_jbe(x) __builtin_annot("jbe "#x" ");
#define xmhfhwm_cpu_insn_ja(x) __builtin_annot("ja "#x" ");
#define xmhfhwm_cpu_insn_int(x) __builtin_annot("int $"#x" ");
#define xmhfhwm_cpu_insn_call(x) __builtin_annot("call "#x" ");
#define xmhfhwm_cpu_insn_ret() __builtin_annot("ret ");
#define xmhfhwm_cpu_insn_lret() __builtin_annot("lret ");


// load/store instructions
#define _xmhfhwm_cpu_insn_movl_imm_eax(x) __builtin_annot("movl $"#x", %eax");
#define xmhfhwm_cpu_insn_movl_imm_eax(x) _xmhfhwm_cpu_insn_movl_imm_eax(x)

#define _xmhfhwm_cpu_insn_movl_imm_ebx(x) __builtin_annot("movl $"#x", %ebx");
#define xmhfhwm_cpu_insn_movl_imm_ebx(x) _xmhfhwm_cpu_insn_movl_imm_ebx(x)

#define _xmhfhwm_cpu_insn_movl_imm_ecx(x) __builtin_annot("movl $"#x", %ecx");
#define xmhfhwm_cpu_insn_movl_imm_ecx(x) _xmhfhwm_cpu_insn_movl_imm_ecx(x)

#define _xmhfhwm_cpu_insn_movl_imm_edi(x) __builtin_annot("movl $"#x", %edi");
#define xmhfhwm_cpu_insn_movl_imm_edi(x) _xmhfhwm_cpu_insn_movl_imm_edi(x)


#define _xmhfhwm_cpu_insn_movw_imm_ax(x) __builtin_annot("movw $"#x", %ax");
#define xmhfhwm_cpu_insn_movw_imm_ax(x) _xmhfhwm_cpu_insn_movw_imm_ax(x)

#define xmhfhwm_cpu_insn_movl_imm_mesp(x,y) __builtin_annot("movl $"#x", "#y"(%esp) ");

#define _xmhfhwm_cpu_insn_movl_imm_meax(x,y) __builtin_annot("movl $"#x", "#y"(%eax) ");
#define xmhfhwm_cpu_insn_movl_imm_meax(x,y) _xmhfhwm_cpu_insn_movl_imm_meax(x,y)

#define _xmhfhwm_cpu_insn_cmpl_imm_meax(x,y) __builtin_annot("cmpl $"#x", "#y"(%eax) ");
#define xmhfhwm_cpu_insn_cmpl_imm_meax(x,y) _xmhfhwm_cpu_insn_cmpl_imm_meax(x,y)


#define xmhfhwm_cpu_insn_movl_ecx_meax(x) __builtin_annot("movl %ecx, "#x"(%eax) ");
#define xmhfhwm_cpu_insn_movl_edx_meax(x) __builtin_annot("movl %edx, "#x"(%eax) ");


#define xmhfhwm_cpu_insn_movl_eax_mesp(x) __builtin_annot("movl %eax, "#x"(%esp) ");
#define xmhfhwm_cpu_insn_movl_eax_esp() __builtin_annot("movl %eax, %esp ");
#define xmhfhwm_cpu_insn_movl_edx_esp() __builtin_annot("movl %edx, %esp ");

#define xmhfhwm_cpu_insn_movl_mesp_eax(x) __builtin_annot("movl "#x"(%esp), %eax ");
#define xmhfhwm_cpu_insn_movw_mesp_ax(x) __builtin_annot("movw "#x"(%esp), %ax ");
#define xmhfhwm_cpu_insn_movl_mesp_ebx(x) __builtin_annot("movl "#x"(%esp), %ebx ");
#define xmhfhwm_cpu_insn_movl_mesp_ecx(x) __builtin_annot("movl "#x"(%esp), %ecx ");
#define xmhfhwm_cpu_insn_movl_mesp_edx(x) __builtin_annot("movl "#x"(%esp), %edx ");
#define xmhfhwm_cpu_insn_movl_mesp_esi(x) __builtin_annot("movl "#x"(%esp), %esi ");
#define xmhfhwm_cpu_insn_movl_mecx_eax(x) __builtin_annot("movl "#x"(%ecx), %eax ");
#define xmhfhwm_cpu_insn_movl_mecx_edx(x) __builtin_annot("movl "#x"(%ecx), %edx ");
#define xmhfhwm_cpu_insn_movl_eax_mecx(x) __builtin_annot("movl %eax, "#x"(%ecx) ");
#define xmhfhwm_cpu_insn_movl_edx_mecx(x) __builtin_annot("movl %edx, "#x"(%ecx) ");

#define xmhfhwm_cpu_insn_movl_eax_mesi(x) __builtin_annot("movl %eax, "#x"(%esi) ");
#define xmhfhwm_cpu_insn_movl_ebx_mesi(x) __builtin_annot("movl %ebx, "#x"(%esi) ");
#define xmhfhwm_cpu_insn_movl_ecx_mesi(x) __builtin_annot("movl %ecx, "#x"(%esi) ");
#define xmhfhwm_cpu_insn_movl_edx_mesi(x) __builtin_annot("movl %edx, "#x"(%esi) ");

#define xmhfhwm_cpu_insn_movl_meax_eax(x) __builtin_annot("movl "#x"(%eax), %eax ");
#define xmhfhwm_cpu_insn_movl_meax_ebx(x) __builtin_annot("movl "#x"(%eax), %ebx ");
#define xmhfhwm_cpu_insn_movl_meax_ecx(x) __builtin_annot("movl "#x"(%eax), %ecx ");
#define xmhfhwm_cpu_insn_movl_meax_edx(x) __builtin_annot("movl "#x"(%eax), %edx ");
#define xmhfhwm_cpu_insn_movl_meax_edi(x) __builtin_annot("movl "#x"(%eax), %edi ");
#define xmhfhwm_cpu_insn_movl_meax_esi(x) __builtin_annot("movl "#x"(%eax), %esi ");
#define xmhfhwm_cpu_insn_movl_meax_ebp(x) __builtin_annot("movl "#x"(%eax), %ebp ");
#define xmhfhwm_cpu_insn_movl_meax_esp(x) __builtin_annot("movl "#x"(%eax), %esp ");

#define xmhfhwm_cpu_insn_movl_mebx_ebx(x) __builtin_annot("movl "#x"(%ebx), %ebx ");
#define xmhfhwm_cpu_insn_movl_mecx_ecx(x) __builtin_annot("movl "#x"(%ecx), %ecx ");
#define xmhfhwm_cpu_insn_movl_medx_edx(x) __builtin_annot("movl "#x"(%edx), %edx ");
#define xmhfhwm_cpu_insn_movl_medi_edi(x) __builtin_annot("movl "#x"(%edi), %edi ");


#define xmhfhwm_cpu_insn_movl_edx_ecx() __builtin_annot("movl %edx, %ecx ");
#define xmhfhwm_cpu_insn_movl_edi_ebx() __builtin_annot("movl %edi, %ebx ");

#define xmhfhwm_cpu_insn_movl_esp_eax() __builtin_annot("movl %esp, %eax ");
#define xmhfhwm_cpu_insn_movl_esp_ecx() __builtin_annot("movl %esp, %ecx ");
#define xmhfhwm_cpu_insn_movl_esp_edx() __builtin_annot("movl %esp, %edx ");

#define xmhfhwm_cpu_insn_movl_mebxeax_eax(x) __builtin_annot("movl (%ebx, %eax, "#x"), %eax ");


#define xmhfhwm_cpu_insn_pushl_ebp() __builtin_annot("pushl %ebp ");
#define xmhfhwm_cpu_insn_pushl_edi() __builtin_annot("pushl %edi ");
#define xmhfhwm_cpu_insn_pushl_esi() __builtin_annot("pushl %esi ");
#define xmhfhwm_cpu_insn_pushl_eax() __builtin_annot("pushl %eax ");
#define xmhfhwm_cpu_insn_pushl_ebx() __builtin_annot("pushl %ebx ");
#define xmhfhwm_cpu_insn_pushl_ecx() __builtin_annot("pushl %ecx ");
#define xmhfhwm_cpu_insn_pushl_edx() __builtin_annot("pushl %edx ");
#define xmhfhwm_cpu_insn_pushl_esp() __builtin_annot("pushl %esp ");
#define xmhfhwm_cpu_insn_pushl_mesp(x) __builtin_annot("pushl "#x"(%esp) ");

#define xmhfhwm_cpu_insn_popl_eax() __builtin_annot("popl %eax ");
#define xmhfhwm_cpu_insn_popl_ebx() __builtin_annot("popl %ebx ");
#define xmhfhwm_cpu_insn_popl_ecx() __builtin_annot("popl %ecx ");
#define xmhfhwm_cpu_insn_popl_edx() __builtin_annot("popl %edx ");

#define xmhfhwm_cpu_insn_popl_esi() __builtin_annot("popl %esi ");
#define xmhfhwm_cpu_insn_popl_edi() __builtin_annot("popl %edi ");
#define xmhfhwm_cpu_insn_popl_ebp() __builtin_annot("popl %ebp ");

#define xmhfhwm_cpu_insn_pushl_imm(x) __builtin_annot("pushl $"#x" ");


// arithmetic/logical
#define xmhfhwm_cpu_insn_xorl_eax_eax() __builtin_annot("xorl %eax, %eax ");
#define xmhfhwm_cpu_insn_xorl_ebx_ebx() __builtin_annot("xorl %ebx, %ebx ");
#define xmhfhwm_cpu_insn_xorl_edx_edx() __builtin_annot("xorl %edx, %edx ");


#define xmhfhwm_cpu_insn_addl_mesp_ecx(x) __builtin_annot("addl "#x"(%esp), %ecx ");
#define xmhfhwm_cpu_insn_addl_imm_esp(x) __builtin_annot("addl $"#x", %esp ");
#define xmhfhwm_cpu_insn_subl_imm_esp(x) __builtin_annot("subl $"#x", %esp ");
#define xmhfhwm_cpu_insn_addl_eax_ecx() __builtin_annot("addl %eax, %ecx");
#define xmhfhwm_cpu_insn_addl_ecx_eax() __builtin_annot("addl %ecx, %eax");

#define xmhfhwm_cpu_insn_addl_imm_ecx(x) __builtin_annot("addl $"#x", %ecx ");

#define _xmhfhwm_cpu_insn_addl_imm_eax(x) __builtin_annot("addl $"#x", %eax ");
#define xmhfhwm_cpu_insn_addl_imm_eax(x) _xmhfhwm_cpu_insn_addl_imm_eax(x)

#define xmhfhwm_cpu_insn_andl_imm_edx(x) __builtin_annot("andl $"#x", %edx ");
#define xmhfhwm_cpu_insn_andl_imm_ecx(x) __builtin_annot("andl $"#x", %ecx ");
#define xmhfhwm_cpu_insn_shl_imm_ecx(x) __builtin_annot("shl $"#x", %ecx ");
#define xmhfhwm_cpu_insn_shr_imm_eax(x) __builtin_annot("shr $"#x", %eax ");

#define xmhfhwm_cpu_insn_orl_ecx_eax() __builtin_annot("orl %ecx, %eax ");
#define xmhfhwm_cpu_insn_orl_edx_eax() __builtin_annot("orl %edx, %eax ");
#define xmhfhwm_cpu_insn_orl_imm_eax(x) __builtin_annot("orl $"#x", %eax ");
#define xmhfhwm_cpu_insn_orl_imm_ecx(x) __builtin_annot("orl $"#x", %ecx ");


#define xmhfhwm_cpu_insn_btl_imm_mecx(x,y) __builtin_annot("btl $"#x", "#y"(%ecx) ");
#define xmhfhwm_cpu_insn_btrl_imm_mecx(x,y) __builtin_annot("btrl $"#x", "#y"(%ecx) ");
#define xmhfhwm_cpu_insn_btsl_imm_mecx(x,y) __builtin_annot("btsl $"#x", "#y"(%ecx) ");
#define xmhfhwm_cpu_insn_bsrl_mesp_eax(x) __builtin_annot("bsrl "#x"(%esp), %eax ");

#define xmhfhwm_cpu_insn_mull_ecx() __builtin_annot("mull %ecx ");


//segment registers
#define xmhfhwm_cpu_insn_movl_cs_eax() __builtin_annot("movl %cs, %eax ");
#define xmhfhwm_cpu_insn_movl_ds_eax() __builtin_annot("movl %ds, %eax ");
#define xmhfhwm_cpu_insn_movl_es_eax() __builtin_annot("movl %es, %eax ");
#define xmhfhwm_cpu_insn_movl_fs_eax() __builtin_annot("movl %fs, %eax ");
#define xmhfhwm_cpu_insn_movl_gs_eax() __builtin_annot("movl %gs, %eax ");
#define xmhfhwm_cpu_insn_movl_ss_eax() __builtin_annot("movl %ss, %eax ");
#define xmhfhwm_cpu_insn_movw_ds_ax() __builtin_annot("movw %ds, %ax ");
#define xmhfhwm_cpu_insn_movw_ax_ds() __builtin_annot("movw %ax, %ds ");
#define xmhfhwm_cpu_insn_movw_ax_es() __builtin_annot("movw %ax, %es ");
#define xmhfhwm_cpu_insn_movw_ax_fs() __builtin_annot("movw %ax, %fs ");
#define xmhfhwm_cpu_insn_movw_ax_gs() __builtin_annot("movw %ax, %gs ");
#define xmhfhwm_cpu_insn_movw_ax_ss() __builtin_annot("movw %ax, %ss ");

//control registers
#define xmhfhwm_cpu_insn_movl_cr0_eax() __builtin_annot("movl %cr0, %eax ");
#define xmhfhwm_cpu_insn_movl_eax_cr0() __builtin_annot("movl %eax, %cr0 ");
#define xmhfhwm_cpu_insn_movl_cr2_eax() __builtin_annot("movl %cr2, %eax ");
#define xmhfhwm_cpu_insn_movl_eax_cr2() __builtin_annot("movl %eax, %cr2 ");
#define xmhfhwm_cpu_insn_movl_cr3_eax() __builtin_annot("movl %cr3, %eax ");
#define xmhfhwm_cpu_insn_movl_eax_cr3() __builtin_annot("movl %eax, %cr3 ");
#define xmhfhwm_cpu_insn_movl_ebx_cr3() __builtin_annot("movl %ebx, %cr3 ");

#define xmhfhwm_cpu_insn_movl_cr4_eax() __builtin_annot("movl %cr4, %eax ");
#define xmhfhwm_cpu_insn_movl_eax_cr4() __builtin_annot("movl %eax, %cr4 ");

//other instructions
#define xmhfhwm_cpu_insn_pause() __builtin_annot("pause ");
#define xmhfhwm_cpu_insn_cpuid() __builtin_annot("cpuid ");
#define xmhfhwm_cpu_insn_pushfl() __builtin_annot("pushfl ");
#define xmhfhwm_cpu_insn_popfl() __builtin_annot("popfl ");
#define xmhfhwm_cpu_insn_rdtsc() __builtin_annot("rdtsc ");
#define xmhfhwm_cpu_insn_hlt() __builtin_annot("hlt ");
#define xmhfhwm_cpu_insn_pushal() __builtin_annot("pushal ");
#define xmhfhwm_cpu_insn_popal() __builtin_annot("popal ");

// system instructions
#define xmhfhwm_cpu_insn_cli() __builtin_annot("cli ");
#define xmhfhwm_cpu_insn_sti() __builtin_annot("sti ");
#define xmhfhwm_cpu_insn_inb_dx_al() __builtin_annot("inb %dx, %al ");
#define xmhfhwm_cpu_insn_inw_dx_ax() __builtin_annot("inw %dx, %ax ");
#define xmhfhwm_cpu_insn_inl_dx_eax() __builtin_annot("inl %dx, %eax ");
#define xmhfhwm_cpu_insn_outb_al_dx() __builtin_annot("outb %al, %dx ");
#define xmhfhwm_cpu_insn_outw_ax_dx() __builtin_annot("outw %ax, %dx ");
#define xmhfhwm_cpu_insn_outl_eax_dx() __builtin_annot("outl %eax, %dx ");
#define xmhfhwm_cpu_insn_rdmsr() __builtin_annot("rdmsr ");
#define xmhfhwm_cpu_insn_wrmsr() __builtin_annot("wrmsr ");
#define xmhfhwm_cpu_insn_wbinvd() __builtin_annot("wbinvd ");
#define xmhfhwm_cpu_insn_invlpg_mesp(x) __builtin_annot("invlpg "#x"(%esp) ");
#define xmhfhwm_cpu_insn_sgdt_mesp(x) __builtin_annot("sgdt "#x"(%esp) ");
#define xmhfhwm_cpu_insn_str_ax() __builtin_annot("str %ax ");
#define xmhfhwm_cpu_insn_sidt_mesp(x) __builtin_annot("sidt "#x"(%esp) ");
#define xmhfhwm_cpu_insn_lidt_mecx(x) __builtin_annot("lidt "#x"(%ecx) ");
#define xmhfhwm_cpu_insn_ltr_ax() __builtin_annot("ltr %ax ");
#define xmhfhwm_cpu_insn_lgdt_mecx(x) __builtin_annot("lgdt "#x"(%ecx) ");
#define xmhfhwm_cpu_insn_lock() __builtin_annot("lock ");
#define xmhfhwm_cpu_insn_xsetbv() __builtin_annot("xsetbv ");
#define xmhfhwm_cpu_insn_xgetbv() __builtin_annot("xgetbv ");
#define xmhfhwm_cpu_insn_iretl() __builtin_annot("iretl ");
#define xmhfhwm_cpu_insn_sysexit() __builtin_annot("sysexit ");
#define xmhfhwm_cpu_insn_sysenter() __builtin_annot("sysenter ");

#endif //__ASSEMBLY__

#endif /* __XMHFHWM_CPU_H__ */
