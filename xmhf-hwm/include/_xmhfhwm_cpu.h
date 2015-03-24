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
} __attribute__((packed)) tss_t;





//////

// label
// TODO: move into xmhf-hic.h as a CASM pseudo-language definition
#define CASM_LABEL(x)   asm volatile (#x": \r\n");
#define CASM_BALIGN(x)  asm volatile (".balign "#x" \r\n");

// branch instructions
#define xmhfhwm_cpu_insn_jmp(x) asm volatile ("jmp "#x" \r\n");
#define xmhfhwm_cpu_insn_jmpl_eax() asm volatile ("jmpl *%eax \r\n");
#define xmhfhwm_cpu_insn_jc(x) asm volatile ("jc "#x" \r\n");
#define xmhfhwm_cpu_insn_jnc(x) asm volatile ("jnc "#x" \r\n");
#define xmhfhwm_cpu_insn_jnz(x) asm volatile ("jnz "#x" \r\n");
#define xmhfhwm_cpu_insn_jbe(x) asm volatile ("jbe "#x" \r\n");
#define xmhfhwm_cpu_insn_ja(x) asm volatile ("ja "#x" \r\n");
#define xmhfhwm_cpu_insn_int(x) asm volatile ("int $"#x" \r\n");
#define xmhfhwm_cpu_insn_call(x) asm volatile ("call "#x" \r\n");
#define xmhfhwm_cpu_insn_ret() asm volatile ("ret \r\n");
#define xmhfhwm_cpu_insn_lret() asm volatile ("lret \r\n");


// load/store instructions
#define _xmhfhwm_cpu_insn_movl_imm_eax(x) asm volatile ("movl $"#x", %eax\r\n");
#define xmhfhwm_cpu_insn_movl_imm_eax(x) _xmhfhwm_cpu_insn_movl_imm_eax(x)

#define _xmhfhwm_cpu_insn_movl_imm_ebx(x) asm volatile ("movl $"#x", %ebx\r\n");
#define xmhfhwm_cpu_insn_movl_imm_ebx(x) _xmhfhwm_cpu_insn_movl_imm_ebx(x)

#define _xmhfhwm_cpu_insn_movl_imm_ecx(x) asm volatile ("movl $"#x", %ecx\r\n");
#define xmhfhwm_cpu_insn_movl_imm_ecx(x) _xmhfhwm_cpu_insn_movl_imm_ecx(x)

#define _xmhfhwm_cpu_insn_movl_imm_edi(x) asm volatile ("movl $"#x", %edi\r\n");
#define xmhfhwm_cpu_insn_movl_imm_edi(x) _xmhfhwm_cpu_insn_movl_imm_edi(x)


#define _xmhfhwm_cpu_insn_movw_imm_ax(x) asm volatile ("movw $"#x", %ax\r\n");
#define xmhfhwm_cpu_insn_movw_imm_ax(x) _xmhfhwm_cpu_insn_movw_imm_ax(x)

#define xmhfhwm_cpu_insn_movl_eax_mesp(x) asm volatile ("movl %eax, "#x"(%esp) \r\n");
#define xmhfhwm_cpu_insn_movl_eax_esp() asm volatile ("movl %eax, %esp \r\n");

#define xmhfhwm_cpu_insn_movl_mesp_eax(x) asm volatile ("movl "#x"(%esp), %eax \r\n");
#define xmhfhwm_cpu_insn_movw_mesp_ax(x) asm volatile ("movw "#x"(%esp), %ax \r\n");
#define xmhfhwm_cpu_insn_movl_mesp_ebx(x) asm volatile ("movl "#x"(%esp), %ebx \r\n");
#define xmhfhwm_cpu_insn_movl_mesp_ecx(x) asm volatile ("movl "#x"(%esp), %ecx \r\n");
#define xmhfhwm_cpu_insn_movl_mesp_edx(x) asm volatile ("movl "#x"(%esp), %edx \r\n");
#define xmhfhwm_cpu_insn_movl_mesp_esi(x) asm volatile ("movl "#x"(%esp), %esi \r\n");
#define xmhfhwm_cpu_insn_movl_mecx_eax(x) asm volatile ("movl "#x"(%ecx), %eax \r\n");
#define xmhfhwm_cpu_insn_movl_mecx_edx(x) asm volatile ("movl "#x"(%ecx), %edx \r\n");
#define xmhfhwm_cpu_insn_movl_eax_mecx(x) asm volatile ("movl %eax, "#x"(%ecx) \r\n");
#define xmhfhwm_cpu_insn_movl_edx_mecx(x) asm volatile ("movl %edx, "#x"(%ecx) \r\n");

#define xmhfhwm_cpu_insn_movl_eax_mesi(x) asm volatile ("movl %eax, "#x"(%esi) \r\n");
#define xmhfhwm_cpu_insn_movl_ebx_mesi(x) asm volatile ("movl %ebx, "#x"(%esi) \r\n");
#define xmhfhwm_cpu_insn_movl_ecx_mesi(x) asm volatile ("movl %ecx, "#x"(%esi) \r\n");
#define xmhfhwm_cpu_insn_movl_edx_mesi(x) asm volatile ("movl %edx, "#x"(%esi) \r\n");

#define xmhfhwm_cpu_insn_movl_meax_eax(x) asm volatile ("movl "#x"(%eax), %eax \r\n");
#define xmhfhwm_cpu_insn_movl_mebx_ebx(x) asm volatile ("movl "#x"(%ebx), %ebx \r\n");
#define xmhfhwm_cpu_insn_movl_mecx_ecx(x) asm volatile ("movl "#x"(%ecx), %ecx \r\n");
#define xmhfhwm_cpu_insn_movl_medx_edx(x) asm volatile ("movl "#x"(%edx), %edx \r\n");
#define xmhfhwm_cpu_insn_movl_medi_edi(x) asm volatile ("movl "#x"(%edi), %edi \r\n");

#define xmhfhwm_cpu_insn_movl_imm_mesp(x,y) asm volatile ("movl $"#x", "#y"(%esp) \r\n");

#define xmhfhwm_cpu_insn_movl_edx_ecx() asm volatile ("movl %edx, %ecx \r\n");
#define xmhfhwm_cpu_insn_movl_edi_ebx() asm volatile ("movl %edi, %ebx \r\n");

#define xmhfhwm_cpu_insn_movl_esp_eax() asm volatile ("movl %esp, %eax \r\n");

#define xmhfhwm_cpu_insn_movl_mebxeax_eax(x) asm volatile ("movl (%ebx, %eax, "#x"), %eax \r\n");



#define xmhfhwm_cpu_insn_popl_ebx() asm volatile ("popl %ebx \r\n");
#define xmhfhwm_cpu_insn_popl_esi() asm volatile ("popl %esi \r\n");
#define xmhfhwm_cpu_insn_pushl_esi() asm volatile ("pushl %esi \r\n");
#define xmhfhwm_cpu_insn_pushl_eax() asm volatile ("pushl %eax \r\n");
#define xmhfhwm_cpu_insn_pushl_ebx() asm volatile ("pushl %ebx \r\n");
#define xmhfhwm_cpu_insn_pushl_esp() asm volatile ("pushl %esp \r\n");
#define xmhfhwm_cpu_insn_pushl_mesp(x) asm volatile ("pushl "#x"(%esp) \r\n");
#define xmhfhwm_cpu_insn_popl_eax() asm volatile ("popl %eax \r\n");
#define xmhfhwm_cpu_insn_pushl_imm(x) asm volatile ("pushl $"#x" \r\n");


// arithmetic/logical
#define xmhfhwm_cpu_insn_xorl_eax_eax() asm volatile ("xorl %eax, %eax \r\n");
#define xmhfhwm_cpu_insn_xorl_ebx_ebx() asm volatile ("xorl %ebx, %ebx \r\n");
#define xmhfhwm_cpu_insn_xorl_edx_edx() asm volatile ("xorl %edx, %edx \r\n");


#define xmhfhwm_cpu_insn_addl_mesp_ecx(x) asm volatile ("addl "#x"(%esp), %ecx \r\n");
#define xmhfhwm_cpu_insn_addl_imm_esp(x) asm volatile ("addl "#x", %esp \r\n");
#define xmhfhwm_cpu_insn_subl_imm_esp(x) asm volatile ("subl "#x", %esp \r\n");
#define xmhfhwm_cpu_insn_addl_eax_ecx() asm volatile ("addl %eax, %ecx\r\n");
#define xmhfhwm_cpu_insn_addl_ecx_eax() asm volatile ("addl %ecx, %eax\r\n");

#define xmhfhwm_cpu_insn_addl_imm_ecx(x) asm volatile ("addl "#x", %ecx \r\n");

#define _xmhfhwm_cpu_insn_addl_imm_eax(x) asm volatile ("addl "#x", %eax \r\n");
#define xmhfhwm_cpu_insn_addl_imm_eax(x) _xmhfhwm_cpu_insn_addl_imm_eax(x)

#define xmhfhwm_cpu_insn_andl_imm_edx(x) asm volatile ("andl $"#x", %edx \r\n");
#define xmhfhwm_cpu_insn_andl_imm_ecx(x) asm volatile ("andl $"#x", %ecx \r\n");
#define xmhfhwm_cpu_insn_shl_imm_ecx(x) asm volatile ("shl $"#x", %ecx \r\n");
#define xmhfhwm_cpu_insn_shr_imm_eax(x) asm volatile ("shr $"#x", %eax \r\n");

#define xmhfhwm_cpu_insn_orl_ecx_eax() asm volatile ("orl %ecx, %eax \r\n");
#define xmhfhwm_cpu_insn_orl_edx_eax() asm volatile ("orl %edx, %eax \r\n");
#define xmhfhwm_cpu_insn_orl_imm_eax(x) asm volatile ("orl $"#x", %eax \r\n");
#define xmhfhwm_cpu_insn_orl_imm_ecx(x) asm volatile ("orl $"#x", %ecx \r\n");


#define xmhfhwm_cpu_insn_btl_imm_mecx(x,y) asm volatile ("btl $"#x", "#y"(%ecx) \r\n");
#define xmhfhwm_cpu_insn_btrl_imm_mecx(x,y) asm volatile ("btrl $"#x", "#y"(%ecx) \r\n");
#define xmhfhwm_cpu_insn_btsl_imm_mecx(x,y) asm volatile ("btsl $"#x", "#y"(%ecx) \r\n");
#define xmhfhwm_cpu_insn_bsrl_mesp_eax(x) asm volatile ("bsrl "#x"(%esp), %eax \r\n");

#define xmhfhwm_cpu_insn_mull_ecx() asm volatile ("mull %ecx \r\n");


//segment registers
#define xmhfhwm_cpu_insn_movl_cs_eax() asm volatile ("movl %cs, %eax \r\n");
#define xmhfhwm_cpu_insn_movl_cs_eax() asm volatile ("movl %ds, %eax \r\n");
#define xmhfhwm_cpu_insn_movl_cs_eax() asm volatile ("movl %es, %eax \r\n");
#define xmhfhwm_cpu_insn_movl_cs_eax() asm volatile ("movl %fs, %eax \r\n");
#define xmhfhwm_cpu_insn_movl_cs_eax() asm volatile ("movl %gs, %eax \r\n");
#define xmhfhwm_cpu_insn_movl_cs_eax() asm volatile ("movl %ss, %eax \r\n");
#define xmhfhwm_cpu_insn_movw_ds_ax() asm volatile ("movw %ds, %ax \r\n");
#define xmhfhwm_cpu_insn_movw_ax_ds() asm volatile ("movw %ax, %ds \r\n");
#define xmhfhwm_cpu_insn_movw_ax_es() asm volatile ("movw %ax, %es \r\n");
#define xmhfhwm_cpu_insn_movw_ax_fs() asm volatile ("movw %ax, %fs \r\n");
#define xmhfhwm_cpu_insn_movw_ax_gs() asm volatile ("movw %ax, %gs \r\n");
#define xmhfhwm_cpu_insn_movw_ax_ss() asm volatile ("movw %ax, %ss \r\n");

//control registers
#define xmhfhwm_cpu_insn_movl_cr0_eax() asm volatile ("movl %cr0, %eax \r\n");
#define xmhfhwm_cpu_insn_movl_eax_cr0() asm volatile ("movl %eax, %cr0 \r\n");
#define xmhfhwm_cpu_insn_movl_cr2_eax() asm volatile ("movl %cr2, %eax \r\n");
#define xmhfhwm_cpu_insn_movl_eax_cr2() asm volatile ("movl %eax, %cr2 \r\n");
#define xmhfhwm_cpu_insn_movl_cr3_eax() asm volatile ("movl %cr3, %eax \r\n");
#define xmhfhwm_cpu_insn_movl_eax_cr3() asm volatile ("movl %eax, %cr3 \r\n");
#define xmhfhwm_cpu_insn_movl_ebx_cr3() asm volatile ("movl %ebx, %cr3 \r\n");

#define xmhfhwm_cpu_insn_movl_cr4_eax() asm volatile ("movl %cr4, %eax \r\n");
#define xmhfhwm_cpu_insn_movl_eax_cr4() asm volatile ("movl %eax, %cr4 \r\n");

//other instructions
#define xmhfhwm_cpu_insn_pause() asm volatile ("pause \r\n");
#define xmhfhwm_cpu_insn_cpuid() asm volatile ("cpuid \r\n");
#define xmhfhwm_cpu_insn_pushfl() asm volatile ("pushfl \r\n");
#define xmhfhwm_cpu_insn_popfl() asm volatile ("popfl \r\n");
#define xmhfhwm_cpu_insn_rdtsc() asm volatile ("rdtsc \r\n");
#define xmhfhwm_cpu_insn_hlt() asm volatile ("hlt \r\n");
#define xmhfhwm_cpu_insn_pushal() asm volatile ("pushal \r\n");
#define xmhfhwm_cpu_insn_popal() asm volatile ("popal \r\n");

// system instructions
#define xmhfhwm_cpu_insn_cli() asm volatile ("cli \r\n");
#define xmhfhwm_cpu_insn_sti() asm volatile ("sti \r\n");
#define xmhfhwm_cpu_insn_inb_dx_al() asm volatile ("inb %dx, %al \r\n");
#define xmhfhwm_cpu_insn_inw_dx_ax() asm volatile ("inw %dx, %ax \r\n");
#define xmhfhwm_cpu_insn_inl_dx_eax() asm volatile ("inl %dx, %eax \r\n");
#define xmhfhwm_cpu_insn_outb_al_dx() asm volatile ("outb %al, %dx \r\n");
#define xmhfhwm_cpu_insn_outw_ax_dx() asm volatile ("outw %ax, %dx \r\n");
#define xmhfhwm_cpu_insn_outl_eax_dx() asm volatile ("outl %eax, %dx \r\n");
#define xmhfhwm_cpu_insn_rdmsr() asm volatile ("rdmsr \r\n");
#define xmhfhwm_cpu_insn_wrmsr() asm volatile ("wrmsr \r\n");
#define xmhfhwm_cpu_insn_wbinvd() asm volatile ("wbinvd \r\n");
#define xmhfhwm_cpu_insn_invlpg_mesp(x) asm volatile ("invlpg "#x"(%esp) \r\n");
#define xmhfhwm_cpu_insn_sgdt_mesp(x) asm volatile ("sgdt "#x"(%esp) \r\n");
#define xmhfhwm_cpu_insn_str_ax() asm volatile ("str %ax \r\n");
#define xmhfhwm_cpu_insn_sidt_mesp(x) asm volatile ("sidt "#x"(%esp) \r\n");
#define xmhfhwm_cpu_insn_lidt_mecx(x) asm volatile ("lidt "#x"(%ecx) \r\n");
#define xmhfhwm_cpu_insn_ltr_ax() asm volatile ("ltr %ax \r\n");
#define xmhfhwm_cpu_insn_lgdt_mecx(x) asm volatile ("lgdt "#x"(%ecx) \r\n");
#define xmhfhwm_cpu_insn_lock() asm volatile ("lock \r\n");
#define xmhfhwm_cpu_insn_xsetbv() asm volatile ("xsetbv \r\n");
#define xmhfhwm_cpu_insn_xgetbv() asm volatile ("xgetbv \r\n");
#define xmhfhwm_cpu_insn_iretl() asm volatile ("iretl \r\n");


#endif //__ASSEMBLY__

#endif /* __XMHFHWM_CPU_H__ */
