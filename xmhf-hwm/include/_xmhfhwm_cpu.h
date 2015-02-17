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

typedef union {
    uint64_t	raw;
    struct {
        uint64_t vcnt        : 8;    /* num variable MTRR pairs */
        uint64_t fix         : 1;    /* fixed range MTRRs are supported */
        uint64_t reserved1   : 1;
        uint64_t wc          : 1;    /* write-combining mem type supported */
        uint64_t reserved2   : 53;
    };
} __attribute__((packed)) mtrr_cap_t;

typedef union {
    uint64_t	raw;
    struct {
        uint64_t type        : 8;
        uint64_t reserved1   : 2;
        uint64_t fe          : 1;    /* fixed MTRR enable */
        uint64_t e           : 1;    /* (all) MTRR enable */
        uint64_t reserved2   : 52;
    };
} __attribute__((packed)) mtrr_def_type_t;

typedef union {
    uint64_t	raw;
    struct {
        uint64_t type      : 8;
        uint64_t reserved1 : 4;
        /* TBD: the end of base really depends on MAXPHYADDR, but since */
        /* the MTRRs are set for SINIT and it must be <4GB, can use 24b */
        uint64_t base      : 24;
        uint64_t reserved2 : 28;
    };
} __attribute__((packed)) mtrr_physbase_t;

typedef union {
    uint64_t	raw;
    struct {
        uint64_t reserved1 : 11;
        uint64_t v         : 1;      /* valid */
        /* TBD: the end of mask really depends on MAXPHYADDR, but since */
        /* the MTRRs are set for SINIT and it must be <4GB, can use 24b */
        uint64_t mask      : 24;
        uint64_t reserved2 : 28;
    };
} __attribute__((packed)) mtrr_physmask_t;

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
typedef struct {
  u16 isrLow;
  u16 isrSelector;
  u8  count;
  u8  type;
  u16 isrHigh;
  u32 offset3263;
  u32 reserved;
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







#define xmhfhwm_cpu_insn_cli() asm volatile ("cli \r\n" : : : "memory");

#define xmhfhwm_cpu_insn_ret() asm volatile ("ret \r\n");




#endif //__ASSEMBLY__

#endif /* __XMHFHWM_CPU_H__ */
