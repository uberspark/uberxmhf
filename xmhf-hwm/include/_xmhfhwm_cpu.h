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


//#define get_eflags(x)  __asm__ __volatile__("pushfl ; popl %0 ":"=g" (x): /* no input */ :"memory")
static inline u64 get_rflags(void){
    u64 _rflags;

    asm volatile(
                 "pushfq \r\n"
                 "popq %0 \r\n"
                 : "=g" (_rflags)
                 :
                 :
                 );

    return _rflags;
}

//#define set_eflags(x) __asm__ __volatile__("pushl %0 ; popfl": /* no output */ :"g" (x):"memory", "cc")
static inline void set_rflags(u64 rflags){

    asm volatile(
                 "pushq %0 \r\n"
                 "popfq \r\n"
                 :
                 : "g" (rflags)
                 : "cc"
                 );

}


static inline void cpuid(u32 op, u32 *eax, u32 *ebx, u32 *ecx, u32 *edx){

    asm volatile(
                 "cpuid \r\n"
                :"=a"(*(eax)), "=b"(*(ebx)), "=c"(*(ecx)), "=d"(*(edx))
                :"a"(op), "c"(*(ecx))
                :
               );

}

#define rdtsc(eax, edx)		\
({						\
  __asm__ __volatile__ ("rdtsc"				\
          :"=a"(*(eax)), "=d"(*(edx))	\
          :);			\
})

static inline uint64_t rdtsc64(void)
{
        uint64_t rv;

        __asm__ __volatile__ ("rdtsc" : "=A" (rv));
        return (rv);
}


/* Calls to read and write control registers */
static inline u64 read_cr0(void){
  u64 __cr0;
  asm volatile("mov %%cr0,%0 \r\n" :"=r" (__cr0));
  return __cr0;
}

static inline void write_cr0(u64 val){
  asm volatile("mov %0,%%cr0 \r\n": :"r" (val));
}

static inline u64 read_cr3(void){
  u64 __cr3;
  asm volatile("mov %%cr3,%0 \r\n" :"=r" (__cr3));
  return __cr3;
}

static inline u32 read_esp(void){
  u32 __esp;
  asm volatile("mov %%esp,%0 \r\n" :"=r" (__esp));
  return __esp;
}

static inline u64 read_rsp(void){
  u64 __rsp;
  asm volatile("movq %%rsp,%0\n\t" :"=r" (__rsp));
  return __rsp;
}

static inline unsigned long read_ebp(void){
  unsigned long __ebp;
  __asm__("mov %%ebp,%0\n\t" :"=r" (__ebp));
  return __ebp;
}

static inline void write_cr3(u64 val){
  asm volatile("mov %0,%%cr3 \r\n"::"r" (val));
}

static inline u64 read_cr2(void){
  u64 __cr2;
  asm volatile("mov %%cr2,%0 \r\n" :"=r" (__cr2));
  return __cr2;
}

//*
static inline u64 read_cr4(void){
  u64 __cr4;
  asm volatile("mov %%cr4, %0 \r\n" :"=r" (__cr4));
  return __cr4;
}

//*
static inline void write_cr4(u64 val){
  asm volatile("mov %0,%%cr4": :"r" (val));
}


static inline void skinit(unsigned long eax) {
    __asm__("mov %0, %%eax": :"r" (eax));
    __asm__("skinit %%eax":);
}


//segment register access
static inline u32 read_segreg_cs(void){
  u32 __cs;
  __asm__("mov %%cs, %0 \r\n" :"=r" (__cs));
  return __cs;
}

static inline u32 read_segreg_ds(void){
  u32 __ds;
  __asm__("mov %%ds, %0 \r\n" :"=r" (__ds));
  return __ds;
}

static inline u32 read_segreg_es(void){
  u32 __es;
  __asm__("mov %%es, %0 \r\n" :"=r" (__es));
  return __es;
}

static inline u32 read_segreg_fs(void){
  u32 __fs;
  __asm__("mov %%fs, %0 \r\n" :"=r" (__fs));
  return __fs;
}

static inline u32 read_segreg_gs(void){
  u32 __gs;
  __asm__("mov %%gs, %0 \r\n" :"=r" (__gs));
  return __gs;
}

static inline u32 read_segreg_ss(void){
  u32 __ss;
  __asm__("mov %%ss, %0 \r\n" :"=r" (__ss));
  return __ss;
}

static inline u16 read_tr_sel(void){
  u16 __trsel;
  __asm__("str %0 \r\n" :"=r" (__trsel));
  return __trsel;
}

static inline void wbinvd(void)
{
    __asm__ __volatile__ ("wbinvd");
}

static inline uint32_t bsrl(uint32_t mask)
{
    uint32_t   result;

    __asm__ __volatile__ ("bsrl %1,%0" : "=r" (result) : "rm" (mask) : "cc");
    return (result);
}


static inline void disable_intr(void)
{
    __asm__ __volatile__ ("cli" : : : "memory");
}

static inline void enable_intr(void)
{
    __asm__ __volatile__ ("sti");
}

//get extended control register (xcr)
static inline u64 xgetbv(u32 xcr_reg){
	u32 eax, edx;

	asm volatile(".byte 0x0f,0x01,0xd0"
			: "=a" (eax), "=d" (edx)
			: "c" (xcr_reg));

	return ((u64)edx << 32) + (u64)eax;
}

//set extended control register (xcr)
static inline void xsetbv(u32 xcr_reg, u64 value){
	u32 eax = (u32)value;
	u32 edx = value >> 32;

	asm volatile(".byte 0x0f,0x01,0xd1"
			:
			: "a" (eax), "d" (edx), "c" (xcr_reg));
}










static inline void sysexitq(u64 rip, u64 rsp){

            asm volatile(
                 "movq %0, %%rdx \r\n"
                 "movq %1, %%rcx \r\n"

                 "sysexitq \r\n"
                 //"int $0x03 \r\n"
                 //"1: jmp 1b \r\n"
                :
                : "m" (rip),
                  "m" (rsp)
                : "rdx", "rcx"
            );

}









#ifndef __XMHF_VERIFICATION__



    static inline void spin_lock(volatile u32 *lock){
        __asm__ __volatile__ (
            "1:	btl	$0, %0	\r\n"	//mutex is available?
            "		jnc 1b	\r\n"	//wait till it is
            "      	lock		\r\n"   //lock the bus (exclusive access)
            "		btrl	$0, %0	\r\n"   //and try to grab the mutex
            "		jnc	1b	\r\n"   //spin until successful --> spinlock :p
            : //no asm outputs
            : "m" (*lock)
        );
    }

    static inline void spin_unlock(volatile u32 *lock){
        __asm__ __volatile__ (
            "btsl	$0, %0		\r\n"	//release spinlock
            : //no asm outputs
            : "m" (*lock)
        );
    }


#else //__XMHF_VERIFICATION__

	static inline u32 get_cpu_vendor_or_die(void) {
			extern u32 xmhf_verify_cpu_vendor;
			return xmhf_verify_cpu_vendor;
	}

	inline void spin_lock(volatile u32 *lock){
			(void)lock;
	}

	inline void spin_unlock(volatile u32 *lock){
			(void)lock;
	}

#endif //__XMHF_VERIFICATION__

//void xmhfhw_cpu_x86_save_mtrrs(mtrr_state_t *saved_state);
//void xmhfhw_cpu_x86_restore_mtrrs(mtrr_state_t *saved_state);




static inline u64 xmhf_baseplatform_arch_x86_getgdtbase(void){
		struct {
			u16 limit;
			u64 base;
		} __attribute__ ((packed)) gdtr;


		asm volatile(
			"sgdt %0 \r\n"
			: //no output
			: "m" (gdtr)
			: //no clobber
		);

		return gdtr.base;
}

static inline u64 xmhf_baseplatform_arch_x86_getidtbase(void){
		struct {
			u16 limit;
			u64 base;
		} __attribute__ ((packed)) idtr;


		asm volatile(
			"sidt %0 \r\n"
			: //no output
			: "m" (idtr)
			: //no clobber
		);

		return idtr.base;
}

static inline u64  xmhf_baseplatform_arch_x86_gettssbase(void){
	  u64 gdtbase = xmhf_baseplatform_arch_x86_getgdtbase();
	  u32 tssdesc_low, tssdesc_high;

	  asm volatile(
            "movl %2, %%edi\r\n"
            "xorl %%eax, %%eax\r\n"
            "str %%ax \r\n"
            "addl %%eax, %%edi\r\n"		//%edi is pointer to TSS descriptor in GDT
            "movl (%%edi), %0 \r\n"		//move low 32-bits of TSS descriptor into tssdesc_low
            "addl $0x4, %%edi\r\n"		//%edi points to top 32-bits of 64-bit TSS desc.
            "movl (%%edi), %1 \r\n"		//move high 32-bits of TSS descriptor into tssdesc_high
	     : "=r" (tssdesc_low), "=r" (tssdesc_high)
	     : "m"(gdtbase)
	     : "edi", "eax"
	  );

       return (  (u64)(  ((u32)tssdesc_high & 0xFF000000UL) | (((u32)tssdesc_high & 0x000000FFUL) << 16)  | ((u32)tssdesc_low >> 16)  ) );
}







#endif //__ASSEMBLY__

#endif /* __XMHFHWM_CPU_H__ */
