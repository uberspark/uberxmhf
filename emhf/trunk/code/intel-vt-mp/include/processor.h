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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

//processor.h - CPU declarations
//author: amit vasudevan (amitvasudevan@acm.org)
#ifndef __PROCESSOR_H
#define __PROCESSOR_H

#define VENDOR_INTEL 0
#define VENDOR_AMD 2

#define AMD_STRING_DWORD1 0x68747541
#define AMD_STRING_DWORD2 0x444D4163
#define AMD_STRING_DWORD3 0x69746E65

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

//CPUID related
#define EDX_PAE 6
#define EDX_NX 20
#define ECX_SVM 2
#define EDX_NP 0


#ifndef __ASSEMBLY__
typedef struct {
  u16 isrLow;
  u16 isrSelector;
  u8  count;
  u8  type;
  u16 isrHigh;
} __attribute__ ((packed)) idtentry_t;

typedef struct {
  unsigned short limit0_15;
  unsigned short baseAddr0_15;
  unsigned char baseAddr16_23;
  unsigned char attributes1;
  unsigned char limit16_19attributes2;    
  unsigned char baseAddr24_31;
} __attribute__ ((packed)) TSSENTRY;

typedef struct {
	unsigned long eip;
	unsigned long cs;
	unsigned long eflags;
	unsigned long esp;
	unsigned long ss;
	unsigned long es;
	unsigned long ds;
	unsigned long fs;
	unsigned long gs;
} __attribute__ ((packed)) FAULTFRAME; 


typedef struct {
	unsigned long ebp;
	unsigned long edi;
	unsigned long esi;
	unsigned long edx;
	unsigned long ecx;
	unsigned long ebx;
	unsigned long eax;
	unsigned long esp;
} __attribute__ ((packed)) INTRREGS; 


#define get_eflags(x)  __asm__ __volatile__("pushfl ; popl %0 ":"=g" (x): /* no input */ :"memory")
#define set_eflags(x) __asm__ __volatile__("pushl %0 ; popfl": /* no output */ :"g" (x):"memory", "cc")

#define cpuid(op, eax, ebx, ecx, edx)		\
({						\
  __asm__("cpuid"				\
          :"=a"(*(eax)), "=b"(*(ebx)), "=c"(*(ecx)), "=d"(*(edx))	\
          :"0"(op), "2" (0));			\
})


#define rdtsc(eax, edx)		\
({						\
  __asm__("rdtsc"				\
          :"=a"(*(eax)), "=d"(*(edx))	\
          :);			\
})

//forward prototypes
static inline u32 read_cr0(void) __attribute__ ((always_inline));
static inline void write_cr0(u32 val) __attribute__ ((always_inline));
static inline u32 read_cr3(void) __attribute__ ((always_inline));
static inline void write_cr3(u32 val) __attribute__ ((always_inline));
static inline u32 read_cr4(void) __attribute__ ((always_inline));
static inline void write_cr4(u32 val) __attribute__ ((always_inline));
static inline u32 read_cr2(void) __attribute__ ((always_inline));

static inline u32 read_segreg_cs(void) __attribute__ ((always_inline));
static inline u32 read_segreg_ds(void) __attribute__ ((always_inline));
static inline u32 read_segreg_es(void) __attribute__ ((always_inline));
static inline u32 read_segreg_fs(void) __attribute__ ((always_inline));
static inline u32 read_segreg_gs(void) __attribute__ ((always_inline));
static inline u32 read_segreg_ss(void) __attribute__ ((always_inline));

static inline u16 read_tr_sel(void) __attribute__ ((always_inline));



/* Calls to read and write control registers */ 
static inline u32 read_cr0(void){
  u32 __cr0;
  __asm__("mov %%cr0,%0\n\t" :"=r" (__cr0));
  return __cr0;
}

static inline void write_cr0(u32 val){
  __asm__("mov %0,%%cr0": :"r" ((u32)val));
}

static inline u32 read_cr3(void){
  u32 __cr3;
  __asm__("mov %%cr3,%0\n\t" :"=r" (__cr3));
  return __cr3;
}

static inline void write_cr3(u32 val){
  __asm__("mov %0,%%cr3\n\t"
          "jmp 1f\n\t"
          "1:"
          : 
          :"r" ((u32)val));
}

static inline u32 read_cr2(void){
  u32 __cr2;
  __asm__("mov %%cr2,%0\n\t" :"=r" (__cr2));
  return __cr2;
}

static inline u32 read_cr4(void){
  u32 __cr4;
  __asm__("mov %%cr4,%0\n\t" :"=r" (__cr4));
  return __cr4;
}

static inline void write_cr4(u32 val){
  __asm__("mov %0,%%cr4": :"r" ((u32)val));
}

//segment register access
static inline u32 read_segreg_cs(void){
  u32 __cs;
  __asm__("mov %%es, %0 \r\n" :"=r" (__cs));
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


#endif

#endif /* __PROCESSOR_H */

