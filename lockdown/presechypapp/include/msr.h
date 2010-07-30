//ia-32 vt/lt msrs
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __MSR_H__
#define __MSR_H__

#define IA32_FEATURE_CONTROL	0x3a

//VMX MSRs
#define IA32_VMX_BASIC	0x480

#define IA32_VMX_CR0_FIXED0	0x486
#define IA32_VMX_CR0_FIXED1 0x487
#define IA32_VMX_CR4_FIXED0 0x488
#define IA32_VMX_CR4_FIXED1 0x489

#define IA32_VMX_PINBASED_CTLS 0x481
#define IA32_VMX_PROCBASED_CTLS 0x482
#define IA32_VMX_PROCBASED_CTLS2 0x48B
#define IA32_VMX_EXIT_CTLS	0x483
#define IA32_VMX_ENTRY_CTLS	0x484


#define IA32_SYSENTER_CS	0x174
#define IA32_SYSENTER_EIP	0x176
#define IA32_SYSENTER_ESP	0x175

#define MSR_EFCR   0x0000003A	// index for Extended Feature Control
#define MSR_K6_STAR                     0xc0000081
#define MSR_EFER	0xc0000080
/* EFER bits */
#define EFER_SCE 0  	/* SYSCALL/SYSRET */
#define EFER_LME 8  	/* Long Mode enable */
#define EFER_LMA 10 	/* Long Mode Active (read-only) */
#define EFER_NXE 11  	/* no execute */

#ifndef __ASSEMBLY__
/* use inline functions rather than macros so compiler can check prototypes
 * gcc manual says that inline function are as fast as macros 
 */

static inline void rdmsr(u32 msr, u32 *eax, u32 *edx)
{
  __asm__("rdmsr"
	  :"=a"(*eax), "=d"(*edx)
	  :"c"(msr));
}

static inline void wrmsr(u32 msr, u32 eax, u32 edx)
{
  __asm__("wrmsr"
	  : /* no outputs */
	  :"c"(msr), "a"(eax), "d"(edx));
}
#endif /* __ASSEMBLY__ */

#endif/* __MSR_H__ */
