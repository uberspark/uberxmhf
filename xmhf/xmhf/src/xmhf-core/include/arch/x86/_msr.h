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

// msr.h - CPU MSR declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __MSR_H__
#define __MSR_H__

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


#ifndef __ASSEMBLY__
static inline void rdmsr(u32 msr, u32 *eax, u32 *edx) __attribute__((always_inline));
static inline void wrmsr(u32 msr, u32 eax, u32 edx) __attribute__((always_inline));

static inline void rdmsr(u32 msr, u32 *eax, u32 *edx){
  __asm__("rdmsr"
	  :"=a"(*eax), "=d"(*edx)
	  :"c"(msr));
}

static inline void wrmsr(u32 msr, u32 eax, u32 edx){
  __asm__("wrmsr"
	  : /* no outputs */
	  :"c"(msr), "a"(eax), "d"(edx));
}


static inline u64 rdmsr64(uint32_t msr)
{
    u64 rv;

    __asm__ __volatile__ ("rdmsr" : "=A" (rv) : "c" (msr));
    return (rv);
}

static inline void wrmsr64(uint32_t msr, uint64_t newval)
{
    __asm__ __volatile__ ("wrmsr" : : "A" (newval), "c" (msr));
}

#endif /* __ASSEMBLY__ */


#endif/* __MSR_H__ */
