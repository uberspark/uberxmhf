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

/* msr.h AMD K8 MSR definitions and macros
 * Written for TrustVisor by Arvind Seshadri
 */

#ifndef __MSR_H__
#define __MSR_H__

/* AMD K8 MSR addresses */

/* MSRs to be protected via intercepts */
#define MSR_STAR	0xc0000081

#define MSR_VM_CR 	0xc0010114
#define MSR_IGNNE 	0xc0010115 
#define MSR_SMM_CTL 	0xc0010116 /* all bits */
#define MSR_HSAVE_PA 	0xc0010117

/* sysenter/sysexit msr. TrustVisor does not support sysenter/sysexit
 * for system calls at this time. intercept os writes to these msrs
 */
#define MSR_SYSENTER_CS  0x00000174
#define MSR_SYSENTER_EIP 0x00000176

#if 0
/* MTRR-related. see docs/handle_intercepts for description on why we
 * need to intercept reads and writes to certain MTRRs
 */
#define MSR_MTRRcap 0x000000fe /* ro msr. intercept reads to this msr */
#define MSR_MTRRdefType 0x000002ff /* intercept write */
/* intercept read and write to this pair of variable-range mtrr this
 * pair is reserved for TrustVisor. Guest should not read or write to
 * this pair
 */
#define MSR_MTRRphysBase7 0x0000020e
#define MSR_MTRRphysMask7 0x0000020f
#endif

#define MSR_EFER	0xc0000080
/* EFER bits */
#define EFER_SCE 0  	/* SYSCALL/SYSRET */
#define EFER_LME 8  	/* Long Mode enable */
#define EFER_LMA 10 	/* Long Mode Active (read-only) */
#define EFER_NXE 11  	/* no execute */
#define EFER_SVME 12   	/* SVM extensions enable */

/* VM CR MSR bits */
#define VM_CR_DPD 0
#define VM_CR_SVME_DISABLE 4

/* APIC */
#define LAPIC_BASE_MSR 0x1B
#define LAPIC_BASE_MSR_ENABLE (1 << 11)
#define LAPIC_BASE_MSR_BSP (1 << 8)

#ifndef __ASSEMBLY__

typedef union msr_star {
  u64 bytes;
  struct
  {
    u64 syscall_eip:32;
    u64 syscall_cs: 16;    
    u64 sysret_cs:  16;    
  } fields;
} __attribute__ ((packed)) msr_star_t;
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
