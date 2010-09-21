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

// msr.h - CPU MSR declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __MSR_H__
#define __MSR_H__

#define MSR_EFER 0xc0000080     // prevent write to efer.sce 
#define VM_CR_MSR 0xc0010114
#define VM_HSAVE_PA 0xc0010117  //this is critical
#define IGNNE 0xc0010115        //can be used to freeze/restart 
#define SMM_CTL 0xc0010116      //SMRAM control

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
#define VM_CR_SVME_DISABLE 4


#ifndef __ASSEMBLY__

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
#endif /* __ASSEMBLY__ */


#endif/* __MSR_H__ */
