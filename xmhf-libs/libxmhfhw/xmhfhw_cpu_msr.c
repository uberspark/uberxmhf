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

// XMHF HW CPU MSR declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHFHW_CPU_MSR_H__
#define __XMHFHW_CPU_MSR_H__


#ifndef __ASSEMBLY__

static inline void rdmsr(u32 msr, u32 *eax, u32 *edx) __attribute__((always_inline));
static inline void wrmsr(u32 msr, u32 eax, u32 edx) __attribute__((always_inline));

//*
static inline void rdmsr(u32 msr, u32 *eax, u32 *edx){
  asm volatile("rdmsr \r\n"
	  :"=a"(*eax), "=d"(*edx)
	  :"c"(msr));
}

//*
static inline void wrmsr(u32 msr, u32 eax, u32 edx){
  asm volatile("wrmsr \r\n"
	  : /* no outputs */
	  :"c"(msr), "a"(eax), "d"(edx));
}


static inline u64 rdmsr64(u32 msr){
    u32 eax, edx;
    rdmsr(msr, &eax, &edx);
    return (((u64)edx << 32) | (u64)eax);
}

static inline void wrmsr64(u32 msr, u64 newval){
    wrmsr(msr, (u32)newval, (u32)((u64)newval >> 32));
}

#endif /* __ASSEMBLY__ */


#endif/* __XMHFHW_CPU_MSR_H__ */
