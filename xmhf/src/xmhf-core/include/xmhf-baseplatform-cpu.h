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

#ifndef __XMHF_BASEPLATFORM_CPU_H__
#define __XMHF_BASEPLATFORM_CPU_H__

#include "xmhf-types.h"

// This macro is used by microsec CPU delay. The delayed time is imprecise.
// [TODO] We assume the CPU frequency is 3.5GHz.
#define CPU_CYCLES_PER_MICRO_SEC        3500UL
#define SEC_TO_CYCLES(x)                (1000UL * 1000UL) * CPU_CYCLES_PER_MICRO_SEC * x


#ifndef __ASSEMBLY__

#define mb()	asm volatile("mfence" ::: "memory")
#define __force	__attribute__((force))

//! @brief Save energy when waiting in a busy loop
static inline void xmhf_cpu_relax(void) 
{
	asm volatile ("pause");
}

// Flushing functions
extern void xmhf_cpu_flush_cache_range(void *vaddr, unsigned int size);

//! @brief Sleep the current core for <us> micro-second.
extern void xmhf_cpu_delay_us(uint64_t us);

#endif	//__ASSEMBLY__



#endif //__XMHF_BASEPLATFORM_CPU_H__
