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

#ifndef VMCALLS_H
#define VMCALLS_H

#include <stdint.h>
#include <trustvisor/trustvisor.h>

/* XXX ripped from emhf's processor.h. use it directly? */

#define CPU_VENDOR_INTEL 	0xAB
#define CPU_VENDOR_AMD 		0xCD
#define CPU_VENDOR_UNKNOWN      0x00

#define AMD_STRING_DWORD1 0x68747541
#define AMD_STRING_DWORD2 0x69746E65
#define AMD_STRING_DWORD3 0x444D4163

#define INTEL_STRING_DWORD1	0x756E6547
#define INTEL_STRING_DWORD2	0x49656E69
#define INTEL_STRING_DWORD3	0x6C65746E	

#define cpuid(op, eax, ebx, ecx, edx)		\
({						\
  __asm__ __volatile__("cpuid"				\
          :"=a"(*(eax)), "=b"(*(ebx)), "=c"(*(ecx)), "=d"(*(edx))	\
          :"0"(op), "2" (0));			\
})

static inline uint32_t get_cpu_vendor(void) {
  uint32_t dummy;
  uint32_t vendor_dword1, vendor_dword2, vendor_dword3;
    
  cpuid(0, &dummy, &vendor_dword1, &vendor_dword3, &vendor_dword2);
  if(vendor_dword1 == AMD_STRING_DWORD1 && vendor_dword2 == AMD_STRING_DWORD2
     && vendor_dword3 == AMD_STRING_DWORD3)
    return CPU_VENDOR_AMD;
  else if(vendor_dword1 == INTEL_STRING_DWORD1 && vendor_dword2 == INTEL_STRING_DWORD2
          && vendor_dword3 == INTEL_STRING_DWORD3)
    return CPU_VENDOR_INTEL;
  else
    return CPU_VENDOR_UNKNOWN;

  return 0; /* never reached */
}
/* XXX end processor.h */

static inline int vmcall(uint32_t eax, uint32_t ecx, uint32_t edx,
                         uint32_t esi, uint32_t edi)
{
  /* FIXME - should use a static bool to cache result.
     However, this is tricky since we need to store in different
     locations depending if we're executing inside a pal or not. */
  switch(get_cpu_vendor()) {
  case CPU_VENDOR_INTEL:
    __asm__ __volatile__(
                         "vmcall\n\t"
                         :"=a"(eax)
                         : "a"(eax), "c"(ecx), "d"(edx),
                           "S"(esi), "D"(edi));
    break;
  case CPU_VENDOR_AMD:
    __asm__ __volatile__(
                         "vmmcall\n\t"
                         :"=a"(eax)
                         : "a"(eax), "c"(ecx), "d"(edx),
                           "S"(esi), "D"(edi));
    break;
  default:
    eax = -1;
  }
  return eax;
}

#endif
