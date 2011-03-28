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

#include <tv.h>

#include "svcapi.h"

#include <stdint.h>

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

__attribute__ ((section (".stext")))
static uint32_t get_cpu_vendor(void) {
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

__attribute__ ((section (".stext")))
static int vmcall(uint32_t eax, uint32_t ecx, uint32_t edx,
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

#ifndef IS_WINDOWS
#include  <sys/mman.h>
#include <sys/resource.h>
#include  <errno.h>
#endif

#ifdef IS_WINDOWS
#include <windows.h>
#endif

#ifndef IS_WINDOWS
static int lock_range(void *ptr, size_t len)
{
  ptr = (void*)PAGE_ALIGN_4K((uintptr_t)ptr);
  len = PAGE_ALIGN_UP4K(len);

  if(!mlock(ptr, len)) {
    return 0;
  }

  if(errno == ENOMEM) {
    /* try increasing soft limit.
     * this will only work if this process is privileged
     * or if the soft limit is less than the hard limit
     */
    struct rlimit memlock_limit;

    if(getrlimit(RLIMIT_MEMLOCK, &memlock_limit)) {
      perror("getrlimit");
      return -1;
    }
    memlock_limit.rlim_cur += len;
    if(setrlimit(RLIMIT_MEMLOCK, &memlock_limit)) {
        perror("setrlimit");
        return -2;
    }

    /* successfully increased limit. try locking again. */
    if(mlock(ptr, len)) {
      perror("mlock");
      return -3;
    }

    return 0;
  } else {
    perror("mlock");
    return -4;
  }
}
#else
/* mlock always returns an error on cygwin, and get\setrlimit doesn't
   support RLIMIT_MEMLOCK. Instead we use the native windows API
   VirtualLock. Unfortunately this API only guarantees that the pages
   are in physical memory while the process is in physical memory.
   Windows may still swap out the whole process.
*/
static int lock_range(void *ptr, size_t len)
{
  SIZE_T dwMin, dwMax;
  HANDLE hProcess = OpenProcess(PROCESS_QUERY_INFORMATION|PROCESS_SET_QUOTA,
                                FALSE,
                                GetCurrentProcessId());
  ptr = (void*)PAGE_ALIGN_4K((uintptr_t)ptr);
  len = PAGE_ALIGN_UP4K(len);

  if (!GetProcessWorkingSetSize(hProcess, &dwMin, &dwMax)) {
    printf("GetProcessWorkingSetSize failed (%ld)\n",
           GetLastError());
    return -1;
  }

  if (!SetProcessWorkingSetSize(hProcess, dwMin+len, dwMax+len)) {
    printf("GetProcessWorkingSetSize failed (%ld)\n",
           GetLastError());
    return -2;
  }

  if (!VirtualLock(ptr, len)) {
    printf("VirtualLock failed (%ld)\n",
           GetLastError());
    return -3;
  }

  return 0;
}
#endif

static int scode_touch_range(void *ptr, size_t len, int do_write)
{
  int i;

  for(i=0; i<len; i+=PAGE_SIZE) {
    volatile unsigned int *addr = (unsigned int*)(ptr + i);
    volatile unsigned int data = *addr;
    if(do_write) {
      *addr = data;
    }
  }
  return 0;
}

/* get scode pages into physical memory, and lock them there if possible.
 * TV won't cope if these pages are swapped out when a PAL executes.
 */
static void lock_scode_pages(const struct scode_sections_info *scode_info)
{
  int i;

  for(i=0; i < scode_info->section_num; i++) {
    /* first try locking the pages into physical memory */
    if(lock_range((void*)scode_info->ps_str[i].start_addr,
                  scode_info->ps_str[i].page_num*PAGE_SIZE)) {
      printf("warning, couldn't lock scode section %d into physical memory\n", i);
      printf("getting pages swapped in and hoping for the best...\n");
    }

    /* if lock_range succeeded,
     * pages *should* already be in physical memory with
     * correct permissions. however, this doesn't seem to be
     * the case on windows unless we still go ahead and touch
     * them first.
     */
    scode_touch_range((void*)scode_info->ps_str[i].start_addr,
                      scode_info->ps_str[i].page_num*PAGE_SIZE,
                      !(scode_info->ps_str[i].type == SCODE_SECTION_TYPE_SCODE
                        || scode_info->ps_str[i].type == SCODE_SECTION_TYPE_STEXT));

  }
}




__attribute__ ((section (".stext")))
int scode_seal(uint8_t *pcrAtRelease_addr,
               void *in,
               size_t in_len,
               void *out,
               size_t *out_len)
{
  unsigned int inbuf1[2]= {(unsigned int)in, (unsigned int)in_len};
  unsigned int outbuf1[2]= {(unsigned int)out, (unsigned int)out_len};

  return vmcall(VMM_SEAL,
                (uint32_t)inbuf1,
                (uint32_t)pcrAtRelease_addr,
                (uint32_t)outbuf1,
                0);
}

__attribute__ ((section (".stext")))
int scode_unseal(void *in,
                 size_t in_len,
                 void *out,
                 size_t *out_len)
{
  int ret;
  unsigned int inbuf2[2]= {(unsigned int)in, (unsigned int)in_len};
  unsigned int outbuf2[2]= {(unsigned int)out, (unsigned int)out_len};

  return vmcall(VMM_UNSEAL,
                (uint32_t)inbuf2,
                (uint32_t)outbuf2,
                0,
                0);
}

__attribute__ ((section (".stext")))
int scode_quote(uint8_t *nonce,
                uint32_t *tpmsel,
                uint8_t *out,
                size_t *out_len)
{
  int ret;
  unsigned int outbuf[2]= {(unsigned int)out, (unsigned int)out_len};

  return vmcall(VMM_QUOTE,
                (uint32_t)tpmsel,
                (uint32_t)outbuf,
                (uint32_t)nonce,
                0);
}

int scode_register(const struct scode_sections_info *pageinfo,
                   const struct scode_params_info *params,
                   const void *entry)
{
  int ret;
  lock_scode_pages(pageinfo);

  return vmcall(VMM_REG,
                (uint32_t)pageinfo,
                0,
                (uint32_t)params,
                (uint32_t)entry);
}

int scode_unregister(void *entry)
{
  int ret;
  return vmcall(VMM_UNREG,
                (uint32_t)entry,
                0, 0, 0);
}

int scode_share(const void *entry, void *start, size_t len)
{
  /* first try locking the pages into physical memory */
  if(lock_range((void*)start, len)) {
      printf("warning, couldn't lock shared section [%08x,%08x] into physical memory\n",
             start, (uintptr_t)start+len);
      printf("getting pages swapped in and hoping for the best...\n");
  }
  /* touch pages to help make sure. necessary in particular if locking
     failed or we're on windows (where locking doesn't seem to ensure
     the pages are initially mapped) */
  scode_touch_range(start, len, true);

  return vmcall(VMM_SHARE,
                (uint32_t)entry,
                (uint32_t)start,
                (uint32_t)len,
                0);
}


int scode_test(void)
{
  int ret;
  return vmcall(VMM_TEST,
                0, 0, 0, 0);
}

