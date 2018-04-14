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

#include <stdio.h>
#include <stdbool.h>

#include <tv.h>

#include "vmcalls.h"
#include "config.h"

#if HAVE_SYS_MMAN_H
#include  <sys/mman.h>
#include <sys/resource.h>
#include  <errno.h>
#endif

#if HAVE_WINDOWS_H
#include <windows.h>
#endif

#if HAVE_WINDOWS_H
/* mlock always returns an error on cygwin, and get\setrlimit doesn't
   support RLIMIT_MEMLOCK. Instead we use the native windows API
   VirtualLock. Unfortunately this API only guarantees that the pages
   are in physical memory while the process is in physical memory.
   Windows may still swap out the whole process.
*/
int tv_lock_range(void *ptr, size_t len)
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
#elif HAVE_SYS_MMAN_H
int tv_lock_range(void *ptr, size_t len)
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
      if (!(memlock_limit.rlim_cur > memlock_limit.rlim_max
            && errno == EINVAL)) {
        perror("setrlimit");
      }
      return -2;
    }

    /* successfully increased limit. try locking again. */
    if(mlock(ptr, len)) {
      perror("mlock");
      return -3;
    }

    return 0;
  }

  perror("mlock");
  return -4;
}
#else
int tv_lock_range(void *ptr, size_t len)
{
  return -1;
}
#endif

#if HAS_WINDOWS_H
int tv_unlock_range(void *ptr, size_t len)
{
  return !VirtualUnlock(ptr, len);
}
#elif HAVE_SYS_MMAN_H
int tv_unlock_range(void *ptr, size_t len)
{
  return munlock(ptr, len);
}
#else
int tv_unlock_range(void *ptr, size_t len)
{
  return -1;
}
#endif

int tv_touch_range(void *ptr, size_t len, int do_write)
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
void tv_lock_pal_sections(const struct tv_pal_sections *scode_info)
{
  int i;

  for(i=0; i < scode_info->num_sections; i++) {
    /* first try locking the pages into physical memory */
    if(tv_lock_range((void*)scode_info->sections[i].start_addr,
                  scode_info->sections[i].page_num*PAGE_SIZE)) {
      printf("warning, couldn't lock scode section %d into physical memory\n", i);
      printf("getting pages swapped in and hoping for the best...\n");
    }

    /* if tv_lock_range succeeded,
     * pages *should* already be in physical memory with
     * correct permissions. however, this doesn't seem to be
     * the case on windows unless we still go ahead and touch
     * them first.
     */
    tv_touch_range((void*)scode_info->sections[i].start_addr,
                   scode_info->sections[i].page_num*PAGE_SIZE,
                   !(scode_info->sections[i].type == TV_PAL_SECTION_CODE
                     || scode_info->sections[i].type == TV_PAL_SECTION_SHARED_CODE));

  }
}
void tv_unlock_pal_sections(const struct tv_pal_sections *scode_info)
{
  int i;

  for(i=0; i < scode_info->num_sections; i++) {
    tv_unlock_range((void*)scode_info->sections[i].start_addr,
                    scode_info->sections[i].page_num*PAGE_SIZE);
  }
}

int tv_pal_register(const struct tv_pal_sections *pageinfo,
                    const struct tv_pal_params *params,
                    const void *entry)
{
  int ret;

  return vmcall(TV_HC_REG,
                (uint32_t)pageinfo,
                0,
                (uint32_t)params,
                (uint32_t)entry);
}

int tv_pal_unregister(void *entry)
{
  int ret;
  return vmcall(TV_HC_UNREG,
                (uint32_t)entry,
                0, 0, 0);
}

int tv_pal_share(const void *entry, void **start, size_t *len, size_t count)
{
  int i;

  return vmcall(TV_HC_SHARE,
                (uint32_t)entry,
                (uint32_t)start,
                (uint32_t)len,
                (uint32_t)count);
}

int tv_test(void)
{
  int ret;
  return vmcall(TV_HC_TEST,
                0, 0, 0, 0);
}
