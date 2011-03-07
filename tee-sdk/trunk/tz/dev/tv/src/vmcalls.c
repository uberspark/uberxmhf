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
  int ret;
  unsigned int inbuf1[2]= {(unsigned int)in, (unsigned int)in_len};
  unsigned int outbuf1[2]= {(unsigned int)out, (unsigned int)out_len};

  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_SEAL), "c"((unsigned int)inbuf1), "d"(pcrAtRelease_addr), "S"((unsigned int)outbuf1));
  return ret;
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

  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_UNSEAL), "c"((unsigned int)inbuf2), "d"((unsigned int)outbuf2));
  return ret;
}

__attribute__ ((section (".stext")))
int scode_quote(uint8_t *nonce,
                uint32_t *tpmsel,
                uint8_t *out,
                size_t *out_len)
{
  int ret;
  unsigned int outbuf[2]= {(unsigned int)out, (unsigned int)out_len};

  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_QUOTE), "S"(nonce), "c"(tpmsel), "d"((unsigned int)outbuf));
  return ret;
}

int scode_register(const struct scode_sections_info *pageinfo,
                   const struct scode_params_info *params,
                   const void *entry)
{
  int ret;
  lock_scode_pages(pageinfo);

  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_REG), "c"((unsigned int)pageinfo), "S"((unsigned int)params), "D"((unsigned int)entry));

  return ret;
}

int scode_unregister(void *entry)
{
  int ret;
  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_UNREG), "c"(entry));
  return ret;
}

int scode_test(void)
{
  int ret;
  __asm__ __volatile__(
                       VMCALL
                       :"=a"(ret)
                       : "a"(VMM_TEST));
  return ret;
}

