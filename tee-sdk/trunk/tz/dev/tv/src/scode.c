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

#include "sections.h"

#include "scode.h"

#include <assert.h>
#ifndef IS_WINDOWS
#include  <sys/mman.h>
#include <sys/resource.h>
#include  <errno.h>
#endif
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

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

int scode_touch_range(void *ptr, size_t len, int do_write)
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

size_t scode_ptr_diff(void *end, void *start)
{
  return (uintptr_t)end - (uintptr_t)start;
}

void scode_sections_info_add(struct scode_sections_info *scode_info,
                             int type,
                             void *start_addr, size_t len)
{
  int sections = scode_info->section_num;

  assert(sections < SCODE_MAX_SECTION_NUM);

  scode_info->ps_str[sections].type = type;
  scode_info->ps_str[sections].start_addr = (unsigned int)start_addr;
  assert((len % PAGE_SIZE) == 0);
  scode_info->ps_str[sections].page_num = len / PAGE_SIZE;
  scode_info->section_num++;
}

/* FIXME- allocates memory. how to make sure it gets freed? */
void scode_sections_info_init(struct scode_sections_info *scode_info,
                              size_t param_sz,
                              size_t stack_sz)
{
  uint8_t *mem = NULL;
  uint8_t *param_mem = NULL;
  uint8_t *stack_mem = NULL;

  scode_info->section_num = 0;

  /* add scode section */
  scode_sections_info_add(scode_info, SCODE_SECTION_TYPE_SCODE, &__scode_start,
                          scode_ptr_diff(&__scode_end, &__scode_start));

  /* add stext section */
  if (&__stext_end != &__stext_start) {
    scode_sections_info_add(scode_info, SCODE_SECTION_TYPE_STEXT, &__stext_start,
                            scode_ptr_diff(&__stext_end, &__stext_start));
  }

  /* add sdata section */
  if (&__sdata_end != &__sdata_start) {
    scode_sections_info_add(scode_info, SCODE_SECTION_TYPE_SDATA, &__sdata_start,
                            scode_ptr_diff(&__sdata_end, &__sdata_start));
  }

  /* allocate and add scratch memory areas */

  /* put stack at the lower address, so that overflows won't go into the param
   * memory space. We still need a stronger guarantee that nothing is mapped to
   * the next lowest page, though (see Issue #67)
   */
  param_sz = PAGE_ALIGN_UP4K(param_sz);
  stack_sz = PAGE_ALIGN_UP4K(stack_sz);
  assert(!posix_memalign((void*)&mem, PAGE_SIZE, param_sz+stack_sz));
  stack_mem = mem;
  param_mem = stack_mem+stack_sz;

  scode_sections_info_add(scode_info, SCODE_SECTION_TYPE_STACK, stack_mem, stack_sz);
  scode_sections_info_add(scode_info, SCODE_SECTION_TYPE_PARAM, param_mem, param_sz);
}

void scode_sections_info_print(struct scode_sections_info *scode_info)
{
  int i;
  printf(".section_num = %d\n", scode_info->section_num);
  for(i=0; i<scode_info->section_num; i++) {
    printf(".ps_str[%d].type = %d\n", i, scode_info->ps_str[i].type);
    printf(".ps_str[%d].start_addr = 0x%08x\n", i, scode_info->ps_str[i].start_addr);
    printf(".ps_str[%d].page_num = %d\n", i, scode_info->ps_str[i].page_num);
    printf("\n");
  }
}
