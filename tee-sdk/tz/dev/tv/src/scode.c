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

#include <stdbool.h>
#include "sections.h"

#include <tv.h>

#include <assert.h>

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include <trustvisor/trustvisor.h>

#include <tz_platform.h>

size_t tv_ptr_diff(void *end, void *start)
{
  return (uintptr_t)end - (uintptr_t)start;
}

void tv_pal_sections_add(struct tv_pal_sections *scode_info,
                         int type,
                         void *start_addr, size_t len)
{
  int sections = scode_info->num_sections;

  assert(sections < TV_MAX_SECTIONS);

  scode_info->sections[sections].type = type;
  scode_info->sections[sections].start_addr = (unsigned int)start_addr;
  assert((len % PAGE_SIZE) == 0);
  scode_info->sections[sections].page_num = len / PAGE_SIZE;
  scode_info->num_sections++;
}

/* FIXME- allocates memory. how to make sure it gets freed? */
void tv_pal_sections_init(struct tv_pal_sections *scode_info,
                          size_t param_sz,
                          size_t stack_sz)
{
  uint8_t *mem = NULL;
  uint8_t *param_mem = NULL;
  uint8_t *stack_mem = NULL;

  scode_info->num_sections = 0;

  /* add scode section */
  tv_pal_sections_add(scode_info, TV_PAL_SECTION_CODE, &__scode_start,
                      tv_ptr_diff(&__scode_end, &__scode_start));

  /* add sdata section */
  if (&__sdata_end != &__sdata_start) {
    tv_pal_sections_add(scode_info, TV_PAL_SECTION_DATA, &__sdata_start,
                        tv_ptr_diff(&__sdata_end, &__sdata_start));
  }

  /* allocate and add scratch memory areas */

  /* put stack at the lower address, so that overflows won't go into the param
   * memory space. We still need a stronger guarantee that nothing is mapped to
   * the next lowest page, though (see Issue #67)
   */
  param_sz = PAGE_ALIGN_UP4K(param_sz);
  stack_sz = PAGE_ALIGN_UP4K(stack_sz);
  assert(mem = tz_aligned_malloc(param_sz+stack_sz, PAGE_SIZE));
  stack_mem = mem;
  param_mem = stack_mem+stack_sz;

  tv_pal_sections_add(scode_info, TV_PAL_SECTION_STACK, stack_mem, stack_sz);
  tv_pal_sections_add(scode_info, TV_PAL_SECTION_PARAM, param_mem, param_sz);
}

void tv_pal_sections_print(struct tv_pal_sections *scode_info)
{
  int i;
  printf(".num_sections = %d\n", scode_info->num_sections);
  for(i=0; i<scode_info->num_sections; i++) {
    printf(".sections[%d].type = %d\n", i, scode_info->sections[i].type);
    printf(".sections[%d].start_addr = 0x%08x\n", i, scode_info->sections[i].start_addr);
    printf(".sections[%d].page_num = %d\n", i, scode_info->sections[i].page_num);
    printf("\n");
  }
}

tz_return_t tv_tz_init(tz_device_t *tzDevice,
                       tz_session_t *tzPalSession,
                       tz_uuid_t *tzSvcId,
                       pal_fn_t pal_entry,
                       size_t param_sz,
                       size_t stack_sz)
{
  struct tv_pal_sections scode_info;
  tz_return_t rv = TZ_SUCCESS;
  tv_service_t pal = 
    {
      .sPageInfo = &scode_info,
      .sParams = NULL, /* soon to be deprecated? */
      .pEntry = pal_entry,
    };

  rv = TZDeviceOpen(NULL, NULL, tzDevice);
  if (rv != TZ_SUCCESS)
    return rv;

  /* download pal 'service' */  
  { 
    tz_session_t tzManagerSession;

    /* open session with device manager */
    rv = TZManagerOpen(tzDevice, NULL, &tzManagerSession);
    if (rv != TZ_SUCCESS)
      return rv;

    /* prepare pal descriptor */
    tv_pal_sections_init(&scode_info,
                         param_sz, stack_sz);

    /* download */
    rv = TZManagerDownloadService(&tzManagerSession,
                                  &pal,
                                  sizeof(pal),
                                  tzSvcId);
    if (rv != TZ_SUCCESS) {
      TZManagerClose(&tzManagerSession);
      return rv;
    }

    /* close session */
    rv = TZManagerClose(&tzManagerSession);
    if (rv != TZ_SUCCESS)
      return rv;
  }

  /* now open a service handle to the pal */
  {
    tz_operation_t op;
    tz_return_t serviceReturn;
    rv = TZOperationPrepareOpen(tzDevice,
                                tzSvcId,
                                NULL, NULL,
                                tzPalSession,
                                &op);
    if (rv != TZ_SUCCESS) {
      TZDeviceClose(tzDevice);
      return rv;
    }

    rv = TZOperationPerform(&op, &serviceReturn);
    if (rv != TZ_SUCCESS) {
      TZOperationRelease(&op);
      TZDeviceClose(tzDevice);
      return rv;
    }

    TZOperationRelease(&op);
  }

  return rv;
}

tz_return_t tv_tz_teardown(tz_device_t *tzDevice, tz_session_t *tzPalSession, tz_uuid_t *tzSvcId)
{
  tz_return_t rv = TZ_SUCCESS;

  /* close session */
  {
    tz_operation_t op;
    tz_return_t serviceReturn;

    rv = TZOperationPrepareClose(tzPalSession, &op) || rv;
    rv = TZOperationPerform(&op, &serviceReturn) || rv;

    TZOperationRelease(&op);
  }

  /* unload pal */
  {
    tz_session_t tzManagerSession;

    /* open session with device manager */
    rv = TZManagerOpen(tzDevice, NULL, &tzManagerSession) || rv;

    /* unload */
    rv = TZManagerRemoveService(&tzManagerSession, tzSvcId) || rv;

    /* close session */
    rv = TZManagerClose(&tzManagerSession) || rv;
  }

  /* close device */
  rv = TZDeviceClose(tzDevice) || rv;

  return rv;
}
