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

/* 
 * Author - Jon McCune (jon@no-fuss.com)
 */

#include <stdio.h>
#include <assert.h>
#include <stdint.h>
#include <stdbool.h>

#include <tee-sdk/tv.h>
#include <tee-sdk/tz.h>
#include <tee-sdk/tzmarshal.h>

#include "rtassert.h"

#include "pal.h"

#define rtassert_tzs(x) rtassert_eq(x, TZ_SUCCESS)

void dump_stderr_from_pal(tz_operation_t *tzOp) {
  tz_return_t tzRet;
  uint8_t *stderr_buf;
  size_t stderr_buf_len;
  char last;

  tzRet = TZIDecodeF(tzOp,
                     "%"TZI_DARRSPC,
                     &stderr_buf, &stderr_buf_len);
  if (tzRet) {
    printf("[ERROR] PAL's stderr unavailable. tzRet = %d\n", tzRet);
    return;
  }

  /* Take care to NULL-terminate the string */
  last = stderr_buf[stderr_buf_len-1];
  stderr_buf[stderr_buf_len-1] = '\0'; 
  printf("********************* BEGIN PAL's STDERR ****************************************\n");
  printf("%s%c%s", stderr_buf, last, last == '\n' ? "" : "\n");
  printf("********************* END PAL's STDERR ******************************************\n");
}

static int call_pal(tz_session_t *tzPalSession)
{
  tz_operation_t tzOp;
  tz_return_t tzRet, serviceReturn;
  int rv=0;

  rtassert_tzs(
               TZOperationPrepareInvoke(tzPalSession,
                                        PAL_HELLO,
                                        NULL,
                                        &tzOp));

  tzRet = TZOperationPerform(&tzOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
    if (tzRet == TZ_ERROR_SERVICE) {
      printf("withoutparam pal returned error %d\n",
             serviceReturn);
      rv = 1;
    } else {
      printf("tz system returned error %d\n",
             tzRet);
      rv = 1;
    }
  }
  dump_stderr_from_pal(&tzOp);
  TZOperationRelease(&tzOp);
  
  return rv;
}

int main(void)
{
  tz_device_t tzDevice;
  tz_session_t tzPalSession;
  tz_uuid_t tzSvcId;
  int rv=0;

  rtassert_tzs(tv_tz_init(&tzDevice,
                          &tzPalSession,
                          &tzSvcId,
                          prngpal,
                          PAGE_SIZE,
                          PAGE_SIZE));

  rv = call_pal(&tzPalSession);

  rtassert_tzs(tv_tz_teardown(&tzDevice,
                              &tzPalSession,
                              &tzSvcId));

  return rv;
} 
