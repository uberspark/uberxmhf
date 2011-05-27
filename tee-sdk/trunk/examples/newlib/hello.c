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

/* 
 * Author - Jim Newsome (jnewsome@no-fuss.com)
 */

#include <stdio.h>
#include <assert.h>

#include <tee-sdk/tv.h>
#include <tee-sdk/tz.h>
#include <tee-sdk/tzmarshal.h>

#include "rtassert.h"

#include "pal.h"

#define rtassert_tzs(x) rtassert_eq(x, TZ_SUCCESS)

/* int ezsetup_int(pal_fn_t pal_entry, */
/*                 pal_name) */
/* #define ezsetup(pal_name, param_sz, stack_sz) */

static void setup(tz_device_t *tzDevice,
                  tz_session_t *tzPalSession,
                  tz_uuid_t *tzSvcId,
                  pal_fn_t pal_entry)
{
  struct scode_sections_info scode_info;
  const size_t param_sz=PAGE_SIZE;
  const size_t stack_sz=PAGE_SIZE;
  tv_service_t pal = 
    {
      .sPageInfo = &scode_info,
      .sParams = NULL, /* soon to be deprecated? */
      .pEntry = pal_entry,
    };

  rtassert_tzs(
               TZDeviceOpen(NULL, NULL, tzDevice));

  /* download pal 'service' */  
  { 
    tz_session_t tzManagerSession;

    /* open session with device manager */
    rtassert_tzs(
                 TZManagerOpen(tzDevice, NULL, &tzManagerSession));

    /* prepare pal descriptor */
    scode_sections_info_init(&scode_info,
                             param_sz, stack_sz);
    printf("scode sections:\n");
    scode_sections_info_print(&scode_info);

    /* download */
    rtassert_tzs(
                 TZManagerDownloadService(&tzManagerSession,
                                          &pal,
                                          sizeof(pal),
                                          tzSvcId));

    /* close session */
    rtassert_tzs(
                 TZManagerClose(&tzManagerSession));
  }

  /* now open a service handle to the pal */
  {
    tz_operation_t op;
    tz_return_t serviceReturn;
    rtassert_tzs(
                 TZOperationPrepareOpen(tzDevice,
                                        tzSvcId,
                                        NULL, NULL,
                                        tzPalSession,
                                        &op));
    rtassert_tzs(
                 TZOperationPerform(&op, &serviceReturn));
    assert(serviceReturn == TZ_SUCCESS); /* by spec, rv=TZ_SUCCESS implies serviceReturn==TZ_SUCCESS */
    TZOperationRelease(&op);
  }
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
  TZOperationRelease(&tzOp);
  
  return rv;
}

static void teardown(tz_device_t *tzDevice, tz_session_t *tzPalSession, tz_uuid_t *tzSvcId)
{
  /* close session */
  {
    tz_operation_t op;
    tz_return_t serviceReturn;

    rtassert_tzs(
                 TZOperationPrepareClose(tzPalSession, &op));

    rtassert_tzs(
                 TZOperationPerform(&op, &serviceReturn));
    assert(serviceReturn == TZ_SUCCESS); /* rv==TZ_SUCCESS implies serviceReturn==TZ_SUCCESS */

    TZOperationRelease(&op);
  }

  /* unload pal */
  {
    tz_session_t tzManagerSession;

    /* open session with device manager */
    rtassert_tzs(
                 TZManagerOpen(tzDevice, NULL, &tzManagerSession));

    /* unload */
    rtassert_tzs(
                 TZManagerRemoveService(&tzManagerSession,
                                        tzSvcId));

    /* close session */
    rtassert_tzs(
                 TZManagerClose(&tzManagerSession));
  }

  /* close device */
  {
    rtassert_tzs(
                 TZDeviceClose(tzDevice));
  }
}

int main(void)
{
  tz_device_t tzDevice;
  tz_session_t tzPalSession;
  tz_uuid_t tzSvcId;
  int rv;

  setup(&tzDevice, &tzPalSession, &tzSvcId, hellopal);
  rv = call_pal(&tzPalSession);
  teardown(&tzDevice, &tzPalSession, &tzSvcId);

  return rv;
} 
