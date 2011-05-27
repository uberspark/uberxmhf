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

  rtassert_eq(TZDeviceOpen(NULL, NULL, tzDevice),
              TZ_SUCCESS);

  /* download pal 'service' */  
  { 
    tz_session_t tzManagerSession;

    /* open session with device manager */
    rtassert_eq(TZManagerOpen(tzDevice, NULL, &tzManagerSession),
                TZ_SUCCESS);

    /* prepare pal descriptor */
    scode_sections_info_init(&scode_info,
                             param_sz, stack_sz);
    printf("scode sections:\n");
    scode_sections_info_print(&scode_info);

    /* download */
    rtassert_eq(TZManagerDownloadService(&tzManagerSession,
                                         &pal,
                                         sizeof(pal),
                                         tzSvcId),
                TZ_SUCCESS);

    /* close session */
    rtassert_eq(TZManagerClose(&tzManagerSession),
                TZ_SUCCESS);
  }

  /* now open a service handle to the pal */
  {
    tz_operation_t op;
    tz_return_t serviceReturn;
    rtassert_eq(TZOperationPrepareOpen(tzDevice,
                                       tzSvcId,
                                       NULL, NULL,
                                       tzPalSession,
                                       &op),
                TZ_SUCCESS);
    rtassert_eq(TZOperationPerform(&op, &serviceReturn),
                TZ_SUCCESS);
    assert(serviceReturn == TZ_SUCCESS); /* by spec, rv=TZ_SUCCESS implies serviceReturn==TZ_SUCCESS */
    TZOperationRelease(&op);
  }
}

/* static void teardown() */
/* { */
/* } */

int main(void)
{
  tz_device_t tzDevice;
  tz_session_t tzPalSession;
  tz_uuid_t tzSvcId;

  setup(&tzDevice, &tzPalSession, &tzSvcId, pal_entry);

/* #ifdef TEST_VMMCALL */
/*   rv = test_vmcall() || rv; */
/* #endif */

/* #ifdef TEST_WITHOUTPARAM */
/*   rv = test_withoutparam(&tzPalSession) || rv; */
/* #endif */

/* #ifdef TEST_PARAM */
/*   rv = test_param(&tzPalSession) || rv; */
/* #endif */

/* #ifdef TEST_SEAL */
/*   rv = test_seal(&tzPalSession) || rv; */
/* #endif */

/* #ifdef TEST_QUOTE */
/*   rv = test_quote(&tzPalSession) || rv; */
/* #endif */

/* #ifdef TEST_PCR_EXTEND */
/*   rv = test_pcr_extend(&tzPalSession) || rv; */
/* #endif */

/* #ifdef TEST_PCR_READ */
/*   rv = test_pcr_read(&tzPalSession) || rv; */
/* #endif */

  
/*   if (rv) { */
/*     printf("FAIL with rv=%d\n", rv); */
/*   } else { */
/*     printf("SUCCESS with rv=%d\n", rv); */
/*   } */

/*   /\* close session *\/ */
/*   { */
/*     tz_operation_t op; */
/*     tz_return_t serviceReturn; */
/*     tzRet = TZOperationPrepareClose(&tzPalSession, */
/*                                     &op); */
/*     assert(tzRet == TZ_SUCCESS); */
/*     tzRet = TZOperationPerform(&op, &serviceReturn); */
/*     assert(tzRet == TZ_SUCCESS); /\* tzRet==TZ_SUCCESS implies serviceReturn==TZ_SUCCESS *\/ */
/*     TZOperationRelease(&op); */
/*   } */

/*   /\* unload pal *\/ */
/*   { */
/*     tz_session_t tzManagerSession; */

/*     /\* open session with device manager *\/ */
/*     tzRet = TZManagerOpen(&tzDevice, NULL, &tzManagerSession); */
/*     assert(tzRet == TZ_SUCCESS); */

/*     /\* download *\/ */
/*     tzRet = TZManagerRemoveService(&tzManagerSession, */
/*                                    &tzSvcId); */
/*     assert(tzRet == TZ_SUCCESS); */

/*     /\* close session *\/ */
/*     tzRet = TZManagerClose(&tzManagerSession); */
/*     assert(tzRet == TZ_SUCCESS); */
/*   } */

/*   /\* close device *\/ */
/*   { */
/*     tzRet = TZDeviceClose(&tzDevice); */
/*     assert(tzRet == TZ_SUCCESS); */
/*   } */

  return 0;
} 
