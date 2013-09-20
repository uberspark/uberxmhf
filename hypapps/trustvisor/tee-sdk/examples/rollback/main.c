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

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <errno.h>
#include <string.h>
#include <inttypes.h>

#include "pals.h" /* TODO: fix dependencies so this can go last */

#include <tee-sdk/tv.h>
#include <tee-sdk/tz.h>
#include <tee-sdk/tzmarshal.h>

#include <trustvisor/tv_utpm.h>

#include "libarb.h" /* for arb_err_t */
#include "libarbtools.h"

bool g_fake_crash = false;

/**
 * Extremely redundant with respect to increment_counter().
 * TODO: Tighten everything up.
 */
tz_return_t attempt_recovery(tz_session_t *tzPalSession) {
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tzOp;
  void *counter, *old_snapshot, *new_snapshot;
  int rv = 0;
  size_t counter_len, old_snapshot_len, new_snapshot_len;
  pal_request_t *req;

  printf("PAL_ARB_ATTEMPT_RECOVERY\n");

  /* prep operation */
  /* No files to write out prior to recovery */
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_ARB_ATTEMPT_RECOVERY,
                                   NULL,
                                   &tzOp);
  assert(tzRet == TZ_SUCCESS);

  assert(sizeof(pal_request_t) == slurp_file(THIS_REQUEST_FILENAME, (void**)&req));
  print_hex("  req: ", req, sizeof(pal_request_t));
  old_snapshot_len = slurp_file(LAST_SNAPSHOT_FILENAME, &old_snapshot);
  assert(old_snapshot_len > 0);

  /* 'EARR' means array already allocated.  use EARRSPC to encode
   * "array space"! */
  assert(!TZIEncodeF(&tzOp,
                     "%"TZI_EARR "%"TZI_EARR,
                     req, sizeof(pal_request_t),
                     old_snapshot, old_snapshot_len));

  /* Call PAL */
  tzRet = TZOperationPerform(&tzOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
    rv = 1;
    printf("%s:%d: tzRet 0x%08x\n", __FILE__, __LINE__, tzRet);
    goto out;
  }

  tzRet = TZIDecodeF(&tzOp,
                     "%"TZI_DARRSPC "%"TZI_DARRSPC,
                     &counter, &counter_len,
                     &new_snapshot, &new_snapshot_len);
  if (tzRet) {
    printf("Output decoder returned error %d\n", tzRet);
    rv = 1;
    goto out;
  }

  print_hex("       counter: ", counter, counter_len);
  print_hex("  new_snapshot: ", new_snapshot, new_snapshot_len);

  puke_file(THIS_SNAPSHOT_FILENAME, new_snapshot, new_snapshot_len);

  /* No need to rename request, just snapshot */
  if(0 != rename(THIS_SNAPSHOT_FILENAME, LAST_SNAPSHOT_FILENAME)) {
      perror("Renaming snapshot from this to last!");
      exit(1);
  }

 out:
  if(old_snapshot) { free(old_snapshot); old_snapshot = NULL; }
  dump_stderr_from_pal(&tzOp);
  TZOperationRelease(&tzOp);

  if(0 != rv) { printf("...FAILED rv %d\n", rv); }
  return rv;
}

tz_return_t increment_counter(tz_session_t *tzPalSession) {
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tzOp;
  void *counter, *old_snapshot, *new_snapshot;
  int rv = 0;
  size_t counter_len, old_snapshot_len, new_snapshot_len;
  pal_request_t req;

  printf("PAL_ARB_INCREMENT\n");

  /* prep operation */
  req.cmd = PAL_ARB_INCREMENT;
  puke_file(THIS_REQUEST_FILENAME, &req, sizeof(pal_request_t));
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   req.cmd,
                                   NULL,
                                   &tzOp);
  assert(tzRet == TZ_SUCCESS);

  old_snapshot_len = slurp_file(LAST_SNAPSHOT_FILENAME, &old_snapshot);
  assert(old_snapshot_len > 0);

  /* 'EARR' means array already allocated.  use EARRSPC to encode
   * "array space"! */
  assert(!TZIEncodeF(&tzOp,
                     "%"TZI_EARR "%"TZI_EARR,
                     &req, sizeof(pal_request_t),
                     old_snapshot, old_snapshot_len));

  /* Call PAL */
  tzRet = TZOperationPerform(&tzOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
    rv = tzRet;
    printf("%s:%d: tzRet 0x%08x\n", __FILE__, __LINE__, tzRet);
    goto out;

  }

  tzRet = TZIDecodeF(&tzOp,
                     "%"TZI_DARRSPC "%"TZI_DARRSPC,
                     &counter, &counter_len,
                     &new_snapshot, &new_snapshot_len);
  if (tzRet) {
    printf("Output decoder returned error %d\n", tzRet);
    rv = tzRet;
    goto out;
  }

  print_hex("       counter: ", counter, counter_len);
  print_hex("  new_snapshot: ", new_snapshot, new_snapshot_len);


  /* Support a "fake crash" to test recovery. */
  if(!g_fake_crash) {
      puke_file(THIS_SNAPSHOT_FILENAME, new_snapshot, new_snapshot_len);

      /* Now rename THIS* to LAST* */
      if(0 != rename(THIS_SNAPSHOT_FILENAME, LAST_SNAPSHOT_FILENAME)) {
          perror("Renaming snapshot from this to last!");
          exit(1);
      }
      /* No need for LAST_REQUEST, but keeping it anyways. See
       * discussion in libarbtools.h */
      if(0 != rename(THIS_REQUEST_FILENAME, LAST_REQUEST_FILENAME)) {
          perror("Renaming request from this to last!");
          exit(1);
      }
  } else {
      printf("**********************************************\n");
      printf("*** Faking a crash. Not updating snapshot! ***\n");
      printf("**********************************************\n");
  }

 out:
  if(old_snapshot) { free(old_snapshot); old_snapshot = NULL; }
  dump_stderr_from_pal(&tzOp);
  TZOperationRelease(&tzOp);

  if(TZ_ERROR_SERVICE == rv && ARB_ERECOVERYNEEDED == serviceReturn) {
      printf("***************************************************\n");
      printf("increment_counter() failed with ARB_ERECOVERYNEEDED\n");
      printf("ATTEMPTING RECOVERY!\n");
      printf("***************************************************\n");
      rv = attempt_recovery(tzPalSession);
  }
  
  if(0 != rv) { printf("...FAILED rv %d\n", rv); }
  return rv;
}

tz_return_t initialize_counter(tz_session_t *tzPalSession) {
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tzOp;
  uint8_t *counter, *snapshot;
  int rv = 0;
  size_t counter_len, snapshot_len;
  pal_request_t req;

  printf("PAL_ARB_INITIALIZE\n");

  /* prep operation */
  req.cmd = PAL_ARB_INITIALIZE;
  puke_file(THIS_REQUEST_FILENAME, &req, sizeof(pal_request_t));
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   req.cmd,
                                   NULL,
                                   &tzOp);
  assert(tzRet == TZ_SUCCESS);
  
  /* Call PAL */
  tzRet = TZOperationPerform(&tzOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
    rv = 1;
    printf("Failure at %s:%d\n", __FILE__, __LINE__); 
    printf("tzRet 0x%08x\n", tzRet);
    goto out;

  }
  
  if (TZDecodeGetError(&tzOp) != TZ_SUCCESS) {
    rv = 1;
    printf("Failure at %s:%d\n", __FILE__, __LINE__); 
    printf("tzRet 0x%08x\n", tzRet);
    goto out;

  }

  if((tzRet = TZIDecodeF(&tzOp,
                         "%"TZI_DARRSPC "%"TZI_DARRSPC,
                         &counter, &counter_len,
                         &snapshot, &snapshot_len))) {
      rv = 1;
      goto out;
  }

  printf("  counter_len = %d, snapshot_len = %d\n", counter_len, snapshot_len);
  print_hex("  counter value: ", counter, counter_len);
  print_hex("  snapshot:      ", snapshot, snapshot_len);

  puke_file(LAST_SNAPSHOT_FILENAME, snapshot, snapshot_len);
  
 out:
  dump_stderr_from_pal(&tzOp);
  TZOperationRelease(&tzOp);

  if(0 != rv) { printf("...FAILED rv %d\n", rv); }
  return rv;
}


// function main
// register some sensitive code and data in libfoo.so and call bar()
int main(int argc, char *argv[])
{
  struct tv_pal_sections scode_info;
  int rv = 0;
  tz_return_t tzRet;
  tz_device_t tzDevice;
  tz_session_t tzPalSession;
  tv_service_t pal = 
    {
      .sPageInfo = &scode_info,
      .sParams = NULL, /* soon to be deprecated? */
      .pEntry = pals,
    };
  tz_uuid_t tzSvcId;
  PAL_CMD cmd;
  
  if(argc < 2) {
      printf("Usage: %s [-initialize][-increment][-test] [-fakecrash]\n", argv[0]);
      exit(1);
  }
  
  if(!strncmp(argv[1], "-increment", 20)) {
      cmd = PAL_ARB_INCREMENT;
  } else if(!strncmp(argv[1], "-initialize", 20)) {
      cmd = PAL_ARB_INITIALIZE;
  } else {
      /* Assume test */
      cmd = PAL_TEST;
      printf("Test Unimplemented.\n");
      exit(1);
  }

  if(argc > 2 && !strncmp(argv[2], "-fakecrash", 20)) {
      g_fake_crash = true;
  }
  
  /* open isolated execution environment device */
  {
    tzRet = TZDeviceOpen(NULL, NULL, &tzDevice);
    assert(tzRet == TZ_SUCCESS);
  }

  /* download pal 'service' */  
  { 
    tz_session_t tzManagerSession;

    /* open session with device manager */
    tzRet = TZManagerOpen(&tzDevice, NULL, &tzManagerSession);
    assert(tzRet == TZ_SUCCESS);

    /* prepare pal descriptor */
    tv_pal_sections_init(&scode_info,
                         PAGE_SIZE, PAGE_SIZE);
    printf("scode sections:\n");
    tv_pal_sections_print(&scode_info);

    /* download */
    tzRet = TZManagerDownloadService(&tzManagerSession,
                                     &pal,
                                     sizeof(pal),
                                     &tzSvcId);
    assert(tzRet == TZ_SUCCESS);

    /* close session */
    tzRet = TZManagerClose(&tzManagerSession);
    assert(tzRet == TZ_SUCCESS);
  }

  /* now open a service handle to the pal */
  {
    tz_operation_t op;
    tz_return_t serviceReturn;
    tzRet = TZOperationPrepareOpen(&tzDevice,
                                   &tzSvcId,
                                   NULL, NULL,
                                   &tzPalSession,
                                   &op);
    assert(tzRet == TZ_SUCCESS);
    tzRet = TZOperationPerform(&op, &serviceReturn);
    assert(tzRet == TZ_SUCCESS); /* tzRet==TZ_SUCCESS implies serviceReturn==TZ_SUCCESS */
    TZOperationRelease(&op);
  }

  switch(cmd) {
      case PAL_ARB_INITIALIZE:
          rv = initialize_counter(&tzPalSession);
          break;
      case PAL_ARB_INCREMENT:
          rv = increment_counter(&tzPalSession);
          break;
      case PAL_TEST:
      default:
          /* No tests presently. */
          break;
  }
  
  if (rv) {
    printf("FAIL with rv=%d\n", rv);
  } else {
    printf("SUCCESS with rv=%d\n", rv);
  }

  /* close session */
  {
    tz_operation_t op;
    tz_return_t serviceReturn;
    tzRet = TZOperationPrepareClose(&tzPalSession,
                                    &op);
    assert(tzRet == TZ_SUCCESS);
    tzRet = TZOperationPerform(&op, &serviceReturn);
    assert(tzRet == TZ_SUCCESS); /* tzRet==TZ_SUCCESS implies serviceReturn==TZ_SUCCESS */
    TZOperationRelease(&op);
  }

  /* unload pal */
  {
    tz_session_t tzManagerSession;

    /* open session with device manager */
    tzRet = TZManagerOpen(&tzDevice, NULL, &tzManagerSession);
    assert(tzRet == TZ_SUCCESS);

    /* download */
    tzRet = TZManagerRemoveService(&tzManagerSession,
                                   &tzSvcId);
    assert(tzRet == TZ_SUCCESS);

    /* close session */
    tzRet = TZManagerClose(&tzManagerSession);
    assert(tzRet == TZ_SUCCESS);
  }

  /* close device */
  {
    tzRet = TZDeviceClose(&tzDevice);
    assert(tzRet == TZ_SUCCESS);
  }

  return rv;
} 

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */
