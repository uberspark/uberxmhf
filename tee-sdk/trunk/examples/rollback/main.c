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

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <errno.h>
#include <string.h>
#include <inttypes.h>

#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/rsa.h>
#include <openssl/sha.h>
#include <openssl/engine.h>

#include "pals.h" /* TODO: fix dependencies so this can go last */

#include <tee-sdk/tv.h>
#include <tee-sdk/tz.h>
#include <tee-sdk/tzmarshal.h>

#include <trustvisor/tv_utpm.h>

/*
 * if 'prefix' != NULL, print it before each line of hex string
 */
void print_hex(const char *prefix, const void *prtptr, size_t size)
{
    size_t i;
    for ( i = 0; i < size; i++ ) {
        if ( i % 16 == 0 && prefix != NULL )
            printf("\n%s", prefix);
        printf("%02x ", *(const uint8_t *)prtptr++);
    }
    printf("\n");
}

/* Read entire file into a newly-allocated buffer. */
/* Returns positive integer representing number of bytes read, or
 * negative value on error.  Don't care about size 0 files. */
static long slurp_file(const char *filename, unsigned char **buf) {
    if(!filename || !buf) return -1;

    FILE *fh = fopen(filename, "rb");
    if(NULL == fh) return -2;

    /* how big is the file? */
    fseek(fh, 0L, SEEK_END);
    long s = ftell(fh);
    rewind(fh);

    /* get some space for its bytes */
    *buf = malloc(s);
    if(NULL == *buf) {
        fclose(fh); fh = NULL;
        return -3;
    }

    fread(*buf, s, 1, fh);
    fclose(fh); fh = NULL;

    printf("  slurp_file successfully read %ld bytes from %s\n",
           s, filename);
    
    return s;
}

/* Create a file (clobbering any existing file) and write the contents
 * of 'bytes' to it. Returns the number of bytes written on success,
 * or a negative value on error. */
static long puke_file(const char *filename, const unsigned char
                      *bytes, long len) {
    if(!filename || !bytes || len < 1) return -1;

    FILE *fh = fopen(filename, "wb");
    if(NULL == fh) return -2;

    if(fwrite(bytes, len, 1, fh) != 1) return -3;
    fclose(fh); fh = NULL;

    printf("  puke_file successfully wrote %ld bytes to %s\n",
           len, filename);
    
    return len;
}


#define SNAPSHOT_FILENAME "snapshot.bin"

static void dump_stderr_from_pal(tz_operation_t *tzOp) {
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

tz_return_t increment_counter(tz_session_t *tzPalSession) {
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tzOp;
  uint8_t *counter, *old_snapshot, *new_snapshot;
  int rv = 0;
  uint32_t counter_len, old_snapshot_len, new_snapshot_len;

  printf("PAL_ARB_INCREMENT\n");

  /* prep operation */
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_ARB_INCREMENT,
                                   NULL,
                                   &tzOp);
  assert(tzRet == TZ_SUCCESS);

  old_snapshot_len = slurp_file(SNAPSHOT_FILENAME, &old_snapshot);
  assert(old_snapshot_len > 0);

  /* 'EARR' means array already allocated.  use EARRSPC to encode
   * "array space"! */
  assert(!TZIEncodeF(&tzOp, "%"TZI_EARR, old_snapshot, old_snapshot_len));

  /* Call PAL */
  tzRet = TZOperationPerform(&tzOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
    rv = 1;
    printf("Failure at %s:%d\n", __FILE__, __LINE__);
    printf("tzRet 0x%08x\n", tzRet);
    goto out;

  }

  tzRet = TZIDecodeF(&tzOp,
                     "%"TZI_DARRSPC "%"TZI_DARRSPC,
                     &counter, &counter_len,
                     &new_snapshot, &new_snapshot_len);
  if (tzRet) {
    printf("UNSEAL decoder returned error %d\n", tzRet);
    rv = 1;
    goto out;
  }

  print_hex("       counter: ", counter, counter_len);
  print_hex("  new_snapshot: ", new_snapshot, new_snapshot_len);

  puke_file(SNAPSHOT_FILENAME, new_snapshot, new_snapshot_len);

 out:
  if(old_snapshot) { free(old_snapshot); old_snapshot = NULL; }
  dump_stderr_from_pal(&tzOp);
  TZOperationRelease(&tzOp);

  if(0 != rv) { printf("...FAILED rv %d\n", rv); }
  return rv;
}

tz_return_t initialize_counter(tz_session_t *tzPalSession) {
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tzOp;
  uint8_t *counter, *snapshot;
  int rv = 0;
  uint32_t counter_len, snapshot_len;

  printf("PAL_ARB_INITIALIZE\n");

  /* prep operation */
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_ARB_INITIALIZE,
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

  puke_file(SNAPSHOT_FILENAME, snapshot, snapshot_len);
  
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
      printf("Usage: %s [-initialize] [-increment] [-test]\n", argv[0]);
      exit(1);
  }
  
  if(!strncmp(argv[1], "-increment", 20)) {
      cmd = PAL_ARB_INCREMENT;
  } else if(!strncmp(argv[1], "-initialize", 20)) {
      cmd = PAL_ARB_INITIALIZE;
  } else {
      /* Assume test */
      cmd = PAL_TEST;
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
          rv = initialize_counter(&tzPalSession) || rv;
          break;
      case PAL_ARB_INCREMENT:
          rv = increment_counter(&tzPalSession) || rv;
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
