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

/**
 * Need some support for expected PCR digest values.  Let's test while
 * including only a single PCR: #7. Its value is expected to be all
 * zeros for unseal to succeed.
 *
 * PcrComposite that selects PCR #7 with expected contents all zeros:
 * 01 00       // sizeOfSelect (little-endian)
 * 80          // pcrSelection (bit vector)
 * 00 00 00 14 // length of PCR values (big-endian)
 * 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 // 20 bytes of zeros
 *
 * TPM_COMPOSITE_HASH (i.e., compute sha-1 over the above data):
 * c6 08 a1 e6 eb 7d 0f 88 6b 15 75 6b 29 83 be d2 e5 86 19 cb 
 */
const uint8_t digestAtRelease[] = {0xc6, 0x08, 0xa1, 0xe6, 0xeb, 0x7d, 0x0f, 0x88, 0x6b, 0x15,
                                  0x75, 0x6b, 0x29, 0x83, 0xbe, 0xd2, 0xe5, 0x86, 0x19, 0xcb};
int test_seal2(tz_session_t *tzPalSession)
{
  int rv=0;
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tz_sealOp, tz_unsealOp;
  char *in = "hello pal-ly boy";
  uint32_t inLen = strlen(in)+1;
  char *sealOut, *unsealOut;
  uint32_t sealOutLen, unsealOutLen;
  uint8_t *digestAtCreationOut;
  uint32_t digestAtCreationLen;

  TPM_PCR_INFO *pcrInfo=NULL;

  printf("\nSEAL with PCRs\n");

  printf("  sizeof(TPM_PCR_INFO) %d, sizeof(TPM_PCR_SELECTION) %d\n",
         sizeof(TPM_PCR_INFO), sizeof(TPM_PCR_SELECTION));
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_SEAL,
                                   NULL,
                                   &tz_sealOp);
  assert(tzRet == TZ_SUCCESS);
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_UNSEAL,
                                   NULL,
                                   &tz_unsealOp);
  assert(tzRet == TZ_SUCCESS);

  tzRet = TZIEncodeF(&tz_sealOp,
                     "%"TZI_EARRSPC "%"TZI_ESTR,
                     &pcrInfo, sizeof(TPM_PCR_INFO),
                     in);
  if (tzRet) {
    printf("SEAL encoder returned error %d\n", tzRet);
    rv=1;
    goto out;
  }
                  
  memset(pcrInfo, 0, sizeof(TPM_PCR_INFO));
  /* utpm_pcr_select_i(&pcrInfo.pcrSelection, 0); */
  /* utpm_pcr_select_i(&pcrInfo.pcrSelection, 1); */
  /* utpm_pcr_select_i(&pcrInfo.pcrSelection, 2); */
  /* utpm_pcr_select_i(&pcrInfo.pcrSelection, 3); */
  /* utpm_pcr_select_i(&pcrInfo.pcrSelection, 4); */
  /* utpm_pcr_select_i(&pcrInfo.pcrSelection, 5); */
  /* utpm_pcr_select_i(&pcrInfo.pcrSelection, 6); */
  utpm_pcr_select_i(&pcrInfo->pcrSelection, 7);
  memcpy(pcrInfo->digestAtRelease.value, digestAtRelease, TPM_HASH_SIZE);
  print_hex("  pcrInfo: ", (uint8_t*)pcrInfo, sizeof(TPM_PCR_INFO));

  tzRet = TZOperationPerform(&tz_sealOp, &serviceReturn);

  if (tzRet != TZ_SUCCESS) {
    if (tzRet == TZ_ERROR_SERVICE) {
      printf("SEAL pal returned error %d\n",
             serviceReturn);
      rv = 1;
      goto out;
    } else {
      printf("tz system returned error %d\n",
             tzRet);
      rv = 1;
      goto out;
    }
  }
  tzRet = TZIDecodeF(&tz_sealOp,
                     "%"TZI_DARRSPC_NOLEN "%"TZI_DU32,
                     &sealOut, /*skip*/
                     &sealOutLen);
  if (tzRet) {
    printf("SEAL decoder returned error %d\n", tzRet);
    rv = 1;
    goto out;
  }

  print_hex("  sealed data: ", sealOut, sealOutLen);
  
  TZEncodeArray(&tz_unsealOp, sealOut, sealOutLen);
  tzRet = TZOperationPerform(&tz_unsealOp, &serviceReturn);
  unsealOut = TZDecodeArraySpace(&tz_unsealOp, &unsealOutLen);
  digestAtCreationOut = TZDecodeArraySpace(&tz_unsealOp, &digestAtCreationLen);
  unsealOutLen = TZDecodeUint32(&tz_unsealOp);  
  
  if (tzRet != TZ_SUCCESS) {
    if (tzRet == TZ_ERROR_SERVICE) {
      printf("UNSEAL pal returned error %d\n",
             serviceReturn);
      rv = 1;
      goto out;
    } else {
      printf("tz system returned error %d\n",
             tzRet);
      rv = 1;
      goto out;
    }
  }
  if (TZDecodeGetError(&tz_sealOp)) {
    printf("SEAL decoder returned error %d\n", TZDecodeGetError(&tz_sealOp));
    rv = 1;
    goto out;
  }

  if(inLen != unsealOutLen 
     || memcmp(in, unsealOut, inLen) != 0) {
    printf("error- unsealed data doesn't match\n");
    printf("in (%d): %s\n", inLen, in);
    printf("out (%d): %s\n", unsealOutLen, unsealOut);
    rv = 1;
    goto out;
  } else {
    print_hex("  digestAtCreation: ", digestAtCreationOut, digestAtCreationLen);
    printf("Success: unsealed data matches input\n");
  }

 out:
  TZOperationRelease(&tz_sealOp);
  TZOperationRelease(&tz_unsealOp);
  return rv;
}

/**
 * Test Seal without PCR bindings.
 */
int test_seal(tz_session_t *tzPalSession)
{
  int rv=0;
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tz_sealOp, tz_unsealOp;
  char *in = "hello pal-ly boy";
  uint32_t inLen = strlen(in)+1;
  char *sealOut, *unsealOut;
  uint32_t sealOutLen, unsealOutLen;
  uint8_t *digestAtCreationOut;
  uint32_t digestAtCreationLen;

  TPM_PCR_INFO *pcrInfo=NULL;

  printf("\nSEAL withOUT PCRs\n");

  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_SEAL,
                                   NULL,
                                   &tz_sealOp);
  assert(tzRet == TZ_SUCCESS);
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_UNSEAL,
                                   NULL,
                                   &tz_unsealOp);
  assert(tzRet == TZ_SUCCESS);

  tzRet = TZIEncodeF(&tz_sealOp,
                     "%"TZI_EARRSPC "%"TZI_ESTR,
                     &pcrInfo, sizeof(TPM_PCR_INFO),
                     in);
  if (tzRet) {
    printf("SEAL encoder returned error %d\n", tzRet);
    rv=1;
    goto out;
  }
  memset(pcrInfo, 0, sizeof(TPM_PCR_INFO));

  tzRet = TZOperationPerform(&tz_sealOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
      printf("SEAL Op FAILED\n");
      rv = 1;
      goto out;
  }

  tzRet = TZIDecodeF(&tz_sealOp,
                     "%"TZI_DARRSPC_NOLEN "%"TZI_DU32,
                     &sealOut,
                     &sealOutLen);
  if (tzRet != TZ_SUCCESS) {
    printf("SEAL Op decode FAILED with %d\n", tzRet);
    rv = 1;
    goto out;
  }

  print_hex("  sealed data: ", sealOut, sealOutLen);

  assert(!TZIEncodeF(&tz_unsealOp, "%"TZI_EARR, sealOut, sealOutLen));
  tzRet = TZOperationPerform(&tz_unsealOp, &serviceReturn);

  if (tzRet != TZ_SUCCESS) {
    if (tzRet == TZ_ERROR_SERVICE) {
      printf("UNSEAL pal returned error %d\n",
             serviceReturn);
      rv = 1;
      goto out;
    } else {
      printf("tz system returned error %d\n",
             tzRet);
      rv = 1;
      goto out;
    }
  }
  tzRet = TZIDecodeF(&tz_unsealOp,
                     "%"TZI_DARRSPC_NOLEN "%"TZI_DARRSPC "%"TZI_DU32,
                     &unsealOut, /*ignore */
                     &digestAtCreationOut, &digestAtCreationLen,
                     &unsealOutLen);
  if (tzRet) {
    printf("UNSEAL decoder returned error %d\n", tzRet);
    rv = 1;
    goto out;
  }

  if(inLen != unsealOutLen 
     || memcmp(in, unsealOut, inLen) != 0) {
    printf("error- unsealed data doesn't match\n");
    printf("in (%d): %s\n", inLen, in);
    printf("out (%d): %s\n", unsealOutLen, unsealOut);
    rv = 1;
    goto out;
  } else {
    print_hex("  digestAtCreation: ", digestAtCreationOut, digestAtCreationLen);
    printf("Success: unsealed data matches input\n");
  }

 out:
  TZOperationRelease(&tz_sealOp);
  TZOperationRelease(&tz_unsealOp);
  return rv;
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

#define LT_SEAL_FILENAME "sealed.dat"

int just_seal(tz_session_t *tzPalSession) {
  int rv=0;
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tz_sealOp;
  char *in = "hello pal-ly boy";
  unsigned char *sealOut;
  uint32_t sealOutLen;

  TPM_PCR_INFO *pcrInfo=NULL;

  printf("\nLong-Term SEAL withOUT PCRs\n");

  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_SEAL,
                                   NULL,
                                   &tz_sealOp);
  assert(tzRet == TZ_SUCCESS);

  tzRet = TZIEncodeF(&tz_sealOp,
                     "%"TZI_EARRSPC "%"TZI_ESTR,
                     &pcrInfo, sizeof(TPM_PCR_INFO),
                     in);
  if (tzRet) {
    printf("SEAL encoder returned error %d\n", tzRet);
    rv=1;
    goto out;
  }
  memset(pcrInfo, 0, sizeof(TPM_PCR_INFO));

  tzRet = TZOperationPerform(&tz_sealOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
      printf("SEAL Op FAILED\n");
      rv = 1;
      goto out;
  }

  tzRet = TZIDecodeF(&tz_sealOp,
                     "%"TZI_DARRSPC_NOLEN "%"TZI_DU32,
                     &sealOut,
                     &sealOutLen);
  if (tzRet != TZ_SUCCESS) {
    printf("SEAL Op decode FAILED with %d\n", tzRet);
    rv = 1;
    goto out;
  }

  print_hex("  sealed data: ", sealOut, sealOutLen);
  if((rv = puke_file(LT_SEAL_FILENAME, sealOut, sealOutLen)) < 0) {
      printf("puke_file() FAILED with rv %d\n", rv);
      rv = 1;
      goto out;
  } else {
      rv = 0;
  }

 out:
  TZOperationRelease(&tz_sealOp);
  return rv;

}

int just_unseal(tz_session_t *tzPalSession) {
  int rv=0;
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tz_unsealOp;
  unsigned char *sealOut, *unsealOut;
  long sealOutLen, unsealOutLen;
  uint8_t *digestAtCreationOut;
  uint32_t digestAtCreationLen;

  printf("\nLong-Term UnSEAL withOUT PCRs\n");

  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_UNSEAL,
                                   NULL,
                                   &tz_unsealOp);
  assert(tzRet == TZ_SUCCESS);

  sealOutLen = slurp_file(LT_SEAL_FILENAME, &sealOut);
  if(sealOutLen < 0) {
      printf("slurp_file() FAILED\n");
      rv = 1;
      goto out;
  }
  
  print_hex("  sealed data: ", sealOut, sealOutLen);

  assert(!TZIEncodeF(&tz_unsealOp, "%"TZI_EARR, sealOut, (uint32_t)sealOutLen));
  tzRet = TZOperationPerform(&tz_unsealOp, &serviceReturn);

  if (tzRet != TZ_SUCCESS) {
    if (tzRet == TZ_ERROR_SERVICE) {
      printf("UNSEAL pal returned error %d\n",
             serviceReturn);
      rv = 1;
      goto out;
    } else {
      printf("tz system returned error %d\n",
             tzRet);
      rv = 1;
      goto out;
    }
  }
  tzRet = TZIDecodeF(&tz_unsealOp,
                     "%"TZI_DARRSPC_NOLEN "%"TZI_DARRSPC "%"TZI_DU32,
                     &unsealOut, /*ignore */
                     &digestAtCreationOut, &digestAtCreationLen,
                     (uint32_t*)&unsealOutLen);
  if (tzRet) {
    printf("UNSEAL decoder returned error %d\n", tzRet);
    rv = 1;
    goto out;
  }

  printf("  out (%ld): %s\n", unsealOutLen, unsealOut);
  print_hex("  digestAtCreation: ", digestAtCreationOut, digestAtCreationLen);

 out:
  if(NULL != sealOut) { free(sealOut); sealOut = NULL; }
  TZOperationRelease(&tz_unsealOp);
  return rv;

}

/**
 * Test LONG-TERM Seal (i.e., persistent TrustVisor sealing keys). If
 * file LT_SEAL_FILENAME exists, it is assumed to be ciphertext and an
 * attempt to is made to unseal it.  If it does not exist, then some
 * plaintext is sealed and the resulting ciphertext is written to that
 * file.  To fully exercise this, the program must be run twice.  This
 * is because a proper test is impossible with a reboot (or at least a
 * hypervisor reload someday down the road).
 */
int test_longterm_seal(tz_session_t *tzPalSession)
{
    unsigned char *buf = NULL;
    /* Sloppy; wastes a read of the file if it already exists. */
    if(slurp_file(LT_SEAL_FILENAME, &buf) > 0) {
        /* File does exist. */
        free(buf); buf = NULL;
        return just_unseal(tzPalSession);
    }

    return just_seal(tzPalSession);      
}




tz_return_t test_nv_rollback(tz_session_t *tzPalSession) {
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tzOp;
  uint8_t *new;
  uint8_t *old;
  int rv = 0;
  uint32_t i, len = 32; /* XXX get this from somewhere (sizeof sha-256) */

  printf("NV_ROLLBACK\n");

  /* prep operation */
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_NV_ROLLBACK,
                                   NULL,
                                   &tzOp);
  assert(tzRet == TZ_SUCCESS);

  /* encode new value */
  assert(!(TZIEncodeF(&tzOp,
                      "%"TZI_EARRSPC,
                      &new, len)));

  /* Fake the new history summary */
  for(i=0; i<len; i++) {
    new[i] = (uint8_t)i;
  }
  
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
                         "%"TZI_DARRSPC,
                         &old, &len))) {
      rv = 1;
      goto out;
  }

  printf("  len = %d\n", len);
  print_hex("  old NV value: ", old, len);
  print_hex("  new NV value: ", new, len);
  
 out:
  TZOperationRelease(&tzOp);

  if(0 != rv) { printf("...FAILED rv %d\n", rv); }
  return rv;  

}

#define SNAPSHOT_FILENAME "snapshot.bin"

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

 out:
  if(old_snapshot) { free(old_snapshot); old_snapshot = NULL; }
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
          //rv = test_seal2(&tzPalSession) || rv;
          //rv = test_seal(&tzPalSession) || rv;
          rv = test_longterm_seal(&tzPalSession) || rv;
          //rv = test_nv_rollback(&tzPalSession) || rv;
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
