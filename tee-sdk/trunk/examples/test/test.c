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
#include "pals.h"
//#include  "config.h"
#include  <sys/mman.h>
#include  <errno.h>
#include  <string.h>

#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/rsa.h>
#include <openssl/sha.h>
#include <openssl/engine.h>

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


/* int test_marshal() */
/* { */
/*   tzi_encode_buffer_t *psEnc, *psEnc2; */
/*   char *in, *out; */
/*   uint32_t inLen, outLen; */
/*   uint32_t inI, outI; */

/*   in = "hello pal-ly boy"; */
/*   inLen = strlen(in); */
/*   inI = 42; */

/*   posix_memalign((void**)&psEnc, 8, 1000); */
/*   posix_memalign((void**)&psEnc2, 8, 1000); */
/*   TZIEncodeBufInit(psEnc, 1000); */
/*   TZIEncodeBufInit(psEnc2, 1000); */

/*   TZIEncodeArray(psEnc, in, inLen); */
/*   TZIEncodeUint32(psEnc, inI); */

/*   TZIEncodeToDecode(psEnc); */
/*   memcpy(psEnc2, psEnc, 1000); */

/*   out = TZIDecodeArraySpace(psEnc2, &outLen); */
/*   printf("returned string (%d): %s\n", outLen, out); */

/*   outI = TZIDecodeUint32(psEnc2); */
/*   printf("returned int %u\n", outI); */

/*   return 0; */
/* } */

int test_vmcall()
{
  printf("VMMCALL\n");
  tv_test();
  printf("VMMCALL returned\n");
  return 0;
}

int test_withoutparam(tz_session_t *tzPalSession)
{
  tz_return_t tzRet;
  tz_operation_t tzOp;
  tz_return_t serviceReturn;
  int rv=0;

  printf("\nWITHOUTPARAM\n");

  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_WITHOUTPARAM,
                                   NULL,
                                   &tzOp);
  assert(tzRet == TZ_SUCCESS);

  printf("running PAL\n");
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

int test_param(tz_session_t *tzPalSession)
{
  int i;
  uint32_t output;
  tz_return_t tzRet;
  tz_operation_t tzOp;
  tz_return_t serviceReturn;
  int rv=0;

  printf("\nPARAM\n");

  for(i=0;i<3; i++) { /* FIXME: bump this up when performance issue is addressed */
    tzRet = TZOperationPrepareInvoke(tzPalSession,
                                     PAL_PARAM,
                                     NULL,
                                     &tzOp);
    assert(tzRet == TZ_SUCCESS);
    TZEncodeUint32(&tzOp, i);

    printf("running PAL\n");
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

    output = TZDecodeUint32(&tzOp);
    if (TZDecodeGetError(&tzOp) != TZ_SUCCESS) {
      printf("error: tz decoder returned status %d\n", TZDecodeGetError(&tzOp));
      rv = 1;
    }

    if(output != i+1) {
      printf("error: output=%d, i=%d\n", output, i);
      rv=1;
    }

    TZOperationRelease(&tzOp);    
  }
  
  return rv;
}

int test_seal(tz_session_t *tzPalSession)
{
  int rv=0;
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tz_sealOp, tz_unsealOp;
  char *in = "hello pal-ly boy";
  uint32_t inLen = strlen(in)+1;
  char *sealOut, *unsealOut;
  uint32_t sealOutLen, unsealOutLen;

  printf("\nSEAL\n");
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

  TZEncodeArray(&tz_sealOp, in, inLen);
  tzRet = TZOperationPerform(&tz_sealOp, &serviceReturn);
  sealOut = TZDecodeArraySpace(&tz_sealOp, &sealOutLen);
  sealOutLen = TZDecodeUint32(&tz_sealOp);
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
  if (TZDecodeGetError(&tz_sealOp)) {
    printf("SEAL decoder returned error %d\n", TZDecodeGetError(&tz_sealOp));
    rv = 1;
    goto out;
  }

  print_hex("sealed data:", sealOut, sealOutLen);
  
  TZEncodeArray(&tz_unsealOp, sealOut, sealOutLen);
  tzRet = TZOperationPerform(&tz_unsealOp, &serviceReturn);
  unsealOut = TZDecodeArraySpace(&tz_unsealOp, &unsealOutLen);
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
    printf("in (%d): %s", inLen, in);
    printf("out (%d): %s", unsealOutLen, unsealOut);
    rv = 1;
    goto out;
  } else {
    printf("unsealed data matches input\n");
  }

 out:
  TZOperationRelease(&tz_sealOp);
  TZOperationRelease(&tz_unsealOp);
  return rv;
}

int test_id_getpub(tz_session_t *tzPalSession, uint8_t *rsaMod)
{
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tzOp;
  uint8_t *rsaModulus = NULL;
  uint32_t rsaModLen;
  uint32_t rv = 0;
  
  printf("ID_GETPUB\n");

  assert(NULL != rsaMod);
  
  /* prep operation */
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_ID_GETPUB,
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

  /* read out RSA public key modulus */
  rsaModulus = TZDecodeArraySpace(&tzOp, &rsaModLen);
  if (rsaModulus == NULL) {
    rv = 1;
    goto out;
  }

  assert(rsaModLen == TPM_RSA_KEY_LEN);

  memcpy(rsaMod, rsaModulus, rsaModLen);

  print_hex("  rsaMod: ", rsaMod, TPM_RSA_KEY_LEN);
  
 out:
  TZOperationRelease(&tzOp);

  if(0 != rv) { printf("...FAILED rv %d\n", rv); }
  return rv;  
}

int verify_quote(uint8_t *tpm_pcr_composite, uint32_t tpc_len, uint8_t *sig, uint32_t sig_len,
                 TPM_NONCE *externalnonce, uint8_t* rsaMod) {
    TPM_QUOTE_INFO quote_info;
    RSA *rsa = NULL;
    int rv=0;

    /* 1) 1.1.0.0 for consistency w/ TPM 1.2 spec */
    *((uint32_t*)&quote_info.version) = 0x00000101; 
    /* 2) 'QUOT' */
    *((uint32_t*)quote_info.fixed) = 0x544f5551; 

    /* 3) SHA-1 hash of TPM_PCR_COMPOSITE */
    SHA1(tpm_pcr_composite, tpc_len, quote_info.digestValue.value);

    print_hex("  tpm_pcr_composite: ", tpm_pcr_composite, tpc_len);
    
    print_hex("  COMPOSITE_HASH: ", quote_info.digestValue.value, TPM_HASH_SIZE);
    
    /* 4) external nonce */
    memcpy(quote_info.externalData.nonce, externalnonce->nonce, TPM_HASH_SIZE);

    print_hex("  quote_info: ", (uint8_t*)&quote_info, sizeof(TPM_QUOTE_INFO));    

    /**
     * Assemble the public key used to check the quote.
     */    

    if(NULL == (rsa = RSA_new())) {
        printf("ERROR: RSA_new() failed\n");
        return 1;
    }

    /* N */
    if(NULL == (rsa->n = BN_bin2bn(rsaMod, TPM_RSA_KEY_LEN, NULL))) {
        printf("ERROR: BN_bin2bn() failed\n");
        goto out;
    }

    /* E */
    if(0 == BN_dec2bn(&rsa->e, "65537")) {
        printf("ERROR: BN_dec2bn() failed\n");
        goto out;
    }        

    /**
     * Verify the signature!
     */
    
    uint8_t valData[TPM_HASH_SIZE];
    SHA1((uint8_t*)&quote_info, sizeof(TPM_QUOTE_INFO), valData);
    print_hex("  valData: ", valData, TPM_HASH_SIZE);

    if(1 != RSA_verify(NID_sha1, valData, TPM_HASH_SIZE, sig, sig_len, rsa)) {
        printf("ERROR: Quote verification FAILED!\n");
        ERR_print_errors_fp(stdout);
        rv = 1;
        goto out;
    } else {
        printf("  RSA_verify: SUCCESSfully verified quote\n");
        rv = 0;
    }
    
  out:
    /* RSA_free() frees the RSA structure and its components. The key
     * is erased before the memory is returned to the system. */
    if(rsa) { RSA_free(rsa); rsa = NULL; }
    
    return 0;
}

int test_quote(tz_session_t *tzPalSession)
{
  TPM_NONCE *nonce;
  TPM_PCR_SELECTION *tpmsel;
  uint8_t *quote;
  uint32_t quoteLen = TPM_MAX_QUOTE_LEN;

  tz_return_t tzRet, serviceReturn;
  tz_operation_t tz_quoteOp;
  
  int i;
  int rv = 0;
  
  uint8_t rsaMod[TPM_RSA_KEY_LEN];

  /**
   * First get the public key that will eventually be used to verify the quote.
   */
  
  if(0 != test_id_getpub(tzPalSession, rsaMod)) {
      printf("test_id_getpub FAILED!\n");
      goto out;
  }
  
  printf("\nQUOTE\n");

  /* prep operation */
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_QUOTE,
                                   NULL,
                                   &tz_quoteOp);
  assert(tzRet == TZ_SUCCESS);

  /* setup nonce */
  nonce = TZEncodeArraySpace(&tz_quoteOp, sizeof(TPM_NONCE));
  if (nonce == NULL) {
    rv = 1;
    goto out;
  }
  for(i=0; i<sizeof(TPM_NONCE); i++) {
    nonce->nonce[i] = (uint8_t)i;
  }

  /* setup tpmsel */
  tpmsel = TZEncodeArraySpace(&tz_quoteOp, sizeof(TPM_PCR_SELECTION));
  if(tpmsel == NULL) {
      rv = 1;
      goto out;
  }
  /* select all PCRs for inclusion in test quote */
  assert(8 == TPM_PCR_NUM); /* want this test to fail if uTPM's grow more uPCRs */
  tpmsel->sizeOfSelect = 1; /* 1 byte to select 8 PCRs */
  for(i=0; i<8; i++) {
      utpm_pcr_select_i(tpmsel, i);
  }  
  
  /* call pal */
  tzRet = TZOperationPerform(&tz_quoteOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
    rv = 1;
    goto out;
  }
  
  /* get quote */
  quote = TZDecodeArraySpace(&tz_quoteOp, &quoteLen);
  if (quote == NULL) {
    rv = 1;
    goto out;
  }
  printf("  max quoteLen = %d\n", quoteLen);

  quoteLen = TZDecodeUint32(&tz_quoteOp);
  printf("  actual quoteLen = %d\n", quoteLen);
  
  if (TZDecodeGetError(&tz_quoteOp) != TZ_SUCCESS) {
    rv = 1;
    goto out;
  }

  if(quoteLen <= TPM_MAX_QUOTE_LEN) {
      //print_hex("  Q: ", quote, quoteLen);
  } else {
      printf("ERROR: quoteLen (%d) > TPM_MAX_QUOTE_LEN! First 16 bytes of response:\n", quoteLen);
      print_hex("  Q! ", quote, 16);
      goto out;
  }


  /* TODO: Verify the signature in the Quote */
  //[ TPM_PCR_COMPOSITE | sigSize | sig ]
  uint32_t tpm_pcr_composite_size = quoteLen - TPM_RSA_KEY_LEN - sizeof(uint32_t);
  uint32_t sigSize = *((uint32_t*)(quote+tpm_pcr_composite_size));
  uint8_t* sig = quote + tpm_pcr_composite_size + sizeof(uint32_t);

  printf("  tpm_pcr_composite_size %d, sigSize %d\n",
         tpm_pcr_composite_size, sigSize);
  
  assert(sigSize == TPM_RSA_KEY_LEN);

  print_hex("  sig: ", sig, TPM_RSA_KEY_LEN);
  
  if((rv = verify_quote(quote, tpm_pcr_composite_size, sig, sigSize, nonce, rsaMod)) != 0) {
      printf("verify_quote FAILED\n");
  }

  out:
  TZOperationRelease(&tz_quoteOp);
  
  return rv;
}

int test_pcr_extend(tz_session_t *tzPalSession)
{
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tzOp;
  uint8_t *meas_ptr;
  uint32_t pcr_idx = 3; /* arbitrary; eventually loop through them all */
  int rv = 0;
  uint32_t i;

  printf("\nPCR_EXTEND\n");

  /* prep operation */
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_PCR_EXTEND,
                                   NULL,
                                   &tzOp);
  assert(tzRet == TZ_SUCCESS);

  /* encode PCR index */
  TZEncodeUint32(&tzOp, pcr_idx);

  /* Prepare space to put measurement */
  meas_ptr = TZEncodeArraySpace(&tzOp, TPM_HASH_SIZE);
  if (meas_ptr == NULL) {
    rv = 1;
    printf("Failure at %s:%d\n", __FILE__, __LINE__); 
    printf("tzRet 0x%08x\n", tzRet);
    goto out;

  }
  /* Fake the measurement */
  for(i=0; i<TPM_HASH_SIZE; i++) {
    meas_ptr[i] = (uint8_t)i;
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

 out:
  TZOperationRelease(&tzOp);

  if(0 != rv) { printf("...FAILED rv %d\n", rv); }
  return rv;  
}

int test_pcr_read_i(tz_session_t *tzPalSession, uint32_t pcr_idx)
{
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tzOp;
  uint8_t *meas;
  uint32_t measLen = 0;
  int rv = 0;

  /* prep operation */
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_PCR_READ,
                                   NULL,
                                   &tzOp);
  assert(tzRet == TZ_SUCCESS);

  /* encode PCR index */
  TZEncodeUint32(&tzOp, pcr_idx);
  
  /* Call PAL */
  tzRet = TZOperationPerform(&tzOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
    rv = 1;
    printf("Failure at %s:%d\n", __FILE__, __LINE__); 
    printf("tzRet 0x%08x\n", tzRet);
    goto out;

  }

  meas = TZDecodeArraySpace(&tzOp, &measLen);
  if(meas == NULL || measLen != TPM_HASH_SIZE) {
    rv = 1;
    printf("Failure at %s:%d\n", __FILE__, __LINE__); 
    printf("tzRet 0x%08x\n", tzRet);
    goto out;

  }

  printf("PCR %d: %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x "
         "%02x %02x %02x %02x %02x %02x %02x %02x %02x %02x\n",
         pcr_idx,
         meas[0], meas[1], meas[2], meas[3], meas[4],
         meas[5], meas[6], meas[7], meas[8], meas[9],
         meas[10], meas[11], meas[12], meas[13], meas[14],
         meas[15], meas[16], meas[17], meas[18], meas[19]);         
  
  if (TZDecodeGetError(&tzOp) != TZ_SUCCESS) {
    rv = 1;
    printf("Failure at %s:%d\n", __FILE__, __LINE__); 
    printf("tzRet 0x%08x\n", tzRet);
    goto out;
  }

 out:
  TZOperationRelease(&tzOp);

  if(0 != rv) { printf("...FAILED rv %d\n", rv); }
  return rv;  
}

int test_pcr_read(tz_session_t *tzPalSession)
{
  int i=0;
  int rv;
  
  printf("\nPCR_READ\n");

  for(i=0; i<TPM_PCR_NUM; i++) {
    rv = test_pcr_read_i(tzPalSession, i);
    if(0 != rv) return rv;
  }
  return rv;
}

int test_rand(tz_session_t *tzPalSession)
{
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tzOp;
  int rv = 0;
  const size_t req_bytes=4;
  size_t got_bytes;
  uint8_t *bytes;
  int i;

  printf("\nRAND\n");

  /* prep operation */
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_RAND,
                                   NULL,
                                   &tzOp);
  assert(tzRet == TZ_SUCCESS);

  TZEncodeUint32(&tzOp, req_bytes);

  /* Call PAL */
  tzRet = TZOperationPerform(&tzOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
    rv = 1;
    printf("Failure at %s:%d\n", __FILE__, __LINE__);
    printf("tzRet 0x%08x\n", tzRet);
    goto out;
  }
  /* fetch result */
  bytes = TZDecodeArraySpace(&tzOp, &got_bytes);
  if (TZDecodeGetError(&tzOp) != TZ_SUCCESS
      || bytes == NULL
      || got_bytes != req_bytes) {
    rv = 1;
    printf("Failure at %s:%d\n", __FILE__, __LINE__);
    printf("tzRet 0x%08x\n", tzRet);
    goto out;
  }

  /* show result */
  printf("Got random bytes: ");
  for(i=0; i<got_bytes; i++) {
    printf(" %02x", bytes[i]);
  }
  printf("\n");

 out:
  TZOperationRelease(&tzOp);

  if(0 != rv) { printf("...FAILED rv %d\n", rv); }
  return rv;
}

static tz_return_t time_init(tz_session_t *tzPalSession)
{
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tzOp;

  /* prep operation */
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_TIME_INIT,
                                   NULL,
                                   &tzOp);
  if (tzRet != TZ_SUCCESS) {
    goto out;
  }

  /* Call PAL */
  tzRet = TZOperationPerform(&tzOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
    printf("Failure at %s:%d\n", __FILE__, __LINE__);
    printf("tzRet 0x%08x\n", tzRet);
    goto out;
  }

 out:
  TZOperationRelease(&tzOp);
  return tzRet;
}

static tz_return_t time_elapsed(tz_session_t *tzPalSession, uint64_t *t)
{
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tzOp;

  /* prep operation */
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_TIME_ELAPSED,
                                   NULL,
                                   &tzOp);
  if(tzRet != TZ_SUCCESS) {
    goto out;
  }

  /* Call PAL */
  tzRet = TZOperationPerform(&tzOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
    printf("Failure at %s:%d\n", __FILE__, __LINE__);
    printf("tzRet 0x%08x\n", tzRet);
    goto out;
  }

  *t = ((uint64_t)TZDecodeUint32(&tzOp)) << 32;
  *t = *t | TZDecodeUint32(&tzOp);
  tzRet = TZDecodeGetError(&tzOp);
  if (tzRet != TZ_SUCCESS) {
    printf("Failure at %s:%d\n", __FILE__, __LINE__);
    printf("tzRet 0x%08x\n", tzRet);
    goto out;
  }

 out:
  TZOperationRelease(&tzOp);
  return tzRet;
}

tz_return_t test_time(tz_session_t *tzPalSession)
{
  tz_return_t rv = TZ_SUCCESS;
  uint64_t t0, t1;

  printf("\nTIME\n");

  printf("initializing time\n");
  rv = time_init(tzPalSession);
  if (rv != TZ_SUCCESS) {
    return rv;
  }

  printf("fetching t0\n");
  rv = time_elapsed(tzPalSession, &t0);
  if (rv != TZ_SUCCESS) {
    return rv;
  }
  printf("got t0=%llu\n", t0);

  printf("fetching t1\n");
  rv = time_elapsed(tzPalSession, &t1);
  if (rv != TZ_SUCCESS) {
    return rv;
  }
  printf("got t1=%llu\n", t1);
  printf("dt=%llu\n", t1 - t0);

  return TZ_SUCCESS;
}

// function main
// register some sensitive code and data in libfoo.so and call bar()
int main(void)
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

#ifdef TEST_VMMCALL
  rv = test_vmcall() || rv;
#endif

#ifdef TEST_WITHOUTPARAM
  rv = test_withoutparam(&tzPalSession) || rv;
#endif

#ifdef TEST_PARAM
  rv = test_param(&tzPalSession) || rv;
#endif

#ifdef TEST_SEAL
  rv = test_seal(&tzPalSession) || rv;
#endif

#ifdef TEST_QUOTE
  rv = test_quote(&tzPalSession) || rv;
#endif

#ifdef TEST_PCR_EXTEND
  rv = test_pcr_extend(&tzPalSession) || rv;
#endif

#ifdef TEST_PCR_READ
  rv = test_pcr_read(&tzPalSession) || rv;
#endif

#ifdef TEST_RAND
  rv = test_rand(&tzPalSession) || rv;
#endif

#ifdef TEST_TIME
  rv = test_time(&tzPalSession) || rv;
#endif

  
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
