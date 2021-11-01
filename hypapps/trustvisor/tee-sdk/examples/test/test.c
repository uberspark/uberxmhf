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
#include "pals.h"
//#include  "config.h"
#include  <errno.h>
#include  <string.h>
#include <inttypes.h>

#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/rsa.h>
#include <openssl/sha.h>
#include <openssl/engine.h>

#include <tee-sdk/tv.h>
#include <tee-sdk/tz.h>
#include <tee-sdk/tze.h>
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
  unsigned int i;
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


int test_id_getpub(tz_session_t *tzPalSession, uint8_t *rsaPubDER, uint32_t *rsaPubDER_sz)
{
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tzOp;
  uint8_t *buf;
  uint32_t rv = 0;
  
  printf("ID_GETPUB\n");

  assert(NULL != rsaPubDER);
  
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
  tzRet = TZIDecodeF(&tzOp, "%"TZI_DARRSPC_NOLEN "%"TZI_DU32,
                     &buf,
                     rsaPubDER_sz);
  if (tzRet) {
    rv = 1;
    goto out;
  }
  memcpy( rsaPubDER, buf, *rsaPubDER_sz);

  print_hex("  rsaMod: ", rsaPubDER, *rsaPubDER_sz);
  
 out:
  TZOperationRelease(&tzOp);

  if(0 != rv) { printf("...FAILED rv %d\n", rv); }
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

int verify_quote(uint8_t *tpm_pcr_composite, uint32_t tpc_len, uint8_t *sig, uint32_t sig_len,
                 TPM_NONCE *externalnonce, uint8_t* rsaPubDER, long rsaPubDER_sz) {
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
     * Import the public key used to check the quote.
     */    
    if (NULL == d2i_RSAPublicKey( &rsa, (const unsigned char**)&rsaPubDER, rsaPubDER_sz)) {
      printf("ERROR: d2i_RSAPublicKey failed\n");
      rv = 1;
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
    
    return rv;
}

int test_quote(tz_session_t *tzPalSession)
{
  TPM_NONCE *nonce;
  TPM_PCR_SELECTION *tpmsel;
  uint8_t *quote;
  uint32_t quoteLen = TPM_MAX_QUOTE_LEN;
  uint32_t maxQuoteLen;
  uint8_t *pcrComp = NULL;
  uint32_t pcrCompLen = 0;

  tz_return_t tzRet, serviceReturn;
  tz_operation_t tz_quoteOp;
  
  unsigned int i;
  int rv = 0;
  
  uint32_t rsaPubDER_sz = TPM_RSA_KEY_LEN + 100;
  uint8_t *rsaPubDER = NULL;

  /**
   * First get the public key that will eventually be used to verify the quote.
   */
  
  rsaPubDER = malloc(rsaPubDER_sz);
  assert(rsaPubDER);
  if(0 != test_id_getpub(tzPalSession, rsaPubDER, &rsaPubDER_sz)) {
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

  /* setup encoded space */
  assert(!(TZIEncodeF(&tz_quoteOp,
                      "%"TZI_EARRSPC "%"TZI_EARRSPC,
                      &nonce, sizeof(TPM_NONCE),
                      &tpmsel, sizeof(TPM_PCR_SELECTION))));
  
  /* setup nonce */
  for(i=0; i<sizeof(TPM_NONCE); i++) {
    nonce->nonce[i] = (uint8_t)i;
  }

  /* setup tpmsel */
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
  if((tzRet = TZIDecodeF(&tz_quoteOp,
                         "%"TZI_DARRSPC "%"TZI_DARRSPC "%"TZI_DU32,
                         &quote, &maxQuoteLen,
                         &pcrComp, &pcrCompLen,
                         &quoteLen))) {
      rv = 1;
      goto out;
  }
  printf("  max quoteLen = %d\n", quoteLen);
  printf("  actual quoteLen = %d\n", quoteLen);

  printf("  pcrCompLen = %d\n", pcrCompLen);
  print_hex("  pcrComp: ", pcrComp, pcrCompLen);  

  /* Verify the signature in the Quote */
  print_hex("  sig: ", quote, quoteLen);
  
  if((rv = verify_quote(pcrComp, pcrCompLen, quote, quoteLen, nonce, rsaPubDER, rsaPubDER_sz)) != 0) {
      printf("verify_quote FAILED\n");
  }

  out:
  free(rsaPubDER);
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
  assert(!(TZIEncodeF(&tzOp,
                      "%"TZI_EU32 "%"TZI_EARRSPC,
                      pcr_idx,
                      &meas_ptr, TPM_HASH_SIZE)));

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
  assert(!(TZIEncodeF(&tzOp, "%"TZI_EU32, pcr_idx)));
  
  /* Call PAL */
  tzRet = TZOperationPerform(&tzOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
    rv = 1;
    printf("Failure at %s:%d\n", __FILE__, __LINE__); 
    printf("tzRet 0x%08x\n", tzRet);
    goto out;

  }

  if ((tzRet = TZIDecodeF(&tzOp, "%"TZI_DARRSPC,
                          &meas, &measLen))
      || measLen != TPM_HASH_SIZE) {
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
  const size_t req_bytes=40;
  size_t got_bytes;
  uint8_t *bytes;
  unsigned int i;

  printf("\nRAND\n");

  /* prep operation */
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_RAND,
                                   NULL,
                                   &tzOp);
  assert(tzRet == TZ_SUCCESS);

  assert(!(TZIEncodeF(&tzOp, "%"TZI_EU32, req_bytes)));

  /* Call PAL */
  tzRet = TZOperationPerform(&tzOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
    rv = 1;
    printf("Failure at %s:%d\n", __FILE__, __LINE__);
    printf("tzRet 0x%08x\n", tzRet);
    goto out;
  }
  /* fetch result */
  
  if ((tzRet = TZIDecodeF(&tzOp, "%"TZI_DARRSPC, &bytes, &got_bytes))
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
  uint32_t t_hi, t_lo;

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

  tzRet = TZIDecodeF(&tzOp, "%"TZI_DU32 "%"TZI_DU32, &t_hi, &t_lo);
  *t = ((uint64_t)t_hi) << 32;
  *t = *t | t_lo;

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

tz_return_t test_nv_rollback(tz_session_t *tzPalSession) {
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tzOp;
  uint8_t *new;
  uint8_t *old;
  int rv = 0;
  uint32_t i, len = 32; /* XXX get this from somewhere (sizeof sha-256) */

  printf("\nNV_ROLLBACK\n");

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

tz_return_t init_tz_sess(tze_dev_svc_sess_t* tz_sess)
{
  tz_return_t rv;
  bool registered_pal=false;

  /* register pal */
  {
    tv_device_open_options_t tv_dev_options = {
      .userspace_only = USERSPACE_ONLY,
    };
    tze_svc_load_and_open_options_t load_options = {
      .pkDeviceInit = &tv_dev_options,
    };
    struct tv_pal_sections scode_info;
    tv_service_t pal = {
      .sPageInfo = &scode_info,
      .pEntry = pals,
    };
    tv_pal_sections_init(&scode_info,
                         3*PAGE_SIZE, 10*PAGE_SIZE);
    rv = TZESvcLoadAndOpen(tz_sess,
                           &pal,
                           sizeof(pal),
                           &load_options);
    if(TZ_SUCCESS != rv) {
        printf("Failure in TZESvcLoadAndOpen: %d\n", rv);
        goto out;
    }
    registered_pal=true;
  }

 out:
  if (rv && registered_pal) {
    TZEClose(tz_sess);
  }

  return rv;
}

// function main
// register some sensitive code and data in libfoo.so and call bar()
int main(void)
{
  int rv = 0;
  tze_dev_svc_sess_t tz_sess;

  assert(TZ_SUCCESS == init_tz_sess(&tz_sess));
  
#ifdef TEST_VMMCALL
  rv = test_vmcall() || rv;
#endif

#ifdef TEST_WITHOUTPARAM
  rv = test_withoutparam(&tz_sess.tzSession) || rv;
#endif

#ifdef TEST_PARAM
  rv = test_param(&tz_sess.tzSession) || rv;
#endif

#ifdef TEST_SEAL
  rv = test_seal2(&tz_sess.tzSession) || rv;
  rv = test_seal(&tz_sess.tzSession) || rv;
#endif

#ifdef TEST_LTSEAL
  rv = test_longterm_seal(&tz_sess.tzSession) || rv;
#endif

  
#ifdef TEST_QUOTE
  rv = test_quote(&tz_sess.tzSession) || rv;
#endif

#ifdef TEST_PCR_EXTEND
  rv = test_pcr_extend(&tz_sess.tzSession) || rv;
#endif

#ifdef TEST_PCR_READ
  rv = test_pcr_read(&tz_sess.tzSession) || rv;
#endif

#ifdef TEST_RAND
  rv = test_rand(&tz_sess.tzSession) || rv;
#endif

#ifdef TEST_TIME
  rv = test_time(&tz_sess.tzSession) || rv;
#endif

#ifdef TEST_NV_ROLLBACK
  rv = test_nv_rollback(&tz_sess.tzSession) || rv;
#endif
  
  if (rv) {
    printf("FAIL with rv=%d\n", rv);
  } else {
    printf("SUCCESS with rv=%d\n", rv);
  }

  rv = TZEClose(&tz_sess) || rv;  

  return rv;
} 
