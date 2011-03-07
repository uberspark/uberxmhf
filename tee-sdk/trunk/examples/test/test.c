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

#include <tz.h>
#include <marshal.h>

#include <tv.h>
#include <scode.h>

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
  scode_test();
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

int test_quote(tz_session_t *tzPalSession)
{
  uint8_t *nonce;
  uint32_t nonceLen=20; /* from constant? */
  uint32_t tpmsel[] = {1, 0}; /* 1 PCR, value 0 */
  uint32_t tpmselLen=2;
  uint32_t *quote;
  uint32_t quoteLen;

  tz_return_t tzRet, serviceReturn;
  tz_operation_t tz_quoteOp;
  
  unsigned char *pdata;
  int num, i,j;
  int rv = 0;

  printf("\nQUOTE\n");

  /* prep operation */
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_QUOTE,
                                   NULL,
                                   &tz_quoteOp);
  assert(tzRet == TZ_SUCCESS);

  /* setup nonce */
  nonce = TZEncodeArraySpace(&tz_quoteOp, nonceLen);
  if (nonce == NULL) {
    rv = 1;
    goto out;
  }
  for(i=0; i<nonceLen; i++) {
    nonce[i] = (uint8_t)i;
  }

  /* setup tpmsel */
  TZEncodeArray(&tz_quoteOp, tpmsel, tpmselLen*sizeof(uint32_t));

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

  /* get actual quote len */
  quoteLen = TZDecodeUint32(&tz_quoteOp);

  if (TZDecodeGetError(&tz_quoteOp) != TZ_SUCCESS) {
    rv = 1;
    goto out;
  }

  printf("quote[0] after PAL is %d!\n", quote[0]);
  printf("output len = %d!\n", quoteLen);

  if (quote[0] != 0x00000101
      || quote[1] != 0x544f5551) {
    printf("quote header error!\n");
    return 1;
  }
  num = quote[2];
  if (num > 4) {
    printf("quote pcr sel error!\n");
    return 1;
  }
  pdata = ((uint8_t*)quote)+8+4+4*num;
  for( i=0 ; i<num ; i++ )  {
    printf("PCR[%d] = ", quote[3+i]);
    for (j=0; j<20; j++) 
      printf("%#x ", *(pdata+i*20+j));
    printf("\n");
  }
  pdata = ((uint8_t*)quote)+8+4+24*num;
  printf("nonce = ");
  for( i=0 ; i<20 ; i++ )  
    printf("%x ", *(pdata+i));
  printf("\n");


 out:
  TZOperationRelease(&tz_quoteOp);

  return rv;
}

// function main
// register some sensitive code and data in libfoo.so and call bar()
int main(void)
{
  struct scode_sections_info scode_info;
  int rv = 0;
  tz_return_t tzRet;
  tz_device_t tzDevice;
  tz_session_t tzPalSession;
  tv_service_t pal = 
    {
      .sPageInfo = &scode_info,
      .sParams = NULL, /* soon to be deprecated? */
      .pEntry = pal_entry,
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
    scode_sections_info_init(&scode_info,
                             PAGE_SIZE, PAGE_SIZE);
    printf("scode sections:\n");
    scode_sections_info_print(&scode_info);

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
