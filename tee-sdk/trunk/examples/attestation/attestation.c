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
#include <inttypes.h>

#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/bio.h>
#include <openssl/buffer.h>
#include <openssl/rsa.h>
#include <openssl/sha.h>
#include <openssl/engine.h>

#include <json/json.h>

#include <tee-sdk/tv.h>
#include <tee-sdk/tz.h>
#include <tee-sdk/tzmarshal.h>

#include <trustvisor/tv_utpm.h>

#include "common.h"



/**
 * Invoke the PAL.
 *
 * The PAL expects as input:
 * 1. uTpmQuoteNonce - a 20-byte nonce for use in generating the uTPM quote
 * 2. tpmsel - data structure that selects which uPCRs to include in the quote
 * 3. palInpData - an ASCII string that is its "input data"
 *
 * The PAL produces an output containing:
 * 1. uTpmPubKeyN
 * 2. pcrComp - PCR composite (tpmsel + length + actual PCR values)
 * 3. uTpmValDataSig
 */
#define PALINPDATA "The quick brown fox jumped over the lazy dog!"
int invoke_pal(tz_session_t *tzPalSession) {
  /* PAL inputs; fixed to simplify testing. */
  char *palInpData;
  const char *uTpmQuoteNonce = "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13";
  TPM_NONCE *nonce;
  TPM_PCR_SELECTION *tpmsel;

  /* PAL outputs */
  uint8_t *quote = NULL;
  uint32_t quoteLen = TPM_MAX_QUOTE_LEN;
  uint32_t maxQuoteLen = TPM_MAX_QUOTE_LEN;
  uint8_t *rsaMod = NULL;
  uint32_t rsaModLen = 0;
  uint8_t *pcrComp = NULL;
  uint32_t pcrCompLen = 0;

  /* massaged / computed */
  //TPM_DIGEST uPcr0;
  //TPM_DIGEST uPcr1;

  /* support */
  tz_return_t tzRet, serviceReturn;
  tz_operation_t tz_quoteOp;  
  int rv = 0;
  

  /**
   * Prepare operation
   */
  tzRet = TZOperationPrepareInvoke(tzPalSession,
                                   PAL_QUOTE,
                                   NULL,
                                   &tz_quoteOp);
  assert(tzRet == TZ_SUCCESS);

  /**
   * Setup encoded input space
   */
  assert(!(TZIEncodeF(&tz_quoteOp,
                      "%"TZI_EARRSPC "%"TZI_EARRSPC "%"TZI_EARRSPC,
                      &nonce, sizeof(TPM_NONCE),
                      &tpmsel, sizeof(TPM_PCR_SELECTION),
                      &palInpData, strlen(PALINPDATA)+1)));
  
  /* copy nonce to input space */
  memcpy(nonce->nonce, uTpmQuoteNonce, sizeof(TPM_NONCE));

  /* copy tpmsel (setup to include uPCRs 0, 1) to input space */
  assert(8 == TPM_PCR_NUM); /* want this test to fail if uTPM's grow more uPCRs */
  tpmsel->sizeOfSelect = 1; /* 1 byte to select up to 8 PCRs */
  utpm_pcr_select_i(tpmsel, 0); /* select uPCR 0 */
  utpm_pcr_select_i(tpmsel, 1); /* select uPCR 1 */

  /* copy generic input data to input space */
  memcpy(palInpData, PALINPDATA, strlen(PALINPDATA)+1);
  
  /**
   * Call pal
   */
  tzRet = TZOperationPerform(&tz_quoteOp, &serviceReturn);
  if (tzRet != TZ_SUCCESS) {
    rv = 1;
    goto out;
  }

  /**
   * Parse outputs
   */

  /* get quote */
  if((tzRet = TZIDecodeF(&tz_quoteOp,
                         "%"TZI_DARRSPC "%"TZI_DARRSPC "%"TZI_DARRSPC "%"TZI_DU32,
                         &rsaMod, &rsaModLen,
                         &pcrComp, &pcrCompLen,
                         &quote, &maxQuoteLen,
                         &quoteLen))) {
      rv = 1;
      goto out;
  }

  fprintf(stderr, "  actual quoteLen = %d\n", quoteLen);
  assert(rsaModLen == TPM_RSA_KEY_LEN);
  assert(quoteLen == TPM_RSA_KEY_LEN);

  fprintf(stderr, "  pcrCompLen = %d\n", pcrCompLen);
  //print_hex("  pcrComp: ", pcrComp, pcrCompLen);
  
  /* Verify the signature in the Quote */
  //print_hex("  sig: ", quote, quoteLen);

  print_hex("  rsaMod: ", rsaMod, TPM_RSA_KEY_LEN);

  /* Format attestation results for external verifier */
  output_as_json(pcrComp, pcrCompLen, quote, quoteLen, nonce, rsaMod);

  /* For now, also check the signature locally (sanity check) */
  if((rv = verify_quote(pcrComp, pcrCompLen, quote, quoteLen, nonce, rsaMod)) != 0) {
      fprintf(stderr, "verify_quote FAILED\n");
  }

  out:
  TZOperationRelease(&tz_quoteOp);
  
  return rv;
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
    //printf("scode sections:\n");
    //tv_pal_sections_print(&scode_info);

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

  rv = invoke_pal(&tzPalSession) || rv;
  
  if (rv) {
    fprintf(stderr, "FAIL with rv = %d\n", rv);
  } else {
    fprintf(stderr, "SUCCESS with rv = %d\n", rv);
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
