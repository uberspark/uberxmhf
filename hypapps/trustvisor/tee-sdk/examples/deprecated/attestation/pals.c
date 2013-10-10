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

#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#include <tee-sdk/tzmarshal.h>
#include <tee-sdk/svcapi.h>

#include <trustvisor/tv_utpm.h>

#include "pals.h"
#include "sha1.h"

__attribute__ ((section (".scode")))
tz_return_t pal_quote(IN TPM_NONCE *nonce,
                      IN TPM_PCR_SELECTION *tpmsel,
                      OUT uint8_t *quote, INOUT size_t *quote_len,
                      OUT uint8_t *pcrComp, INOUT size_t *pcrCompLen) 
{
  if (!svc_utpm_quote(nonce, tpmsel, quote, quote_len, pcrComp, pcrCompLen)) {
    return TZ_SUCCESS;
  } else {
    return TZ_ERROR_GENERIC;
  }
}

__attribute__ ((section (".scode")))
tz_return_t pal_id_getpub(OUT uint8_t* rsaModulus, INOUT size_t *sz)
{
    if(!svc_utpm_id_getpub(rsaModulus, sz)) {
        return TZ_SUCCESS;
    } else {
        return TZ_ERROR_GENERIC;
    }
}

__attribute__ ((section (".scode")))
tz_return_t pal_pcr_extend(IN uint32_t idx,
                           IN uint8_t *meas)
{
  if((idx >= TPM_PCR_NUM) || (NULL == meas)) {
    return TZ_ERROR_GENERIC;
  }
  
  if(svc_utpm_pcr_extend(idx, meas) == 0) {
    return TZ_SUCCESS;
  } else {
    return TZ_ERROR_GENERIC;
  }
}

__attribute__ ((section (".scode")))
tz_return_t pal_pcr_read(IN uint32_t idx,
                        OUT uint8_t *val)
{
  if((idx >= TPM_PCR_NUM) || (NULL == val)) {
    return TZ_ERROR_GENERIC;
  }

  if(svc_utpm_pcr_read(idx, val) == 0) {
    return TZ_SUCCESS;
  } else {
    return TZ_ERROR_GENERIC;
  }
}

__attribute__ ((section (".scode")))
void pals(uint32_t uiCommand, tzi_encode_buffer_t *psInBuf, tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv)
{
    /* We only know one command. */
    if(PAL_QUOTE != uiCommand) {
        return;
    }

    /* input parameters */
    TPM_NONCE *nonce = NULL;
    uint32_t nonceLen = 0;
    TPM_PCR_SELECTION *tpmsel = NULL;
    uint32_t tpmselLen = 0;
    uint8_t *inpAscii = NULL;
    uint32_t inpAsciiLen = 0;

    /* output parameters */
    uint8_t *quote = NULL;      
    uint32_t maxQuoteLen = TPM_MAX_QUOTE_LEN;
    uint32_t actualQuoteLen = 0;
    uint8_t *pcrComp = NULL;
    uint32_t pcrCompLen = 47; /* 3+4+20+20 XXX */
    uint8_t *rsaModulus = NULL;
    size_t rsaModulusLen = TPM_RSA_KEY_LEN + 100;

    /* massaged / computed */
    TPM_DIGEST inpAsciiDigest;
    
    *puiRv = TZ_SUCCESS;

    /* Decode input parameters from legacy userspace's test.c */
    nonce = TZIDecodeArraySpace(psInBuf, &nonceLen);
    tpmsel = TZIDecodeArraySpace(psInBuf, &tpmselLen);
    inpAscii = TZIDecodeArraySpace(psInBuf, &inpAsciiLen);

    /* Sanity-check input parameters */
    if(!nonce || !tpmsel || !inpAscii
       || tpmselLen != sizeof(TPM_PCR_SELECTION)
       || nonceLen != sizeof(TPM_NONCE)
       || inpAsciiLen < 1) {
        *puiRv = TZ_ERROR_ENCODE_FORMAT;
        return;
    }

    /* Prepare the output buffer to hold the response back to userspace. */
    rsaModulus = TZIEncodeArraySpace(psOutBuf, rsaModulusLen);
    pcrComp = TZIEncodeArraySpace(psOutBuf, pcrCompLen);
    quote = TZIEncodeArraySpace(psOutBuf, TPM_RSA_KEY_LEN);

    if(!rsaModulus || !pcrComp || !quote) {
        *puiRv = TZ_ERROR_ENCODE_FORMAT;
        return;
    }
    
    
    /**
     * Make the hypercalls to invoke the uTPM operations
     */

    /* Extend uPCR 1 with hash of input data */
    sha1_buffer(inpAscii, inpAsciiLen, inpAsciiDigest.value);
    if((*puiRv = pal_pcr_extend(1, inpAsciiDigest.value))) return;

    /* Read the public key modulus for the keypair that signs the quote */
    if((*puiRv = pal_id_getpub(rsaModulus, &rsaModulusLen))) return;

    /* Request the actual uPCR quote from the uTPM */
    actualQuoteLen = maxQuoteLen;
    if((*puiRv = pal_quote(nonce, tpmsel, quote, (size_t*)&actualQuoteLen, pcrComp, (size_t*)&pcrCompLen))) return;
    
    /* Also encode the _actual_ length of the quote */
    TZIEncodeUint32(psOutBuf, actualQuoteLen);

    /* Encode _actual_ length of pub key */
    TZIEncodeUint32(psOutBuf, rsaModulusLen);
}
