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
#include  "pals.h"

#include <tee-sdk/tzmarshal.h>
#include <tee-sdk/svcapi.h>

#include <trustvisor/tv_utpm.h>

__attribute__ ((section (".scode")))
void pals(uint32_t uiCommand, tzi_encode_buffer_t *psInBuf, tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv)
{
  switch(uiCommand) {
  case PAL_WITHOUTPARAM:
    *puiRv = TZ_SUCCESS;
    pal_withoutparam();
    break;

  case PAL_PARAM:
    {
      uint32_t input;
      uint32_t out;
      *puiRv = TZ_SUCCESS;

      if((*puiRv = TZIDecodeBufF(psInBuf, "%"TZI_DU32, &input)))
        break;

      out = pal_param(input);

      if((*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EU32, out)))
        break;
    }
    break;

  case PAL_SEAL:
    {
      uint8_t *in, *out;
      size_t inLen, outLen;
      TPM_PCR_INFO *tpmPcrInfo;
      size_t tpmPcrInfoLen;
      *puiRv = TZ_SUCCESS;

      {
        uint32_t inLen32, tpmPcrInfoLen32;
        if((*puiRv = TZIDecodeBufF(psInBuf,
                                   "%"TZI_DARRSPC "%"TZI_DARRSPC,
                                   &tpmPcrInfo, &tpmPcrInfoLen32,
                                   &in, &inLen32)))
          break;
        tpmPcrInfoLen = tpmPcrInfoLen32;
        (void)tpmPcrInfoLen; /* pacify compiler that this is unused */
        inLen = inLen32;
      }
        
      outLen = inLen + 100; /* XXX guessing at seal overhead (real overhead is sizeof(IV + HMAC)) */

      if((*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EARRSPC,
                                 &out, (uint32_t)outLen)))
        break;

      if((*puiRv = pal_seal(tpmPcrInfo, in, inLen, out, &outLen)))
        break;

      /* actual size of previous array */
      if((*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EU32, (uint32_t)outLen)))
        break;
    }
    break;

  case PAL_UNSEAL:
    {
      uint8_t *in, *out, *digestAtCreation;
      size_t inLen, outLen;
      *puiRv = TZ_SUCCESS;

      {
        uint32_t inLen32;
        if((*puiRv = TZIDecodeBufF(psInBuf,
                                   "%"TZI_DARRSPC,
                                   &in, &inLen32)))
          break;
        inLen = inLen32;
      }

      outLen = inLen + 100; /* XXX guessing at unseal overhead, though should actually be negative */

      if((*puiRv = TZIEncodeBufF(psOutBuf,
                                "%"TZI_EARRSPC "%"TZI_EARRSPC,
                                 &out, (uint32_t)outLen,
                                 &digestAtCreation, (uint32_t)TPM_HASH_SIZE)))
        break;
      
      if((*puiRv = pal_unseal(in, inLen, out, &outLen, digestAtCreation)))
        break;

      /* actual size of previous array */
      if((*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EU32, (uint32_t)outLen)))
        break;
    }
    break;

  case PAL_QUOTE:
    {
      TPM_NONCE *nonce = NULL;
      size_t nonceLen = 0;
      TPM_PCR_SELECTION *tpmsel = NULL;
      size_t tpmselLen = 0;
      uint8_t *quote = NULL;      
      size_t maxQuoteLen = TPM_MAX_QUOTE_LEN;
      size_t actualQuoteLen = 0;
      uint8_t *pcrComp = NULL;
      size_t pcrCompLen = 3+4+8*20; /* XXX */
      
      *puiRv = TZ_SUCCESS;

      /* Decode input parameters from legacy userspace's test.c */
      {
        uint32_t nonceLen32, tpmselLen32;
        if((*puiRv = TZIDecodeBufF(psInBuf,
                                   "%"TZI_DARRSPC "%"TZI_DARRSPC,
                                   &nonce, &nonceLen32,
                                   &tpmsel, &tpmselLen32)))
          break;
        nonceLen = nonceLen32;
        tpmselLen = tpmselLen32;
      }

      /* Sanity-check input parameters */
      if (tpmselLen != sizeof(TPM_PCR_SELECTION)
          || nonceLen != sizeof(TPM_NONCE)) {
        *puiRv = TZ_ERROR_ENCODE_FORMAT;
        break;
      }

      /* Prepare the output buffer to hold the response back to userspace. */
      if((*puiRv = TZIEncodeBufF(psOutBuf,
                                "%"TZI_EARRSPC "%"TZI_EARRSPC,
                                 &quote, (uint32_t)maxQuoteLen,
                                 &pcrComp, (uint32_t)pcrCompLen)))
        break;
                                     
      /* Make the hypercall to invoke the uTPM operation */
      actualQuoteLen = maxQuoteLen;
      if((*puiRv = pal_quote(nonce, tpmsel, quote, &actualQuoteLen, pcrComp, &pcrCompLen)))
        break;

      /* Also encode the actual length of the result */
      if((*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EU32, (uint32_t)actualQuoteLen)))
        break;
    }
    break;

    case PAL_ID_GETPUB:
    {
      uint8_t *rsaModulus;
      size_t sz = TPM_RSA_KEY_LEN + 100;
      
      /* Prepare the output buffer to hold the response back to userspace. */
      if((*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EARRSPC,
                                 &rsaModulus, (uint32_t)sz)))
        break;

      if((*puiRv = pal_id_getpub(rsaModulus, &sz)))
        break;

      /* actual size of previous array */
      if((*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EU32, (uint32_t)sz)))
        break;
    }
    break;
    
    case PAL_PCR_EXTEND:
    {
      uint8_t *measIn;
      size_t measLen;
      uint32_t idx;
      *puiRv = TZ_SUCCESS;

      {
        uint32_t measLen32;
        if((*puiRv = TZIDecodeBufF(psInBuf,
                                   "%"TZI_DU32 "%"TZI_DARRSPC,
                                   &idx,
                                   &measIn, &measLen32)))
          break;
        measLen = measLen32;
      }

      if(measLen != TPM_HASH_SIZE) {
        *puiRv = TZ_ERROR_GENERIC;
        break;
      }

      if((*puiRv = pal_pcr_extend(idx, measIn)))
        break;
    }
    break;
    
    case PAL_PCR_READ:
    {
      uint8_t *valOut;
      uint32_t idx;
      *puiRv = TZ_SUCCESS;

      if((*puiRv = TZIDecodeBufF(psInBuf, "%"TZI_DU32, &idx)))
        break;

      if((*puiRv = TZIEncodeBufF(psOutBuf,
                                "%"TZI_EARRSPC,
                                 &valOut, (uint32_t)TPM_HASH_SIZE)))
        break;

      if((*puiRv = pal_pcr_read(idx, valOut)))
        break;
    }
    break;

  case PAL_RAND:
    {
      uint32_t len;
      uint8_t *bytes;

      if((*puiRv = TZIDecodeBufF(psInBuf, "%"TZI_DU32, &len)))
        break;

      if((*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EARRSPC,
                                 &bytes, len)))
        break;
      
      if((*puiRv = pal_rand(len, bytes)))
        break;
    }
    break;

  case PAL_TIME_INIT:
    *puiRv = pal_time_init();
    break;

  case PAL_TIME_ELAPSED:
    {
      uint64_t dt;
      uint32_t dt_hi, dt_lo;

      if((*puiRv = pal_time_elapsed(&dt)))
        break;

      dt_hi = (uint32_t)(dt>>32);
      dt_lo = (uint32_t)dt;
      if((*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EU32 "%"TZI_EU32,
                                 dt_hi, dt_lo)))
        break;
    }
    break;
  case PAL_NV_ROLLBACK:
    {
      uint8_t *old;
      uint8_t *new;        
      uint32_t len = 32; /* XXX bad magic XXX */
      
      if((*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EARRSPC,
                                 &old, len)))
          break;

      if((*puiRv = TZIDecodeBufF(psInBuf,
                                 "%"TZI_DARRSPC,
                                 &new, &len)))
          break;      

      if((*puiRv = pal_nv_rollback(new, &len, old)))
          break;
    }
    break;
  }
  return;
}

/* sensitive code  */
__attribute__ ((section (".scode")))
void pal_withoutparam(void) 
{
  asm("nop"::);
  asm("nop"::);
  asm("nop"::);
  asm("nop"::);
}

__attribute__ ((section (".scode")))
uint32_t pal_param(uint32_t input) 
{
  return input + 1;
}

__attribute__ ((section (".scode")))
tz_return_t pal_seal(TPM_PCR_INFO *pcrInfo, uint8_t *input, uint32_t inputLen, uint8_t *output, size_t *outputLen)
{
  if (svc_utpm_seal(pcrInfo, input, inputLen, output, outputLen) == 0) {
    return TZ_SUCCESS;
  } else {
    return TZ_ERROR_GENERIC;
  }
}

__attribute__ ((section (".scode")))
tz_return_t pal_unseal(uint8_t *input, uint8_t inputLen, uint8_t *output, size_t *outputLen, uint8_t *digestAtCreation)
{
    if (svc_utpm_unseal(input, inputLen, output, outputLen, digestAtCreation) == 0) {
    return TZ_SUCCESS;
  } else {
    return TZ_ERROR_GENERIC;
  }
}

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
tz_return_t pal_rand(IN size_t len,
                     OUT uint8_t *bytes)
{
  if (svc_utpm_rand_block(bytes, len) == 0) {
    return TZ_SUCCESS;
  } else {
    return TZ_ERROR_GENERIC;
  }
}

static uint64_t t0;
static uint64_t t0_nonce;
static bool t0_initd=false;
tz_return_t pal_time_init()
{
  if (svc_time_elapsed_us(&t0_nonce, &t0)) {
    return TZ_ERROR_GENERIC;
  }
  t0_initd=true;
  return TZ_SUCCESS;
}

__attribute__ ((section (".scode")))
tz_return_t pal_time_elapsed(OUT uint64_t *us)
{
  uint64_t t;
  uint64_t t_nonce;

  if (!t0_initd)
    return TZ_ERROR_GENERIC;

  if (svc_time_elapsed_us(&t_nonce, &t)) {
    return TZ_ERROR_GENERIC;
  }

  if (t_nonce != t0_nonce) {
    return TZ_ERROR_GENERIC;
  }

  *us = t - t0;

  return TZ_SUCCESS;
}

__attribute__ ((section (".scode")))
tz_return_t pal_nv_rollback(IN uint8_t *newval,
                            OUT uint32_t *nv_size,
                            OUT uint8_t *oldval)
{
    size_t size;

    if(svc_tpmnvram_getsize(&size)) {
        return TZ_ERROR_GENERIC;
    }

    *nv_size = (uint32_t)size;
    
    if(svc_tpmnvram_readall(oldval)) {
        return TZ_ERROR_GENERIC;
    }

    if(svc_tpmnvram_writeall(newval)) {
        return TZ_ERROR_GENERIC;
    }
    
    return TZ_SUCCESS;
}
