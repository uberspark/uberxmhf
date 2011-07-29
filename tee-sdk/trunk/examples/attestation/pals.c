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

  case PAL_QUOTE:
    {
      TPM_NONCE *nonce = NULL;
      uint32_t nonceLen = 0;
      TPM_PCR_SELECTION *tpmsel = NULL;
      uint32_t tpmselLen = 0;
      uint8_t *quote = NULL;
      
      uint32_t maxQuoteLen = TPM_MAX_QUOTE_LEN;
      uint32_t actualQuoteLen = 0;
      *puiRv = TZ_SUCCESS;

      /* Decode input parameters from legacy userspace's test.c */
      if(*puiRv = TZIDecodeBufF(psInBuf,
                                "%"TZI_DARRSPC "%"TZI_DARRSPC,
                                &nonce, &nonceLen,
                                &tpmsel, &tpmselLen))
        break;

      /* Sanity-check input parameters */
      if (tpmselLen != sizeof(TPM_PCR_SELECTION)
          || nonceLen != sizeof(TPM_NONCE)) {
        *puiRv = TZ_ERROR_ENCODE_FORMAT;
        break;
      }

      /* Prepare the output buffer to hold the response back to userspace. */
      if(*puiRv = TZIEncodeBufF(psOutBuf,
                                "%"TZI_EARRSPC,
                                &quote, maxQuoteLen))
        break;
                                     
      /* Make the hypercall to invoke the uTPM operation */
      actualQuoteLen = maxQuoteLen;
      if(*puiRv = pal_quote(nonce, tpmsel, quote, &actualQuoteLen))
        break;

      /* Also encode the actual length of the result */
      if(*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EU32, actualQuoteLen))
        break;
    }
    break;

    case PAL_ID_GETPUB:
    {
      uint8_t *rsaModulus;
      
      /* Prepare the output buffer to hold the response back to userspace. */
      if(*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EARRSPC,
                                &rsaModulus, TPM_RSA_KEY_LEN))
        break;

      if(*puiRv = pal_id_getpub(rsaModulus))
        break;
    }
    break;
    
    case PAL_PCR_EXTEND:
    {
      uint8_t *measIn;
      size_t measLen;
      uint32_t idx;
      *puiRv = TZ_SUCCESS;

      if(*puiRv = TZIDecodeBufF(psInBuf,
                                "%"TZI_DU32 "%"TZI_DARRSPC,
                                &idx,
                                &measIn, &measLen))
        break;

      if(measLen != TPM_HASH_SIZE) {
        *puiRv = TZ_ERROR_GENERIC;
        break;
      }

      if(*puiRv = pal_pcr_extend(idx, measIn))
        break;
    }
    break;
    
    case PAL_PCR_READ:
    {
      uint8_t *valOut;
      uint32_t idx;
      *puiRv = TZ_SUCCESS;

      if(*puiRv = TZIDecodeBufF(psInBuf, "%"TZI_DU32, &idx))
        break;

      if(*puiRv = TZIEncodeBufF(psOutBuf,
                                "%"TZI_EARRSPC,
                                &valOut, TPM_HASH_SIZE))
        break;

      if(*puiRv = pal_pcr_read(idx, valOut))
        break;
    }
    break;

  case PAL_RAND:
    {
      uint32_t len;
      uint8_t *bytes;

      if(*puiRv = TZIDecodeBufF(psInBuf, "%"TZI_DU32, &len))
        break;

      if(*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EARRSPC,
                                &bytes, len))
        break;
      
      if(*puiRv = pal_rand(len, bytes))
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

      if(*puiRv = pal_time_elapsed(&dt))
        break;

      dt_hi = (uint32_t)(dt>>32);
      dt_lo = (uint32_t)dt;
      if(*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EU32 "%"TZI_EU32,
                                dt_hi, dt_lo))
        break;
    }
    break;
  }
  return;
}

/* sensitive code  */

__attribute__ ((section (".scode")))
tz_return_t pal_quote(IN TPM_NONCE *nonce,
                      IN TPM_PCR_SELECTION *tpmsel,
                      OUT uint8_t *quote, INOUT size_t *quote_len) 
{
  if (!svc_utpm_quote(nonce, tpmsel, quote, quote_len)) {
    return TZ_SUCCESS;
  } else {
    return TZ_ERROR_GENERIC;
  }
}

__attribute__ ((section (".scode")))
tz_return_t pal_id_getpub(OUT uint8_t* rsaModulus)
{
    if(!svc_utpm_id_getpub(rsaModulus)) {
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
