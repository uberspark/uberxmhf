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
#include  "pals.h"

#include <tee-sdk/tzmarshal.h>
#include <tee-sdk/svcapi.h>

__attribute__ ((section (".scode")))
void pal_entry(uint32_t uiCommand, tzi_encode_buffer_t *psInBuf, tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv)
{
  switch(uiCommand) {
  case PAL_WITHOUTPARAM:
    *puiRv = TZ_SUCCESS;
    pal_withoutparam();
    break;

  case PAL_PARAM:
    {
      uint32_t input = TZIDecodeUint32(psInBuf);
      uint32_t out;
      *puiRv = TZ_SUCCESS;

      if (TZIDecodeGetError(psInBuf) != TZ_SUCCESS) {
        *puiRv = TZIDecodeGetError(psInBuf);
      } else {
        out = pal_param(input);
        TZIEncodeUint32(psOutBuf, out);
      }
    }
    break;

  case PAL_SEAL:
    {
      uint8_t *in, *out;
      size_t inLen, outLen;
      *puiRv = TZ_SUCCESS;

      in = TZIDecodeArraySpace(psInBuf, &inLen);
      if (TZIDecodeGetError(psInBuf) != TZ_SUCCESS) {
        *puiRv = TZIDecodeGetError(psInBuf);
        break;
      }

      outLen = inLen + 100; /* XXX guessing at seal overhead */
      out = TZIEncodeArraySpace(psOutBuf, outLen);
      if (out == NULL) {
        *puiRv = TZ_ERROR_MEMORY;
        break;
      }

      *puiRv = pal_seal(in, inLen, out, &outLen);
      if (*puiRv != TZ_SUCCESS) {
        break;
      }

      /* actual size of previous array */
      TZIEncodeUint32(psOutBuf, outLen);
      if (TZIDecodeGetError(psOutBuf) != TZ_SUCCESS) {
        *puiRv = TZIDecodeGetError(psOutBuf);
        break;
      }
    }
    break;

  case PAL_UNSEAL:
    {
      uint8_t *in, *out;
      size_t inLen, outLen;
      *puiRv = TZ_SUCCESS;

      in = TZIDecodeArraySpace(psInBuf, &inLen);
      if (TZIDecodeGetError(psInBuf) != TZ_SUCCESS) {
        *puiRv = TZIDecodeGetError(psInBuf);
        break;
      }

      outLen = inLen + 100; /* XXX guessing at unseal overhead, though should actually be negative */
      out = TZIEncodeArraySpace(psOutBuf, outLen);
      if (out == NULL) {
        *puiRv = TZ_ERROR_MEMORY;
        break;
      }
      
      *puiRv = pal_unseal(in, inLen, out, &outLen);
      if (*puiRv != TZ_SUCCESS) {
        break;
      }

      /* actual size of previous array */
      TZIEncodeUint32(psOutBuf, outLen);
      if (TZIDecodeGetError(psOutBuf) != TZ_SUCCESS) {
        *puiRv = TZIDecodeGetError(psOutBuf);
        break;
      }
    }
    break;

  case PAL_QUOTE:
    {
      uint8_t *nonce;
      uint32_t nonceLen;
      uint32_t *tpmsel;
      uint32_t tpmselLen;
      uint8_t *quote;
      uint32_t quoteLen = 800; /* FIXME should be TPM_QUOTE_SIZE, or dynamically check */;
      *puiRv = TZ_SUCCESS;

      nonce = TZIDecodeArraySpace(psInBuf, &nonceLen);
      tpmsel = TZIDecodeArraySpace(psInBuf, &tpmselLen);
      if (TZIDecodeGetError(psInBuf) != TZ_SUCCESS) {
        *puiRv = TZIDecodeGetError(psInBuf);
        break;
      }

      /* decodearrayspace deals with size in bytes. convert to uint32_t.
       * XXX write an API extension to deal with these situations?
       */
      if (tpmselLen % sizeof(uint32_t) != 0) {
        *puiRv = TZ_ERROR_ENCODE_FORMAT;
        break;
      }
      tpmselLen /= sizeof(uint32_t);

      quote = TZIEncodeArraySpace(psOutBuf, quoteLen);
      if (TZIDecodeGetError(psOutBuf) != TZ_SUCCESS) {
        *puiRv = TZIDecodeGetError(psOutBuf);
        break;
      } else if (quote == NULL) {
        *puiRv = TZ_ERROR_GENERIC;
        break;
      }

      *puiRv = pal_quote(nonce, tpmsel, quote, &quoteLen);
      if (*puiRv != TZ_SUCCESS) {
        break;
      }

      TZIEncodeUint32(psOutBuf, quoteLen);
      if (TZIDecodeGetError(psOutBuf) != TZ_SUCCESS) {
        *puiRv = TZIDecodeGetError(psOutBuf);
        break;
      }
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
tz_return_t pal_seal(uint8_t *input, uint8_t inputLen, uint8_t *output, size_t *outputLen)
{
  if (scode_seal(NULL, input, inputLen, output, outputLen) == 0) {
    return TZ_SUCCESS;
  } else {
    return TZ_ERROR_GENERIC;
  }
}

__attribute__ ((section (".scode")))
tz_return_t pal_unseal(uint8_t *input, uint8_t inputLen, uint8_t *output, size_t *outputLen)
{
  if (scode_unseal(input, inputLen, output, outputLen) == 0) {
    return TZ_SUCCESS;
  } else {
    return TZ_ERROR_GENERIC;
  }
}

__attribute__ ((section (".scode")))
tz_return_t pal_quote(IN uint8_t *nonce, /* assumed to be TPM_NONCE_SIZE */
                      IN uint32_t *tpmsel, /* first element is how many other elements there are */
                      OUT uint8_t *quote, OUT size_t *quote_len) 
{
  /* int i; */
  /* uint8_t nonce[20]; */
  /* uint8_t tpmsel[8]; */
  /* *((unsigned int *)tpmsel)=1; */
  /* *((unsigned int *)(tpmsel+4))=0; */

  /* for( i=0 ; i<20 ; i++ )  { */
  /*   nonce[i]=((char)i)+tpmsel[i%8]; */
  /* } */

  if (!scode_quote(nonce, tpmsel, quote, quote_len)) {
    return TZ_SUCCESS;
  } else {
    return TZ_ERROR_GENERIC;
  }
}
