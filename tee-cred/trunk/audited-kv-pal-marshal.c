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

#include "audited-kv-pal.h"
#include "audited-kv-pal-fns.h"

#define AKVP_MAX_KEY_LEN 1000
#define AKVP_MAX_VAL_LEN 1000

struct {
  uint32_t uiCommand;
  union {
    struct {
      uint8_t key[AKVP_MAX_KEY_LEN];
      uint8_t val[AKVP_MAX_VAL_LEN];
    } db_add;
  };
} pending_cmd;

void audited_kv_pal(uint32_t uiCommand, struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv)
{
/*   switch(uiCommand) { */
/*   case AKVP_DB_ADD: */
/*     break; */

/*   default: */
/*     *puiRv = TZ_ERROR_NOT_IMPLEMENTED; */
/*   } */

/*   case PAL_PARAM: */
/*     { */
/*       uint32_t input = TZIDecodeUint32(psInBuf); */
/*       uint32_t out; */
/*       *puiRv = TZ_SUCCESS; */

/*       if (TZIDecodeGetError(psInBuf) != TZ_SUCCESS) { */
/*         *puiRv = TZIDecodeGetError(psInBuf); */
/*       } else { */
/*         out = pal_param(input); */
/*         TZIEncodeUint32(psOutBuf, out); */
/*       } */
/*     } */
/*     break; */

/*   case PAL_SEAL: */
/*     { */
/*       uint8_t *in, *out; */
/*       size_t inLen, outLen; */
/*       *puiRv = TZ_SUCCESS; */

/*       in = TZIDecodeArraySpace(psInBuf, &inLen); */
/*       if (TZIDecodeGetError(psInBuf) != TZ_SUCCESS) { */
/*         *puiRv = TZIDecodeGetError(psInBuf); */
/*         break; */
/*       } */

/*       outLen = inLen + 100; /\* XXX guessing at seal overhead *\/ */
/*       out = TZIEncodeArraySpace(psOutBuf, outLen); */
/*       if (out == NULL) { */
/*         *puiRv = TZ_ERROR_MEMORY; */
/*         break; */
/*       } */

/*       *puiRv = pal_seal(in, inLen, out, &outLen); */
/*       if (*puiRv != TZ_SUCCESS) { */
/*         break; */
/*       } */

/*       /\* actual size of previous array *\/ */
/*       TZIEncodeUint32(psOutBuf, outLen); */
/*       if (TZIDecodeGetError(psOutBuf) != TZ_SUCCESS) { */
/*         *puiRv = TZIDecodeGetError(psOutBuf); */
/*         break; */
/*       } */
/*     } */
/*     break; */

/*   case PAL_UNSEAL: */
/*     { */
/*       uint8_t *in, *out; */
/*       size_t inLen, outLen; */
/*       *puiRv = TZ_SUCCESS; */

/*       in = TZIDecodeArraySpace(psInBuf, &inLen); */
/*       if (TZIDecodeGetError(psInBuf) != TZ_SUCCESS) { */
/*         *puiRv = TZIDecodeGetError(psInBuf); */
/*         break; */
/*       } */

/*       outLen = inLen + 100; /\* XXX guessing at unseal overhead, though should actually be negative *\/ */
/*       out = TZIEncodeArraySpace(psOutBuf, outLen); */
/*       if (out == NULL) { */
/*         *puiRv = TZ_ERROR_MEMORY; */
/*         break; */
/*       } */
      
/*       *puiRv = pal_unseal(in, inLen, out, &outLen); */
/*       if (*puiRv != TZ_SUCCESS) { */
/*         break; */
/*       } */

/*       /\* actual size of previous array *\/ */
/*       TZIEncodeUint32(psOutBuf, outLen); */
/*       if (TZIDecodeGetError(psOutBuf) != TZ_SUCCESS) { */
/*         *puiRv = TZIDecodeGetError(psOutBuf); */
/*         break; */
/*       } */
/*     } */
/*     break; */

/*   case PAL_QUOTE: */
/*     { */
/*       TPM_NONCE *nonce = NULL; */
/*       uint32_t nonceLen = 0; */
/*       TPM_PCR_SELECTION *tpmsel = NULL; */
/*       uint32_t tpmselLen = 0; */
/*       uint8_t *quote = NULL; */
      
/*       uint32_t maxQuoteLen = TPM_MAX_QUOTE_LEN; */
/*       uint32_t actualQuoteLen = 0; */
/*       *puiRv = TZ_SUCCESS; */

/*       /\* Decode input parameters from legacy userspace's test.c *\/ */
/*       nonce = (TPM_NONCE*)TZIDecodeArraySpace(psInBuf, &nonceLen); */
/*       tpmsel = (TPM_PCR_SELECTION*)TZIDecodeArraySpace(psInBuf, &tpmselLen); */
/*       if (TZIDecodeGetError(psInBuf) != TZ_SUCCESS) { */
/*         *puiRv = TZIDecodeGetError(psInBuf); */
/*         break; */
/*       } */

/*       /\* Sanity-check input parameters *\/ */
/*       if (tpmselLen != sizeof(TPM_PCR_SELECTION) */
/*           || nonceLen != sizeof(TPM_NONCE)) { */
/*         *puiRv = TZ_ERROR_ENCODE_FORMAT; */
/*         break; */
/*       } */

/*       /\* Prepare the output buffer to hold the response back to userspace. *\/ */
/*       quote = TZIEncodeArraySpace(psOutBuf, maxQuoteLen); */
/*       if (TZIDecodeGetError(psOutBuf) != TZ_SUCCESS) { */
/*         *puiRv = TZIDecodeGetError(psOutBuf); */
/*         break; */
/*       } else if (quote == NULL) { */
/*         *puiRv = TZ_ERROR_GENERIC; */
/*         break; */
/*       } */

/*       /\* Make the hypercall to invoke the uTPM operation *\/ */
/*       actualQuoteLen = maxQuoteLen; */
/*       *puiRv = pal_quote(nonce, tpmsel, quote, &actualQuoteLen); */
/*       if (*puiRv != TZ_SUCCESS) { */
/*         break; */
/*       } */
      
/*       /\* Also encode the actual length of the result *\/ */
/*       TZIEncodeUint32(psOutBuf, actualQuoteLen); */
/*       if (TZIDecodeGetError(psOutBuf) != TZ_SUCCESS) { */
/*         *puiRv = TZIDecodeGetError(psOutBuf); */
/*         break; */
/*       }       */
/*     } */
/*     break; */

/*     case PAL_ID_GETPUB: */
/*     { */
/*       uint8_t *rsaModulus; */
      
/*       /\* Prepare the output buffer to hold the response back to userspace. *\/ */
/*       rsaModulus = TZIEncodeArraySpace(psOutBuf, TPM_RSA_KEY_LEN); */
/*       if (TZIDecodeGetError(psOutBuf) != TZ_SUCCESS) { */
/*         *puiRv = TZIDecodeGetError(psOutBuf); */
/*         break; */
/*       } else if (rsaModulus == NULL) { */
/*         *puiRv = TZ_ERROR_GENERIC; */
/*         break; */
/*       } */

/*       *puiRv = pal_id_getpub(rsaModulus); */
/*       if (*puiRv != TZ_SUCCESS) { */
/*         break; */
/*       }       */
/*     } */
/*     break; */
    
/*     case PAL_PCR_EXTEND: */
/*     { */
/*       uint8_t *measIn; */
/*       size_t measLen; */
/*       uint32_t idx; */
/*       *puiRv = TZ_SUCCESS; */

/*       idx = TZIDecodeUint32(psInBuf); */
/*       measIn = TZIDecodeArraySpace(psInBuf, &measLen); */
/*       if (TZIDecodeGetError(psInBuf) != TZ_SUCCESS) { */
/*         *puiRv = TZIDecodeGetError(psInBuf); */
/*         break; */
/*       } */

/*       if(measLen != TPM_HASH_SIZE) { */
/*         *puiRv = TZ_ERROR_GENERIC; */
/*         break; */
/*       } */

/*       *puiRv = pal_pcr_extend(idx, measIn); */
/*       if (*puiRv != TZ_SUCCESS) { */
/*         break; */
/*       } */
/*     } */
/*     break; */

/* } */
