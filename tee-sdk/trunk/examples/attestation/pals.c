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

/* sensitive code */
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
    TPM_DIGEST *uPcr0 = NULL;
    TPM_DIGEST *uPcr1 = NULL;
    uint8_t *rsaModulus = NULL;

    *puiRv = TZ_SUCCESS;

    /* Decode input parameters from legacy userspace's test.c */
    if((*puiRv = TZIDecodeBufF(psInBuf,
                               "%"TZI_DARRSPC "%"TZI_DARRSPC "%"TZI_DARRSPC,
                               &nonce, &nonceLen,
                               &tpmsel, &tpmselLen,
                               &inpAscii, &inpAsciiLen)))
        return;
    
    /* Sanity-check input parameters */
    if (tpmselLen != sizeof(TPM_PCR_SELECTION)
        || nonceLen != sizeof(TPM_NONCE)
        || inpAsciiLen < 1) {
        *puiRv = TZ_ERROR_ENCODE_FORMAT;
        return;
    }

    /* Prepare the output buffer to hold the response back to userspace. */
    if((*puiRv = TZIEncodeBufF(psOutBuf,
                               "%"TZI_EARRSPC "%"TZI_EARRSPC "%"TZI_EARRSPC "%"TZI_EARRSPC "%"TZI_EARRSPC,
                               &uPcr0, sizeof(TPM_DIGEST),
                               &uPcr1, sizeof(TPM_DIGEST),
                               &rsaModulus, TPM_RSA_KEY_LEN,
                               &pcrComp, pcrCompLen, 
                               &quote, maxQuoteLen)))
        return;

    
    
    /**
     * Make the hypercalls to invoke the uTPM operations
     */

    /* Extend uPCR 1 with input data */
    /* XXX -- TODO: need SHA-1 to hash arbitrary-length input data */
    /* if(inpAsciiLen */
    /*   if(*puiRv = pal_pcr_extend(idx, measIn)) */
          
    /* Read uPCR 0,1 */
    if((*puiRv = pal_pcr_read(0, uPcr0->value))) return;
    if((*puiRv = pal_pcr_read(1, uPcr1->value))) return;

    /* Read the public key modulus for the keypair that signs the quote */
    if((*puiRv = pal_id_getpub(rsaModulus))) return;

    /* Request the actual uPCR quote from the uTPM */
    actualQuoteLen = maxQuoteLen;
    if((*puiRv = pal_quote(nonce, tpmsel, quote, &actualQuoteLen, pcrComp, &pcrCompLen))) return;
    
    /* Also encode the _actual_ length of the quote */
    if((*puiRv = TZIEncodeBufF(psOutBuf, "%"TZI_EU32, actualQuoteLen))) return;
}


