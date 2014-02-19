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

#include <stddef.h>
#include <stdint.h>

#include <tee-sdk/tzmarshal.h>

#include <trustvisor/tv_utpm.h>

typedef enum {
  PAL_WITHOUTPARAM,
  PAL_PARAM,
  PAL_SEAL,
  PAL_UNSEAL,
  PAL_QUOTE,
  PAL_ID_GETPUB,
  PAL_PCR_READ,
  PAL_PCR_EXTEND,
  PAL_RAND,
  PAL_TIME_INIT,
  PAL_TIME_ELAPSED,
  PAL_NV_ROLLBACK,
} PAL_CMD;

void pals(uint32_t uiCommand, tzi_encode_buffer_t *psInBuf, tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv);
void pal_withoutparam();
uint32_t pal_param(uint32_t input);
tz_return_t pal_seal(TPM_PCR_INFO *pcrInfo, uint8_t *input, uint32_t inputLen, uint8_t *output, size_t *outputLen);
tz_return_t pal_unseal(uint8_t *input, uint8_t inputLen, uint8_t *output, size_t *outputLen, uint8_t *digestAtCreation);
tz_return_t pal_quote(IN TPM_NONCE *nonce,
                      IN TPM_PCR_SELECTION *tpmsel,
                      OUT uint8_t *quote, INOUT size_t *quote_len,
                      OUT uint8_t *pcrComp, INOUT size_t *pcrCompLen); 
tz_return_t pal_id_getpub(OUT uint8_t* rsaModulus, INOUT size_t *sz);
tz_return_t pal_pcr_extend(IN uint32_t idx,
                           IN uint8_t *meas);
tz_return_t pal_pcr_read(IN uint32_t idx,
                        OUT uint8_t *val);
tz_return_t pal_rand(IN size_t len,
                     OUT uint8_t *bytes);
tz_return_t pal_time_init();
tz_return_t pal_time_elapsed(OUT uint64_t *us);
tz_return_t pal_nv_rollback(IN uint8_t *newval,
                            OUT uint32_t *nv_size,
                            OUT uint8_t *oldval);
