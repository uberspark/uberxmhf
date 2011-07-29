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
} PAL_CMD;

void pals(uint32_t uiCommand, tzi_encode_buffer_t *psInBuf, tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv);
void pal_withoutparam();
tz_return_t pal_quote(IN TPM_NONCE *nonce,
                      IN TPM_PCR_SELECTION *tpmsel,
                      OUT uint8_t *quote, OUT size_t *quote_len);
tz_return_t pal_id_getpub(OUT uint8_t* rsaModulus);
tz_return_t pal_pcr_extend(IN uint32_t idx,
                           IN uint8_t *meas);
tz_return_t pal_pcr_read(IN uint32_t idx,
                        OUT uint8_t *val);
tz_return_t pal_rand(IN size_t len,
                     OUT uint8_t *bytes);
tz_return_t pal_time_init();
tz_return_t pal_time_elapsed(OUT uint64_t *us);
