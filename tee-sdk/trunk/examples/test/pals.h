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

#include <marshal.h>

typedef enum {
  PAL_WITHOUTPARAM,
  PAL_PARAM,
  PAL_SEAL,
  PAL_UNSEAL,
  PAL_QUOTE
} PAL_CMD;

void pal_entry(uint32_t uiCommand, tzi_encode_buffer_t *psInBuf, tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv);
void pal_withoutparam();
uint32_t pal_param(uint32_t input);
tz_return_t pal_seal(uint8_t *input, uint8_t inputLen, uint8_t *output, size_t *outputLen);
tz_return_t pal_unseal(uint8_t *input, uint8_t inputLen, uint8_t *output, size_t *outputLen);
tz_return_t pal_quote(IN uint8_t *nonce, /* assumed to be TPM_NONCE_SIZE */
                      IN uint32_t *tpmsel, /* first element is how many other elements there are */
                      OUT uint8_t *quote, OUT size_t *quote_len);
