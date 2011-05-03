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

#ifndef SVCAPI_H
#define SVCAPI_H

#include <stdint.h>
#include <stdlib.h>

/* typedef void (*svc_fn_t)(uint32_t uiCommand, */
/*                          tzi_encode_buffer_t *psInBuf,  */
/*                          tzi_encode_buffer_t *psOutBuf, */
/*                          tz_return_t *puiRv); */

/* Seal data under a pcr value.
 * pcrAtRelease_addr is the required value of pcr #FIXME the
 *   data to be unsealed.
 * in points to the data to be sealed.
 * in_len is the size of the data to be sealed, in bytes
 * out is a pointer at which the sealed data will be stored
 * out_len will be set to the length of the sealed data
 *   FIXME: this is currently output only. TV does not check
 *          that the destination is large enough.
 *
 * Returns 0 on success, nonzero on failure.
 */
int scode_seal(uint8_t *pcrAtRelease_addr,
               void *in,
               size_t in_len,
               void *out,
               size_t *out_len);

/* unseal data
 * in is a pointer to the data to be unsealed.
 * in_len is the size of the sealed data, in bytes
 * out is a pointer at which the unsealed data will be stored
 * out_len will be set to the length of the unsealed data
 *   FIXME: this is currently output only. TV does not check
 *          that the destination is large enough.
 *
 * Returns 0 on success, nonzero on failure.
 */
int scode_unseal(void *in,
                 size_t in_len,
                 void *out,
                 size_t *out_len);

/* generate a TPM quote (FIXME of...?)
 * nonce points to a nonce to be used FIXME: size?
 * tpmsel FIXME what is this?
 * out the quote is written here
 * out_len the length of out is written here.
 *   FIXME: output only?
 *
 * Returns 0 on success, nonzero on failure.
 */
int scode_quote(uint8_t *nonce,
                uint32_t *tpmsel,
                uint8_t *out,
                size_t *out_len);
/* Extend uTPM PCR 'idx' with new measurement 'meas'.
 * 'meas' is assumed to be exactly 20 bytes.
 *
 * Returns 0 on success, nonzero on failure.
 */
int scode_pcr_extend(uint32_t idx,   /* in */
                     uint8_t *meas); /* in */

/* Read the value of uTPM PCR 'idx'
 * 'val' is assumed to point to 20 bytes of
 * available space.
 *
 * Returns 0 on success, nonzero on failure.
 */
int scode_pcr_read(uint32_t idx,  /* in */
                   uint8_t* val); /* out */
#endif
