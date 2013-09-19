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

#ifndef SVCAPI_H
#define SVCAPI_H

#include <stdint.h>
#include <stdlib.h>

#include <trustvisor/tv_utpm.h>

/* typedef void (*svc_fn_t)(uint32_t uiCommand, */
/*                          tzi_encode_buffer_t *psInBuf,  */
/*                          tzi_encode_buffer_t *psOutBuf, */
/*                          tz_return_t *puiRv); */

/* return micro-seconds elapsed from the beginning of the current
 * epoch. when calculating a time interval from t0 to t1, the caller
 * must check that epoch_nonce is identical for both calls. Otherwise
 * the two times are not comparable. This could occur, for example,
 * after a reboot for trusted execution environments without a
 * trustworthy absolute time source.
 *
 * epoch_nonce : a unique identifier for the current epoch
 * us          : microseconds elapsed since the current epoch
 */
int svc_time_elapsed_us(uint64_t *epoch_nonce, /* out */
                        uint64_t *us); /* out */

/* Seal data, optionally controlled by PCR values.
 * pcrInfo points to a TPM_PCR_INFO struct.
 * in_len is the size of the data to be sealed, in bytes
 * out is a pointer at which the sealed data will be stored
 * out_len will be set to the length of the sealed data
 *   FIXME: this is currently output only. TV does not check
 *          that the destination is large enough.
 *
 * Returns 0 on success, nonzero on failure.
 */
int svc_utpm_seal(TPM_PCR_INFO *pcrInfo,
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
int svc_utpm_unseal(void *in,
                    size_t in_len,
                    void *out,
                    size_t *out_len,
                    void *digestAtCreation);

/* generate a TPM quote (FIXME of...?)
 * nonce points to a nonce to be used FIXME: size?
 * tpmsel FIXME what is this?
 * out the quote is written here
 * out_len the length of out is written here.
 *   FIXME: output only?
 *
 * Returns 0 on success, nonzero on failure.
 */
int svc_utpm_quote(TPM_NONCE *nonce, /* in */
                   TPM_PCR_SELECTION *tpmsel, /* in */
                   uint8_t *sig,
                   size_t *sigLen,
                   uint8_t *pcrComposite,
                   size_t *pcrCompositeLen);

/* Extend uTPM PCR 'idx' with new measurement 'meas'.
 * 'meas' is assumed to be exactly 20 bytes.
 *
 * Returns 0 on success, nonzero on failure.
 */
int svc_utpm_pcr_extend(uint32_t idx,   /* in */
                        uint8_t *meas); /* in */

/* Read the value of uTPM PCR 'idx'
 * 'val' is assumed to point to 20 bytes of
 * available space.
 *
 * Returns 0 on success, nonzero on failure.
 */
int svc_utpm_pcr_read(uint32_t idx,  /* in */
                      uint8_t* val); /* out */


/* Read the RSA public key modulus that corresponds to the TrustVisor
 * uTPM identity keypair that is used to sign quotes.
 *
 * Returns 0 on success, nonzero on failure.
 */
int svc_utpm_id_getpub(uint8_t *N,      /* out */
                       size_t *out_len  /* in, out*/ );

/* Request out_len secure-random bytes. The TEE will use some secure
 * source of true entropy, either directly, or to seed a secure PRNG.
 * The TEE may return fewer than the requested number of bytes if
 * insufficient entropy is currently available.
 *
 * out     : random bytes
 * out_len : in: the number of requested bytes,
 *           out: the number of provided bytes
 */
int svc_utpm_rand(void *out, /* out */
                  size_t *out_len); /* in,out */

/* Request out_len secure-random bytes. The TEE will use some secure
 * source of true entropy, either directly, or to seed a secure PRNG.
 * The TEE will block to get more entropy if necessary.
 *
 * out     : random bytes
 * out_len : the number of requested bytes,
 */
int svc_utpm_rand_block(void *out, /* out */
                        size_t out_len); /* in */

/* Get the size of the TrustVisor-internal Hardware TPM NVRAM space
 * dedicated to providing rollback resistance for a privileged NV
 * Multiplexor PAL (NvMuxPal).
 *
 * size : the number of bytes that fit in the relevant NVRAM index.
 */
int svc_tpmnvram_getsize(size_t *size); /* out */

/* Get the bytes stored in the TrustVisor-internal Hardware TPM NVRAM
 * space dedicated to providing rollback resistance for a privileged
 * NV Multiplexor PAL (NvMuxPal).
 *
 * out : a buffer to hold the contents from NVRAM; had better be big
 * enough.
 */
int svc_tpmnvram_readall(uint8_t *out); /* out */

/* Write the provided bytes into the TrustVisor-internal Hardware TPM NVRAM
 * space dedicated to providing rollback resistance for a privileged
 * NV Multiplexor PAL (NvMuxPal).
 *
 * in : a buffer holding the data to write into NVRAM; had better be
 * big enough.
 */
int svc_tpmnvram_writeall(uint8_t *in); /* in */

#endif
