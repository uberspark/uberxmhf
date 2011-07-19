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

/* TrustVisor's internal Micro-TPM header file */

#ifndef _UTPM_H_
#define _UTPM_H_

#include <types.h>

/* uTPM-specific types and structs common to svcapi and TV internals */
#include <tv_utpm.h> 

typedef struct tdTPM_STORED_DATA{ /* XXX inconsistent with hardware TPM */
  uint32_t sealInfoSize;
  TPM_PCR_INFO sealInfo;       /* structure of TPM_PCR_INFO */
  uint32_t encDataSize;
  uint8_t* encData;  /* encrypted TPM_SEALED_DATA structure containg the confidential part of data*/
} TPM_STORED_DATA;

typedef struct utpm_master_state {
	TPM_DIGEST pcr_bank[TPM_PCR_NUM];
} __attribute__ ((packed)) utpm_master_state_t;

/* TPM functions  */
TPM_RESULT utpm_pcrread(TPM_DIGEST* pcr_value,
                        utpm_master_state_t *utpm, uint32_t pcr_num);
TPM_RESULT utpm_extend(TPM_DIGEST *measurement, utpm_master_state_t *utpm, uint32_t pcr_num);

TPM_RESULT utpm_seal(utpm_master_state_t *utpm,
                     TPM_PCR_INFO *tpmPcrInfo,
                     uint8_t* input, uint32_t inlen,
                     uint8_t* output, uint32_t* outlen,
                     uint8_t* hmackey, uint8_t* aeskey);
TPM_RESULT utpm_unseal(utpm_master_state_t *utpm, uint8_t* input, uint32_t inlen, uint8_t* output, uint32_t* outlen, TPM_COMPOSITE_HASH *digestAtCreation, uint8_t* hmackey, uint8_t* aeskey);

TPM_RESULT utpm_quote(TPM_NONCE* externalnonce, TPM_PCR_SELECTION* tpmsel, /* hypercall inputs */
                      uint8_t* output, uint32_t* outlen, /* hypercall outputs */
                      utpm_master_state_t *utpm, uint8_t* rsa); /* TrustVisor inputs */

/**
 * Keeping these around solely for the Apache SSL web server demo
 */
TPM_RESULT utpm_seal_deprecated(uint8_t* pcrAtRelease, uint8_t* input, uint32_t inlen, uint8_t* output, uint32_t* outlen, uint8_t* hmackey, uint8_t* aeskey);
TPM_RESULT utpm_unseal_deprecated(utpm_master_state_t *utpm, uint8_t* input, uint32_t inlen, uint8_t* output, uint32_t* outlen, uint8_t* hmackey, uint8_t* aeskey);
TPM_RESULT utpm_quote_deprecated(uint8_t* externalnonce, uint8_t* output, uint32_t* outlen,
                      utpm_master_state_t *utpm, uint8_t* tpmsel, uint32_t tpmsel_len, uint8_t* rsa );


TPM_RESULT utpm_rand(uint8_t* buffer, uint32_t *numbytes);

/* internal use. */
void utpm_init_internal(utpm_master_state_t *utpm);

#endif /* _UTPM_H_ */

