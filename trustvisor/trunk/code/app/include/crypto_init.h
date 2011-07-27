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

#ifndef _CRYPTO_INIT_H_
#define _CRYPTO_INIT_H_

#include <rsa.h>

#define CTR_DRBG_SEED_BITS 256
#define CTR_DRBG_NONCE_BITS 64

/* softTPM related definitions */
#define TPM_PCR_SIZE                   20
#define TPM_AES_KEY_LEN                128 /* key size is 128 bit */
#define TPM_HMAC_KEY_LEN               20

/* max len of sealed data */
#define  MAX_SEALDATA_LEN 2048
#define  SEALDATA_HEADER_LEN 48

extern u8 g_aeskey[TPM_AES_KEY_LEN/8];
extern u8 g_hmackey[TPM_HMAC_KEY_LEN];
extern rsa_context g_rsa;


int get_hw_tpm_entropy(uint8_t* buf, unsigned int requested_len /* bytes */);
int trustvisor_master_crypto_init(void);

#endif /* _CRYPTO_INIT_H_ */

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* tab-width:2      */
/* End:             */

