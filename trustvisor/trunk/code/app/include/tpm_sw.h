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

/* Software TPM header file */

#ifndef _SW_TPM_H
#define _SW_TPM_H
#include <types.h>

/* TPM commands for trustvisor */
#define HV_EXTEND                      1
#define HV_SEAL                        2
#define HV_UNSEAL                      3
#define HV_QUOTE                       4

/* TPM FLAGS */
#define TPM_ACTIVE_FLAGS_FALSE      0   
#define TPM_ACTIVE_FLAGS_TRUE       1

/* constant value for TPM chip */
#define TPM_RSA_KEY_LEN                256 /* RSA key size is 2048 bit */
#define TPM_HASH_SIZE                  20
#define TPM_NONCE_SIZE                 20

#define  MAX_PCR_SEL_NUM 4
#define  MAX_PCR_SEL_SIZE (4+4*MAX_PCR_SEL_NUM)
#define  MAX_PCR_DATA_SIZE (MAX_PCR_SEL_NUM*20)

#define  MAX_TPM_EXTEND_DATA_LEN 4096
#define  MAX_TPM_RAND_DATA_LEN 4096

#define TPM_QUOTE_SIZE ( 8 + MAX_PCR_SEL_SIZE + MAX_PCR_DATA_SIZE + TPM_NONCE_SIZE + TPM_RSA_KEY_LEN )

#define  TPM_CONFOUNDER_SIZE 20

/* Return codes for uTPM operations. */
#define UTPM_SUCCESS 0
#define UTPM_ERR_BAD_PARAM 1
#define UTPM_ERR_PCR_OUT_OF_RANGE 2

typedef struct tdTPM_NONCE{
  u8 nonce[TPM_NONCE_SIZE];
} TPM_NONCE;

/* Keys used in TPM */

typedef struct tdTPM_COMPOSITE_HASH{
  u8 value[TPM_HASH_SIZE];
} TPM_COMPOSITE_HASH;

typedef struct tdTPM_PCR_INFO{
  TPM_COMPOSITE_HASH digestAtRelease; 
  TPM_COMPOSITE_HASH digestAtCreation;
} TPM_PCR_INFO;

typedef struct tdTPM_STRUCT_VER{
  u8 major;   /* 0x01 */
  u8 minor;   /* 0x01 */
  u8 revMajor; /* 0x00 */
  u8 revMinor; /* 0x00 */
} TPM_STRUCT_VER;

typedef struct tdTPM_QUOTE_INFO{
  TPM_STRUCT_VER version;  /* must be 1.1.0.0 based on TPM part2 structure */
  u8 fixed[4];           /* this always be the string 'QUOT '*/
  TPM_COMPOSITE_HASH digestValue; 
  TPM_NONCE externalData;
} TPM_QUOTE_INFO;

/* structure for storage */
typedef struct tdTPM_SEALED_DATA{
  /*TPM_HMAC hmac;*/ /* NOT SURE HMAC */
  u32 dataSize;        
  u8* data;        /*data to be sealed*/
} TPM_SEALED_DATA;

typedef struct tdTPM_STORED_DATA{
  u32 sealInfoSize;
  TPM_PCR_INFO sealInfo;       /* s tructure of TPM_PCR_INFO */
  u32 encDataSize;
  u8* encData;  /* encrypted TPM_SEALED_DATA structure containg the confidential part of data*/
} TPM_STORED_DATA;

/* TPM functions  */
u32 stpm_pcrread(u8* pcr_value, u8* pcr_bank, u32 pcr_num);
u32 stpm_extend(u8* measurement, u8* pcr_bank, u32 pcr_num);
u32 stpm_seal(u8* pcrAtRelease, u8* input, u32 inlen, u8* output, u32* outlen, u8* hmackey, u8* aeskey);
u32 stpm_unseal(u8* pcr_bank, u8* input, u32 inlen, u8* output, u32* outlen, u8* hmackey, u8* aeskey);
u32 stpm_quote(u8* externalnonce, u8* output, u32* outlen, u8* pcr_bank, u8* tpmsel, u32 tpmsel_len, u8* rsa );
//u32 stpm_rand(u8* buffer, u32 numbytes);
#endif

