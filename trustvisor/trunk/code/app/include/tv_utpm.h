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

/**
 * Common type and structure definitions across TrustVisor's internal
 * Micro-TPM implementation, tee-sdk's svcapi, and any PAL writer who
 * uses any of the relevant Micro-TPM operations.
 */

#ifndef _TV_UTPM_H_
#define _TV_UTPM_H_

/* TODO: types.h lives in various places depending on where we are
 * compiling. The current header must be included after the relevant
 * types.h is included. Need to fix this elegantly. */
/* #include <types.h> */

/* FIXME: A lot of these values are also defined in the public header
 * files for a TSS.  We should consider leveraging those and changing
 * the names here of the ones where we break compatibility. */

/* constant value for TPM chip */
#define TPM_RSA_KEY_LEN                256 /* RSA key size is 2048 bit */
#define TPM_HASH_SIZE                  20

#define  MAX_PCR_SEL_NUM 4
#define  MAX_PCR_SEL_SIZE (4+4*MAX_PCR_SEL_NUM)
#define  MAX_PCR_DATA_SIZE (MAX_PCR_SEL_NUM*20)

#define  MAX_TPM_EXTEND_DATA_LEN 4096
#define  MAX_TPM_RAND_DATA_LEN 4096

#define TPM_QUOTE_SIZE ( 8 + MAX_PCR_SEL_SIZE + MAX_PCR_DATA_SIZE + TPM_NONCE_SIZE + TPM_RSA_KEY_LEN )

#define TPM_CONFOUNDER_SIZE 20

/* Return codes for uTPM operations. */
#define UTPM_SUCCESS 0
#define UTPM_ERR_BAD_PARAM 1
#define UTPM_ERR_PCR_OUT_OF_RANGE 2

typedef uint32_t TPM_RESULT;

#define TPM_PCR_NUM                    8

typedef struct tdTPM_PCR_SELECTION { 
    uint16_t sizeOfSelect;            /* The size in bytes of the pcrSelect structure */
    uint8_t pcrSelect[TPM_PCR_NUM/8]; /* This SHALL be a bit map that indicates if a PCR
                                            is active or not */
} TPM_PCR_SELECTION; 

#define TPM_MAX_QUOTE_LEN ( \
    sizeof(TPM_PCR_SELECTION) + sizeof(uint32_t) \
    + TPM_PCR_NUM*TPM_HASH_SIZE /* max size of TPM_PCR_COMPOSITE */ \
    + sizeof(uint32_t)          /* sigSize */ \
    + TPM_RSA_KEY_LEN)          /* sig */


static inline void utpm_pcr_select_i(TPM_PCR_SELECTION *tpmsel, uint32_t i) {
    /* TODO: fail loudly if any of these conditions do not hold */
    if(NULL == tpmsel) return;
    if(i >= TPM_PCR_NUM) return;    
    if(i/8 >= tpmsel->sizeOfSelect) return;

    if(tpmsel->sizeOfSelect < i/8) { tpmsel->sizeOfSelect = i/8; } /* XXX not future-proof */
    /* Set the bit corresponding to PCR i */
    tpmsel->pcrSelect[i/8] |= (1 << (i%8));
}

static inline bool utpm_pcr_is_selected(TPM_PCR_SELECTION *tpmsel, uint32_t i) {
    /* TODO: fail loudly if any of these conditions do not hold */
    if(NULL == tpmsel) return false;
    if(i >= TPM_PCR_NUM) return false;
    if(i/8 >= tpmsel->sizeOfSelect) return false;

    return (tpmsel->pcrSelect[i/8] & (1 << (i%8)));
}

typedef struct tdTPM_DIGEST{
  uint8_t value[TPM_HASH_SIZE];
} TPM_DIGEST;

typedef TPM_DIGEST TPM_COMPOSITE_HASH;

typedef struct tdTPM_PCR_INFO { 
    TPM_PCR_SELECTION pcrSelection;      /* This SHALL be the selection of PCRs to which the
                                            data or key is bound. */
    TPM_COMPOSITE_HASH digestAtRelease;  /* This SHALL be the digest of the PCR indices and
                                            PCR values to verify when revealing Sealed Data
                                            or using a key that was wrapped to PCRs.  NOTE:
                                            This is passed in by the host, and used as
                                            authorization to use the key */
    TPM_COMPOSITE_HASH digestAtCreation; /* This SHALL be the composite digest value of the
                                            PCR values, at the time when the sealing is
                                            performed. NOTE: This is generated at key
                                            creation, but is just informative to the host,
                                            not used for authorization */
} TPM_PCR_INFO; 

#define TPM_NONCE_SIZE 20
typedef struct tdTPM_NONCE{
  uint8_t nonce[TPM_NONCE_SIZE];
} TPM_NONCE;

/* structure for storage */ /* XXX inconsistent with hardware TPM */
typedef struct tdTPM_SEALED_DATA{
  /*TPM_HMAC hmac;*/ /* NOT SURE HMAC */
  uint32_t dataSize;        
  uint8_t* data;        /*data to be sealed*/
} TPM_SEALED_DATA;

typedef struct tdTPM_STRUCT_VER{
  uint8_t major;   /* 0x01 */
  uint8_t minor;   /* 0x01 */
  uint8_t revMajor; /* 0x00 */
  uint8_t revMinor; /* 0x00 */
} TPM_STRUCT_VER;

typedef struct tdTPM_QUOTE_INFO{
  TPM_STRUCT_VER version;  /* must be 1.1.0.0 based on TPM part2 structure */
  uint8_t fixed[4];           /* this always be the string 'QUOT'*/
  TPM_COMPOSITE_HASH digestValue; 
  TPM_NONCE externalData;
} TPM_QUOTE_INFO;



#endif /* _TV_UTPM_H_ */





