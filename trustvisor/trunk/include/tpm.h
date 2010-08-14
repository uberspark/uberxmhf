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

/*
 * \brief   macros, enums and headers for tpm.c
 * \date    2006-03-28
 * \author  Bernhard Kauer <kauer@tudos.org>
 */
/*
 * Copyright (C) 2006  Bernhard Kauer <kauer@tudos.org>
 * Technische Universitaet Dresden, Operating Systems Research Group
 *
 * This file is part of the OSLO package, which is distributed under
 * the  terms  of the  GNU General Public Licence 2.  Please see the
 * COPYING file for details.
 */
/**
 * Modified by Jonathan M. McCune for use with Flicker in 2007.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License v2.0 as published by
 * the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 */


#ifndef _TPM_H
#define _TPM_H

#include <tis.h>

#define TCG_HASH_SIZE                  20
#define TCG_DATA_OFFSET                10
#define TCG_BUFFER_SIZE                ((TCG_DATA_OFFSET+4+TCG_HASH_SIZE))


/**
 * Copy values from the buffer.
 */
#define TPM_COPY_FROM(DEST,OFFSET,SIZE)				\
  slb_assert(TCG_BUFFER_SIZE>=TCG_DATA_OFFSET + OFFSET + SIZE)	\
  slb_memcpy(DEST, &buffer[TCG_DATA_OFFSET + OFFSET], SIZE)

/**
 * Extract long values from the buffer.
 */
#define TPM_EXTRACT_LONG(OFFSET)			\
  slb_ntohl(*(unsigned long *)(buffer+TCG_DATA_OFFSET+OFFSET))


/**
 * Copy values from the buffer.
 */
#define TPM_COPY_TO(DEST,OFFSET,SIZE)				\
  slb_assert(TCG_BUFFER_SIZE>=TCG_DATA_OFFSET + OFFSET + SIZE)	\
  slb_memcpy(&buffer[TCG_DATA_OFFSET + OFFSET], DEST, SIZE)

///////////////////////////////////////////////////////////////////////////


typedef unsigned int TPM_KEY_FLAGS;
typedef unsigned int TPM_ALGORITHM_ID;

typedef unsigned short TPM_STRUCTURE_TAG;
typedef unsigned short TPM_KEY_USAGE;
typedef unsigned short TPM_ENC_SCHEME;
typedef unsigned short TPM_SIG_SCHEME;

typedef unsigned char BYTE;
typedef unsigned char TPM_AUTH_DATA_USAGE;

struct tpm_key_parms {
    TPM_ALGORITHM_ID algorithmID; /* 0-3 */
    TPM_ENC_SCHEME encScheme; /* 4-5 */
    TPM_SIG_SCHEME sigScheme; /* 6-7 */
    unsigned int parmSize; /* 8-b */
    BYTE* parms; /* c */
} __attribute__((packed));

typedef struct tpm_key_parms TPM_KEY_PARMS;

struct tpm_store_pubkey {
    unsigned long keyLength;
    BYTE* key;
} __attribute__((packed));

typedef struct tpm_store_pubkey TPM_STORE_PUBKEY;

/* See Chapter 10 of TPM Structures Specification */
struct tpm_key12
{
    TPM_STRUCTURE_TAG tag; /* 0-1 */
    unsigned short fill; /* 2-3 */
    TPM_KEY_USAGE keyUsage; /* 4-5 */
    TPM_KEY_FLAGS keyFlags; /* 6-9 */
    TPM_AUTH_DATA_USAGE authDataUsage; /* a */
    TPM_KEY_PARMS algorithmParms; /* b-16 (c+) */
    unsigned int PCRInfoSize; /* 17-1a */
    BYTE* PCRInfo; /* 1b+ */
    TPM_STORE_PUBKEY pubKey; /* 1c-20 (5+) */
    unsigned int encDataSize; /* 21-24 */
    BYTE* encData; /* 25+ */
} __attribute__((packed));

typedef struct tpm_key12 TPM_KEY12;

/**
 * 
 */
enum tpm_ords {
    TPM_ORD_OIAP=0xa,
    TPM_ORD_OSAP=0xb,
	TPM_ORD_Extend=0x14,
	TPM_ORD_PcrRead = 0x15,
    TPM_ORD_Seal = 0x17,
    TPM_ORD_Unseal = 0x18,
    TPM_ORD_CreateWrapKey = 0x1f,
    TPM_ORD_LoadKey2 = 0x41,
    TPM_ORD_GetRandom = 0x46,
    TPM_ORD_SelfTestFull = 0x50,
    TPM_ORD_ContinueSelfTest = 0x53,
	TPM_ORD_GetCapability=0x65,
    TPM_ORD_ReadPubek=0x7c,
	TPM_ORD_Startup = 0x99,
    TPM_ORD_CreateCounter = 0xDC,
    TPM_ORD_IncrementCounter = 0xDD,
    TPM_ORD_ReadCounter = 0xDE,
    TPM_ORD_ReleaseCounter = 0xDF,
    TPM_ORD_ReleaseCounterOwner = 0xE0,
};

enum tpm_caps {
	TPM_CAP_PROPERTY=0x5,
};

enum tpm_subcaps {
	TPM_CAP_PROP_PCR   = 0x101,
    TPM_CAP_PROP_MIN_COUNTER = 0x107,
    TPM_CAP_PROP_COUNTERS = 0x10C,
    TPM_CAP_PROP_MAX_COUNTERS = 0x10f,
    TPM_CAP_PROP_ACTIVE_COUNTER = 0x122,
};

enum tpm_subcaps_size {
  TPM_NO_SUBCAP=0x0,
  TPM_SUBCAP=0x4,
};

enum tpm_tags {
    TPM_TAG_RQU_COMMAND = 0xc1,
    TPM_TAG_RQU_AUTH1_COMMAND = 0xc2,
    TPM_TAG_RQU_AUTH2_COMMAND = 0xc3,
    TPM_TAG_RSP_COMMAND = 0xc4,
    TPM_TAG_RSP_AUTH1_COMMAND = 0xc5,
    TPM_TAG_RSP_AUTH2_COMMAND = 0xc6
};

enum tpm_key_handles {
    TPM_KH_SRK = 0x40000000,
};

enum tpm_entity_types {
    TPM_ET_KEYHANDLE = 0x0001, /* keyHandle w/ XOR encryption */
    TPM_ET_OWNER = 0x0002, /* owner w/ XOR encryption */
    TPM_ET_COUNTER = 0x000a, /* counter w/ XOR encryption */
};

enum tpm_return_codes {
    TPM_SUCCESS=0x0,
    TPM_AUTHFAIL=0x1,
    TPM_BAD_PARAMETER=0x3,
    TPM_RESOURCES=0x15,
    TPM_INVALID_PCR_INFO=0x10,
    TPM_ENCRYPT_ERROR=0x20,
    TPM_DECRYPT_ERROR=0x21,
    TPM_INVALID_AUTHHANDLE=0x22,
    TPM_BAD_DATASIZE=0x2b,
    TPM_BAD_COUNTER=0x45,
    TPM_NON_FATAL=0x800,
};

///////////////////////////////////////////////////////////////////////////

int slb_TPM_Extend(unsigned char buffer[TCG_BUFFER_SIZE], unsigned long pcrindex, unsigned char *hash);
int TPM_GetSubCap (unsigned char *buffer, unsigned int *value,
                  unsigned long subcap);
int slb_TPM_PcrRead(unsigned char buffer[TCG_BUFFER_SIZE], unsigned long pcrindex, unsigned char *pcrvalue);
int TPM_GetRandom(unsigned char *buffer, unsigned int bytesRequested, unsigned char *bytes);

void slb_print_tpm_error(int error);
void tpm_deactive(void);
void init_tpm(void);


int initsec_TPM_Extend(unsigned long pcrindex, unsigned char *hash)   __attribute__ ((section ("_init_text")));


//u32 stpm_pcrread(u64 gcr3, u32 buf, u32 index, u32 value);
//u32 stpm_extend(u64 gcr3, u32 buf, u32 index, u32 hash);

#endif
