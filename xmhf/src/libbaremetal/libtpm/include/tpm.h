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

/*
 * tpm.h: TPM-related support functions
 *
 * Copyright (c) 2006-2009, Intel Corporation
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above
 *     copyright notice, this list of conditions and the following
 *     disclaimer in the documentation and/or other materials provided
 *     with the distribution.
 *   * Neither the name of the Intel Corporation nor the names of its
 *     contributors may be used to endorse or promote products derived
 *     from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#ifndef __TPM_H__
#define __TPM_H__

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

//======================================================================
//libtpm environment specific functions
//the following need to be defined within the target environment
//that uses libtpm
//e.g., EMHF-x86

#ifndef __ASSEMBLY__


extern uint32_t tpm_wait_cmd_ready(uint32_t locality);


extern uint32_t tpm_write_cmd_fifo(uint32_t locality, uint8_t *in,
                                   uint32_t in_size, uint8_t *out,
                                   uint32_t *out_size);

#endif //__ASSEMBLY__
//======================================================================


#define TPM_NR_LOCALITIES             5


/*
 * return code:
 * The TPM has five types of return code. One indicates successful operation
 * and four indicate failure.
 * TPM_SUCCESS (00000000) indicates successful execution.
 * The failure reports are:
 *      TPM defined fatal errors (00000001 to 000003FF)
 *      vendor defined fatal errors (00000400 to 000007FF)
 *      TPM defined non-fatal errors (00000800 to 00000BFF)
 *      vendor defined non-fatal errors (00000C00 to 00000FFF).
 * Here only give definitions for a few commonly used return code.
 */
#define TPM_BASE                0x00000000
#define TPM_NON_FATAL           0x00000800
#define TPM_SUCCESS             TPM_BASE
#define TPM_BADINDEX            (TPM_BASE + 2)
#define TPM_BAD_PARAMETER       (TPM_BASE + 3)
#define TPM_DEACTIVATED         (TPM_BASE + 6)
#define TPM_DISABLED            (TPM_BASE + 7)
#define TPM_FAIL                (TPM_BASE + 9)
#define TPM_BAD_ORDINAL         (TPM_BASE + 10)
#define TPM_NOSPACE             (TPM_BASE + 17)
#define TPM_NOTRESETABLE        (TPM_BASE + 50)
#define TPM_NOTLOCAL            (TPM_BASE + 51)
#define TPM_BAD_LOCALITY        (TPM_BASE + 61)
#define TPM_READ_ONLY           (TPM_BASE + 62)
#define TPM_NOT_FULLWRITE       (TPM_BASE + 70)
#define TPM_RETRY               (TPM_BASE + TPM_NON_FATAL)

#ifndef __ASSEMBLY__


#define TPM_DIGEST_SIZE          20
typedef struct __attribute__ ((packed)) {
    uint8_t     digest[TPM_DIGEST_SIZE];
} tpm_digest_t;
typedef tpm_digest_t tpm_pcr_value_t;

/*
 * specified as minimum cmd buffer size should be supported by all 1.2 TPM
 * device in the TCG_PCClientTPMSpecification_1-20_1-00_FINAL.pdf
 */
#define TPM_CMD_SIZE_MAX        768
#define TPM_RSP_SIZE_MAX        768

#define TPM_NR_PCRS             24


extern uint32_t tpm_get_version(uint8_t *major, uint8_t *minor);

/*
 * tpm_pcr_read fetchs the current value of given PCR vai given locality.
 * locality     : TPM locality (0 - 4)
 * pcr          : PCR index (0 - 23)
 * out          : PCR value buffer, out parameter, should not be NULL
 * return       : TPM_SUCCESS for success, error code defined as TPM_xxx
 */
extern uint32_t tpm_pcr_read(uint32_t locality, uint32_t pcr,
                             tpm_pcr_value_t *pcr_value);

/*
 * tpm_pcr_extend extends data octets into given PCR via given locality,
 * and return the PCR value after extending if required.
 * locality     : TPM locality (0 - 4)
 * pcr          : PCR index (0 - 23)
 * in           : Hash value to be extended into PCR, should not be NULL
 * out          : Out buffer for PCR value after extending, may be NULL
 * return       : TPM_SUCCESS for success, error code defined as TPM_xxx
 */
extern uint32_t tpm_pcr_extend(uint32_t locality, uint32_t pcr,
                               const tpm_digest_t* in, tpm_pcr_value_t* out);

/* PCRs lower than 16 are not resetable */
#define TPM_PCR_RESETABLE_MIN           16

/*
 * tpm_pcr_reset resets given PCR via given locality.
 * locality     : TPM locality (0 - 4)
 * pcr          : PCR index (16 - 23)
 * return       : TPM_SUCCESS for success, error code defined as TPM_xxx
 */
extern uint32_t tpm_pcr_reset(uint32_t locality, uint32_t pcr);

#define TPM_NV_READ_VALUE_DATA_SIZE_MAX  (TPM_RSP_SIZE_MAX - 14)

typedef uint32_t tpm_nv_index_t;

/*
 * tpm_nv_read_value reads data from TPM NV ram in the given locality.
 * locality     : TPM locality (0 - 4)
 * index        : Predefined index for certain NV space
 * offset       : Start reading from offset given by this parameter.
 * data         : Out buffer for read data, should not be NULL
 * data_size    : As IN, give the size required to read, should not be NULL;
 *              : as OUT, return the size really read from TPM.
 *              : The largest nv data size can be read in a single call is
 *              : defined by TPM_NV_READ_VALUE_DATA_SIZE_MAX.
 * return       : TPM_SUCCESS for success, error code defined as TPM_xxx
 */
extern uint32_t tpm_nv_read_value(uint32_t locality, tpm_nv_index_t index,
                                  uint32_t offset, uint8_t *data,
                                  uint32_t *data_size);

#define TPM_NV_WRITE_VALUE_DATA_SIZE_MAX (TPM_CMD_SIZE_MAX - 22)

/*
 * tpm_nv_write_value writes data into TPM NV ram in the given locality.
 * locality     : TPM locality (0 - 4)
 * index        : Predefined index for certain NV space
 * offset       : Start writing from offset given by this parameter.
 * data         : Data to be written to TPM NV, should not be NULL
 * data_size    : The size of data to be written.
 *              : The largest nv data size can be written in a single call
 *              : is defined by TPM_NV_WRITE_VALUE_DATA_SIZE_MAX.
 * return       : TPM_SUCCESS for success, error code defined as TPM_xxx
 */
extern uint32_t tpm_nv_write_value(uint32_t locality, tpm_nv_index_t index,
                                   uint32_t offset, const uint8_t *data,
                                   uint32_t data_size);

typedef uint8_t tpm_locality_selection_t;
#define TPM_LOC_ZERO    0x01
#define TPM_LOC_ONE     0x02
#define TPM_LOC_TWO     0x04
#define TPM_LOC_THREE   0x08
#define TPM_LOC_FOUR    0x10
#define TPM_LOC_RSVD    0xE0

/*
 * tpm_seal seal given data (in_data[in_data_size]) to given pcrs
 * (pcr_indcs_create[pcr_nr_create]). The sealed data can only be unsealed
 * while the given pcrs (pcr_indcs_release[pcr_nr_release]) met given values
 * (pcr_values_release[pcr_nr_release]), and under one of the given release
 * locality (release_locsa).
 *
 * locality     : TPM locality (0 - 4)
 * release_locs : should be one or composition of TPM_LOC_ZERO to TPM_LOC_FOUR
 * pcr_nr_create: the number of pcrs which will be used as creation pcrs
 * pcr_indcs_create
 *              : an array of pcr indices, size is pcr_nr_create.
 * pcr_nr_release
 *              : the number of pcrs which will be used as release pcrs
 * pcr_indcs_release
 *              : an array of pcr indices, size is pcr_nr_release.
 * pcr_values_release
 *              : an array of pointers to pcr value, size is pcr_nr_release.
 * in_data_size : The size of data to be sealed.
 * in_data      : Data to be sealed, should not be NULL
 * sealed_data_size
 *              : [in] the size of prepared output buffer (sealed_data)
 *                [out] the size of sealed data blob
 * sealed_data  : [out] the buffer to receive sealed data blob. The buffer
 *                size should be large enough. For example, the sealed blob
 *                for 20-byte data will need buffer larger than 322 bytes.
 * return       : TPM_SUCCESS for success, error code defined as TPM_xxx
 *                TPM_NOSPACE for insufficient output buffer
 */
extern uint32_t tpm_seal(
                  uint32_t locality, tpm_locality_selection_t release_locs,
                  uint32_t pcr_nr_create, const uint8_t pcr_indcs_create[],
                  uint32_t pcr_nr_release, const uint8_t pcr_indcs_release[],
                  const tpm_pcr_value_t *pcr_values_release[],
                  uint32_t in_data_size, const uint8_t *in_data,
                  uint32_t *sealed_data_size, uint8_t *sealed_data);

/*
 * tpm_unseal unseal given data (sealed_data[sealed_data_size]) and return the
 * unsealed data in the given buffer (secret[*secret_size]).
 *
 * locality     : TPM locality (0 - 4)
 * sealed_data_size
 *              : the size of data to be unsealed.
 * sealed_data  : the data to be unsealed.
 * secret_size  : [in] the output buffer size.
 *                [out] the size of unsealed data
 * secret       : [out]unsealed data.
 * return       : TPM_SUCCESS for success, error code defined as TPM_xxx
 */
extern uint32_t tpm_unseal(
                  uint32_t locality,
                  uint32_t sealed_data_size, const uint8_t *sealed_data,
                  uint32_t *secret_size, uint8_t *secret);

/*
 * tpm_cmp_creation_pcrs compare the current values of specified PCRs with
 * the values of the creation PCRs in the sealed data
 *
 * return       : true if they match, false if they don't match
 */
extern bool tpm_cmp_creation_pcrs(
              uint32_t pcr_nr_create, const uint8_t pcr_indcs_create[],
              const tpm_pcr_value_t *pcr_values_create[],
              uint32_t sealed_data_size, uint8_t *sealed_data);

/*
 * tpm_get_nvindex_size use TPM_GETCAPABILITY cmd to  get the size of the NV
 * index given as index.
 *
 * return       : TPM_SUCCESS for success, error code defined as TPM_xxx
 */
extern uint32_t tpm_get_nvindex_size(uint32_t locality,
                                     tpm_nv_index_t index, uint32_t *size);

/*
 * tpm_save_state save all volatile state info into non-volatile memory.
 *
 * return       : TPM_SUCCESS for success, error code defined as TPM_xxx
 */
extern uint32_t tpm_save_state(uint32_t locality);


/*
 * tpm_get_random return TPM-generated random data.
 *
 * return       : TPM_SUCCESS for success, error code defined as TPM_xxx
 */
extern uint32_t tpm_get_random(uint32_t locality, uint8_t *random_data,
                               uint32_t *data_size);





/*
 * the following inline function reversely copy the bytes from 'in' to
 * 'out', the byte number to copy is given in count.
 */
#define reverse_copy(out, in, count) \
    _reverse_copy((uint8_t *)(out), (const uint8_t *)(in), count)

static inline void _reverse_copy(uint8_t *out, const uint8_t *in, uint32_t count)
{
    uint32_t i;    
    for ( i = 0; i < count; i++ )
        out[i] = in[count - i - 1];
}


/* un-comment to enable detailed command tracing */
#define noTPM_TRACE

/* ~5 secs are required for Infineon that requires this, so leave some extra */
#define MAX_SAVESTATE_RETRIES       60

#define TPM_TAG_RQU_COMMAND         0x00C1
#define TPM_TAG_RQU_AUTH1_COMMAND   0x00C2
#define TPM_TAG_RQU_AUTH2_COMMAND   0x00C3
#define TPM_ORD_PCR_EXTEND          0x00000014
#define TPM_ORD_PCR_READ            0x00000015
#define TPM_ORD_PCR_RESET           0x000000C8
#define TPM_ORD_NV_READ_VALUE       0x000000CF
#define TPM_ORD_NV_WRITE_VALUE      0x000000CD
#define TPM_ORD_GET_CAPABILITY      0x00000065
#define TPM_ORD_SEAL                0x00000017
#define TPM_ORD_UNSEAL              0x00000018
#define TPM_ORD_OSAP                0x0000000B
#define TPM_ORD_OIAP                0x0000000A
#define TPM_ORD_SAVE_STATE          0x00000098
#define TPM_ORD_GET_RANDOM          0x00000046

#define TPM_TAG_PCR_INFO_LONG       0x0006
#define TPM_TAG_STORED_DATA12       0x0016

//TPM data structures



#define CMD_HEAD_SIZE           10
#define RSP_HEAD_SIZE           10
#define CMD_SIZE_OFFSET         2
#define CMD_ORD_OFFSET          6
#define RSP_SIZE_OFFSET         2
#define RSP_RST_OFFSET          6


#define WRAPPER_IN_BUF          (cmd_buf + CMD_HEAD_SIZE)
#define WRAPPER_OUT_BUF         (rsp_buf + RSP_HEAD_SIZE)
#define WRAPPER_IN_MAX_SIZE     (TPM_CMD_SIZE_MAX - CMD_HEAD_SIZE)
#define WRAPPER_OUT_MAX_SIZE    (TPM_RSP_SIZE_MAX - RSP_HEAD_SIZE)

typedef struct __attribute__ ((packed)) {
    uint16_t    size_of_select;
    uint8_t     pcr_select[3];
} tpm_pcr_selection_t;


#define TPM_CAP_VERSION_VAL 0x1A

typedef uint16_t tpm_structure_tag_t;

typedef struct __attribute__ ((packed)) {
   uint8_t  major;
   uint8_t  minor;
   uint8_t  rev_major;
   uint8_t  rev_minor;
} tpm_version_t;

typedef struct __attribute__ ((packed)) {
    tpm_structure_tag_t tag;
    tpm_version_t       version;
    uint16_t            specLevel;
    uint8_t             errataRev;
    uint8_t             tpmVendorID[4];
    uint16_t            vendorSpecificSize;
    uint8_t             vendorSpecific[];
} tpm_cap_version_info_t;


#define HMAC_BLOCK_SIZE     64
#define HMAC_OUTPUT_SIZE    20


typedef uint16_t tpm_entity_type_t;
typedef uint32_t tpm_authhandle_t;
typedef struct __attribute__ ((packed)) {
    uint8_t     nonce[20];
} tpm_nonce_t;

#define TPM_ET_SRK              0x0004
#define TPM_KH_SRK              0x40000000

typedef uint32_t tpm_key_handle_t;

typedef tpm_digest_t tpm_composite_hash_t;
typedef struct __attribute__ ((packed)) {
    tpm_structure_tag_t         tag;
    tpm_locality_selection_t    locality_at_creation;
    tpm_locality_selection_t    locality_at_release;
    tpm_pcr_selection_t         creation_pcr_selection;
    tpm_pcr_selection_t         release_pcr_selection;
    tpm_composite_hash_t        digest_at_creation;
    tpm_composite_hash_t        digest_at_release;
} tpm_pcr_info_long_t;

typedef uint8_t tpm_authdata_t[20];
typedef tpm_authdata_t tpm_encauth_t;

typedef struct __attribute__ ((packed)) {
    tpm_structure_tag_t         tag;
    tpm_entity_type_t           et;
    uint32_t                    seal_info_size;
} tpm_stored_data12_header_t;

typedef struct __attribute__ ((packed)) {
    tpm_stored_data12_header_t  header;
    uint32_t                    enc_data_size;
    uint8_t                     enc_data[];
} tpm_stored_data12_short_t;

typedef struct __attribute__ ((packed)) {
    tpm_stored_data12_header_t  header;
    tpm_pcr_info_long_t         seal_info;
    uint32_t                    enc_data_size;
    uint8_t                     enc_data[];
} tpm_stored_data12_t;

#define UNLOAD_INTEGER(buf, offset, var) {\
    reverse_copy(buf + offset, &(var), sizeof(var));\
    offset += sizeof(var);\
}

#define UNLOAD_BLOB(buf, offset, blob, size) {\
        memcpy(buf + offset, blob, size); \
    offset += size;\
}

#define UNLOAD_BLOB_TYPE(buf, offset, blob) \
    UNLOAD_BLOB(buf, offset, blob, sizeof(*(blob)))

#define UNLOAD_PCR_SELECTION(buf, offset, sel) {\
    UNLOAD_INTEGER(buf, offset, (sel)->size_of_select);\
    UNLOAD_BLOB(buf, offset, (sel)->pcr_select, (sel)->size_of_select);\
}

#define UNLOAD_PCR_INFO_SHORT(buf, offset, info) {\
    UNLOAD_PCR_SELECTION(buf, offset, &(info)->pcr_selection);\
    UNLOAD_BLOB_TYPE(buf, offset, &(info)->locality_at_release);\
    UNLOAD_BLOB_TYPE(buf, offset, &(info)->digest_at_release);\
}

#define UNLOAD_NV_ATTRIBUTES(buf, offset, attr) {\
    UNLOAD_INTEGER(buf, offset, (attr)->tag);\
    UNLOAD_INTEGER(buf, offset, (attr)->attributes);\
}

/* Single-byte values do not require reverse_copy(endianness n/a) */
#define UNLOAD_NV_DATA_PUBLIC(buf, offset, pub) {\
    UNLOAD_INTEGER(buf, offset, (pub)->tag);\
    UNLOAD_INTEGER(buf, offset, (pub)->nv_index);\
    UNLOAD_PCR_INFO_SHORT(buf, offset, &(pub)->pcr_info_read);\
    UNLOAD_PCR_INFO_SHORT(buf, offset, &(pub)->pcr_info_write);\
    UNLOAD_NV_ATTRIBUTES(buf, offset, &(pub)->permission);\
    *(buf + offset) = (pub)->b_read_st_clear; offset += 1;\
    *(buf + offset) = (pub)->b_write_st_clear; offset += 1;\
    *(buf + offset) = (pub)->b_write_define; offset += 1;\
    UNLOAD_INTEGER(buf, offset, (pub)->data_size);\
}

#define UNLOAD_PCR_INFO_LONG(buf, offset, info) {\
    UNLOAD_INTEGER(buf, offset, (info)->tag);\
    UNLOAD_BLOB_TYPE(buf, offset, &(info)->locality_at_creation);\
    UNLOAD_BLOB_TYPE(buf, offset, &(info)->locality_at_release);\
    UNLOAD_PCR_SELECTION(buf, offset, &(info)->creation_pcr_selection);\
    UNLOAD_PCR_SELECTION(buf, offset, &(info)->release_pcr_selection);\
    UNLOAD_BLOB_TYPE(buf, offset, &(info)->digest_at_creation);\
    UNLOAD_BLOB_TYPE(buf, offset, &(info)->digest_at_release);\
}

#define UNLOAD_STORED_DATA12(buf, offset, hdr) {\
   UNLOAD_INTEGER(buf, offset, ((const tpm_stored_data12_header_t *)(hdr))->tag);\
   UNLOAD_INTEGER(buf, offset, ((const tpm_stored_data12_header_t *)(hdr))->et);\
   UNLOAD_INTEGER(buf, offset,\
                  ((const tpm_stored_data12_header_t *)(hdr))->seal_info_size);\
   if ( ((const tpm_stored_data12_header_t *)(hdr))->seal_info_size == 0 ) {\
       UNLOAD_INTEGER(buf, offset,\
                      ((const tpm_stored_data12_short_t *)hdr)->enc_data_size);\
       UNLOAD_BLOB(buf, offset,\
                   ((const tpm_stored_data12_short_t *)hdr)->enc_data,\
                   ((const tpm_stored_data12_short_t *)hdr)->enc_data_size);\
   }\
   else {\
       UNLOAD_PCR_INFO_LONG(buf, offset,\
                            &((const tpm_stored_data12_t *)hdr)->seal_info);\
       UNLOAD_INTEGER(buf, offset,\
                      ((const tpm_stored_data12_t *)hdr)->enc_data_size);\
       UNLOAD_BLOB(buf, offset,\
                   ((const tpm_stored_data12_t *)hdr)->enc_data,\
                   ((const tpm_stored_data12_t *)hdr)->enc_data_size);\
   }\
}

#define LOAD_INTEGER(buf, offset, var) {\
    reverse_copy(&(var), buf + offset, sizeof(var));\
    offset += sizeof(var);\
}

#define LOAD_BLOB(buf, offset, blob, size) {\
    memcpy(blob, buf + offset, size);\
    offset += size;\
}

#define LOAD_BLOB_TYPE(buf, offset, blob) \
    LOAD_BLOB(buf, offset, blob, sizeof(*(blob)))

#define LOAD_PCR_SELECTION(buf, offset, sel) {\
    LOAD_INTEGER(buf, offset, (sel)->size_of_select);\
    LOAD_BLOB(buf, offset, (sel)->pcr_select, (sel)->size_of_select);\
}

#define LOAD_PCR_INFO_SHORT(buf, offset, info) {\
    LOAD_PCR_SELECTION(buf, offset, &(info)->pcr_selection);\
    LOAD_BLOB_TYPE(buf, offset, &(info)->locality_at_release);\
    LOAD_BLOB_TYPE(buf, offset, &(info)->digest_at_release);\
}

#define LOAD_NV_ATTRIBUTES(buf, offset, attr) {\
    LOAD_INTEGER(buf, offset, (attr)->tag);\
    LOAD_INTEGER(buf, offset, (attr)->attributes);\
}

/* Single-byte values do not require reverse_copy(endianness n/a) */
#define LOAD_NV_DATA_PUBLIC(buf, offset, pub) {\
    LOAD_INTEGER(buf, offset, (pub)->tag);\
    LOAD_INTEGER(buf, offset, (pub)->nv_index);\
    LOAD_PCR_INFO_SHORT(buf, offset, &(pub)->pcr_info_read);\
    LOAD_PCR_INFO_SHORT(buf, offset, &(pub)->pcr_info_write);\
    LOAD_NV_ATTRIBUTES(buf, offset, &(pub)->permission);\
    (pub)->b_read_st_clear = *(buf + offset); offset += 1;\
    (pub)->b_write_st_clear = *(buf + offset); offset += 1;\
    (pub)->b_write_define = *(buf + offset); offset += 1;\
    LOAD_INTEGER(buf, offset, (pub)->data_size);\
}

#define LOAD_PCR_INFO_LONG(buf, offset, info) {\
    LOAD_INTEGER(buf, offset, (info)->tag);\
    LOAD_BLOB_TYPE(buf, offset, &(info)->locality_at_creation);\
    LOAD_BLOB_TYPE(buf, offset, &(info)->locality_at_release);\
    LOAD_PCR_SELECTION(buf, offset, &(info)->creation_pcr_selection);\
    LOAD_PCR_SELECTION(buf, offset, &(info)->release_pcr_selection);\
    LOAD_BLOB_TYPE(buf, offset, &(info)->digest_at_creation);\
    LOAD_BLOB_TYPE(buf, offset, &(info)->digest_at_release);\
}

#define LOAD_STORED_DATA12(buf, offset, hdr) {\
   LOAD_INTEGER(buf, offset, ((tpm_stored_data12_header_t *)(hdr))->tag);\
   LOAD_INTEGER(buf, offset, ((tpm_stored_data12_header_t *)(hdr))->et);\
   LOAD_INTEGER(buf, offset, \
                ((tpm_stored_data12_header_t *)(hdr))->seal_info_size);\
   if ( ((tpm_stored_data12_header_t *)(hdr))->seal_info_size == 0 ) {\
       LOAD_INTEGER(buf, offset,\
                    ((tpm_stored_data12_short_t *)hdr)->enc_data_size);\
       LOAD_BLOB(buf, offset,\
                 ((tpm_stored_data12_short_t *)hdr)->enc_data,\
                 ((tpm_stored_data12_short_t *)hdr)->enc_data_size);\
   }\
   else {\
       LOAD_PCR_INFO_LONG(buf, offset,\
                          &((tpm_stored_data12_t *)hdr)->seal_info);\
       LOAD_INTEGER(buf, offset,\
                    ((tpm_stored_data12_t *)hdr)->enc_data_size);\
       LOAD_BLOB(buf, offset,\
                 ((tpm_stored_data12_t *)hdr)->enc_data,\
                 ((tpm_stored_data12_t *)hdr)->enc_data_size);\
   }\
}


#define XOR_BLOB_TYPE(data, pad) {\
    uint32_t i;                                 \
    for ( i = 0; i < sizeof(*(data)); i++ ) \
        ((uint8_t *)data)[i] ^= ((uint8_t *)pad)[i % sizeof(*(pad))];\
}


typedef uint32_t tpm_capability_area_t;

#define TPM_CAP_NV_INDEX    0x00000011


typedef struct __attribute__ ((packed)) {
    tpm_pcr_selection_t         pcr_selection;
    tpm_locality_selection_t    locality_at_release;
    tpm_composite_hash_t        digest_at_release;
} tpm_pcr_info_short_t;

typedef struct __attribute__ ((packed)) {
    tpm_structure_tag_t tag;
    uint32_t            attributes;
} tpm_nv_attributes_t;

typedef struct __attribute__ ((packed)) {
    tpm_structure_tag_t     tag;
    tpm_nv_index_t          nv_index;
    tpm_pcr_info_short_t    pcr_info_read;
    tpm_pcr_info_short_t    pcr_info_write;
    tpm_nv_attributes_t     permission;
    uint8_t                 b_read_st_clear;
    uint8_t                 b_write_st_clear;
    uint8_t                 b_write_define;
    uint32_t                data_size;
} tpm_nv_data_public_t;



typedef struct __attribute__ ((packed)) {
    tpm_structure_tag_t tag;
    uint8_t disable;
    uint8_t ownership;
    uint8_t deactivated;
    uint8_t read_pubek;
    uint8_t disable_owner_clear;
    uint8_t allow_maintenance;
    uint8_t physical_presence_lifetime_lock;
    uint8_t physical_presence_hw_enable;
    uint8_t physical_presence_cmd_enable;
    uint8_t cekp_used;
    uint8_t tpm_post;
    uint8_t tpm_post_lock;
    uint8_t fips;
    uint8_t operator;
    uint8_t enable_revoke_ek;
    uint8_t nv_locked;
    uint8_t read_srk_pub;
    uint8_t tpm_established;
    uint8_t maintenance_done;
    uint8_t disable_full_da_logic_info;
} tpm_permanent_flags_t;

typedef struct __attribute__ ((packed)) {
    tpm_structure_tag_t tag;
    uint8_t deactivated;
    uint8_t disable_force_clear;
    uint8_t physical_presence;
    uint8_t phycical_presence_lock;
    uint8_t b_global_lock;
} tpm_stclear_flags_t;

#define TPM_CAP_FLAG            0x00000004
#define TPM_CAP_FLAG_PERMANENT  0x00000108
#define TPM_CAP_FLAG_VOLATILE   0x00000109


#define TPM_CAP_PROPERTY          0x00000005
#define TPM_CAP_PROP_TIS_TIMEOUT  0x00000115


/*
 * tpm_get_nv_data_public uses TPM_GETCAPABILITY cmd to get the public
 * data associated with the NV given index.
 *
 * return       : TPM_SUCCESS for success, error code defined as TPM_xxx
 */
extern uint32_t tpm_get_nv_data_public(uint32_t locality,
                                       tpm_nv_index_t index,
                                       tpm_nv_data_public_t *pub);

/* Functions newly required to be extern since they can be referenced
 * from tpm_extra.c as well. */
extern uint32_t _tpm_submit_cmd(uint32_t locality, uint16_t tag, uint32_t cmd,
                                uint32_t arg_size, uint32_t *out_size);

extern uint32_t tpm_submit_cmd(uint32_t locality, uint32_t cmd,
                               uint32_t arg_size, uint32_t *out_size);
extern uint32_t tpm_get_capability(
                  uint32_t locality, tpm_capability_area_t cap_area,
                  uint32_t sub_cap_size, const uint8_t *sub_cap,
                  uint32_t *resp_size, uint8_t *resp);

#endif // __ASSEMBLY__


#endif   /* __TPM_H__ */

/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
