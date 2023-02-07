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

// EMHF TPM component
// x86 arch. specific declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHF_TPM_ARCH_X86_H__
#define __XMHF_TPM_ARCH_X86_H__



#ifndef __ASSEMBLY__


//from libtpm/tpm.h


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

    /* static */
static     uint8_t     cmd_buf[TPM_CMD_SIZE_MAX];
    /* static */
static     uint8_t     rsp_buf[TPM_RSP_SIZE_MAX];

#define TPM_NR_PCRS             24


/* PCRs lower than 16 are not resetable */
#define TPM_PCR_RESETABLE_MIN           16


#define TPM_NV_READ_VALUE_DATA_SIZE_MAX  (TPM_RSP_SIZE_MAX - 14)

typedef uint32_t tpm_nv_index_t;


#define TPM_NV_WRITE_VALUE_DATA_SIZE_MAX (TPM_CMD_SIZE_MAX - 22)


typedef uint8_t tpm_locality_selection_t;
#define TPM_LOC_ZERO    0x01
#define TPM_LOC_ONE     0x02
#define TPM_LOC_TWO     0x04
#define TPM_LOC_THREE   0x08
#define TPM_LOC_FOUR    0x10
#define TPM_LOC_RSVD    0xE0



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

//----------------------------------------------------------------------
//exported FUNCTIONS
//----------------------------------------------------------------------

//open TPM locality
int xmhf_tpm_open_locality(int locality);

//check if TPM is ready for use
bool xmhf_tpm_is_tpm_ready(uint32_t locality);

//deactivate all TPM localities
void xmhf_tpm_deactivate_all_localities(void);

//prepare TPM for use
bool xmhf_tpm_prepare_tpm(void);

//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------
//open TPM locality
int xmhf_tpm_arch_open_locality(int locality);

//check if TPM is ready for use
bool xmhf_tpm_arch_is_tpm_ready(uint32_t locality);

//deactivate all TPM localities
void xmhf_tpm_arch_deactivate_all_localities(void);

//prepare TPM for use
bool xmhf_tpm_arch_prepare_tpm(void);
*/


//----------------------------------------------------------------------
//x86 ARCH. INTERFACES
//----------------------------------------------------------------------
#define TPM_LOCALITY_BASE             0xfed40000
#define NR_TPM_LOCALITY_PAGES         ((TPM_LOCALITY_1 - TPM_LOCALITY_0) >> \
                                       PAGE_SHIFT)

#define TPM_LOCALITY_0                TPM_LOCALITY_BASE
#define TPM_LOCALITY_1                (TPM_LOCALITY_BASE | 0x1000)
#define TPM_LOCALITY_2                (TPM_LOCALITY_BASE | 0x2000)
/* these localities (3+4) are mostly not usable by Xen */
#define TPM_LOCALITY_3                (TPM_LOCALITY_BASE | 0x3000)
#define TPM_LOCALITY_4                (TPM_LOCALITY_BASE | 0x4000)

#define TPM_LOCALITY_BASE_N(n)        (TPM_LOCALITY_BASE | ((n) << 12))



#define TPM_VALIDATE_LOCALITY_TIME_OUT  0x100

/*
 * TPM registers and data structures
 *
 * register values are offsets from each locality base
 * see {read,write}_tpm_reg() for data struct format
 */

/* TPM_ACCESS_x */
#define TPM_REG_ACCESS           0x00
#define SIZE_TPM_REG_ACCESS      0x1

typedef struct {
    uint32_t tpm_establishment   ; //: 1;  //  RO, 0=T/OS has been established
                                 //   before
    uint32_t request_use         ; //: 1;  //  RW, 1=locality is requesting TPM use
    uint32_t pending_request     ; //: 1;  //  RO, 1=other locality is requesting
                                 //   TPM usage
    uint32_t seize               ; //: 1;  //  WO, 1=seize locality
    uint32_t been_seized         ; //: 1;  //  RW, 1=locality seized while active
    uint32_t active_locality     ; //: 1;  //  RW, 1=locality is active
    uint32_t reserved            ; //: 1;  //
    uint32_t tpm_reg_valid_sts   ; //: 1;  //  RO, 1=other bits are valid
} __attribute__((packed)) tpm_reg_access_t;

#define pack_tpm_reg_access_t(s) \
    (uint8_t)( \
    (((uint32_t)(s)->tpm_reg_valid_sts    & 0x00000001UL) << 7) | \
    (((uint32_t)(s)->reserved             & 0x00000001UL) << 6) | \
    (((uint32_t)(s)->active_locality      & 0x00000001UL) << 5) | \
    (((uint32_t)(s)->been_seized          & 0x00000001UL) << 4) | \
    (((uint32_t)(s)->seize                & 0x00000001UL) << 3) | \
    (((uint32_t)(s)->pending_request      & 0x00000001UL) << 2) | \
    (((uint32_t)(s)->request_use          & 0x00000001UL) << 1) | \
    (((uint32_t)(s)->tpm_establishment    & 0x00000001UL) << 0 ) \
    )

#define unpack_tpm_reg_access_t(s, value) \
    (s)->tpm_reg_valid_sts      = (uint32_t)(((uint8_t)value >> 7) & 0x00000001UL); \
    (s)->reserved               = (uint32_t)(((uint8_t)value >> 6) & 0x00000001UL); \
    (s)->active_locality        = (uint32_t)(((uint8_t)value >> 5) & 0x00000001UL); \
    (s)->been_seized            = (uint32_t)(((uint8_t)value >> 4) & 0x00000001UL); \
    (s)->seize                  = (uint32_t)(((uint8_t)value >> 3) & 0x00000001UL); \
    (s)->pending_request        = (uint32_t)(((uint8_t)value >> 2) & 0x00000001UL); \
    (s)->request_use            = (uint32_t)(((uint8_t)value >> 1) & 0x00000001UL); \
    (s)->tpm_establishment      = (uint32_t)(((uint8_t)value >> 0) & 0x00000001UL);



/* TPM_STS_x */
#define TPM_REG_STS              0x18
#define SIZE_TPM_REG_STS         0x3
/*typedef struct {
        uint8_t reserved1       : 1;
        uint8_t response_retry  : 1;  // WO, 1=re-send response
        uint8_t reserved2       : 1;
        uint8_t expect          : 1;  // RO, 1=more data for command expected
        uint8_t data_avail      : 1;  // RO, 0=no more data for response
        uint8_t tpm_go          : 1;  // WO, 1=execute sent command
        uint8_t command_ready   : 1;  // RW, 1=TPM ready to receive new cmd
        uint8_t sts_valid       : 1;  // RO, 1=data_avail and expect bits are
                                 //   valid
        uint16_t burst_count    : 16; // RO, # read/writes bytes before wait
} __attribute__((packed)) tpm_reg_sts_t;
*/

typedef struct {
        uint32_t reserved1       ;//: 1;
        uint32_t response_retry  ;//: 1;  // WO, 1=re-send response
        uint32_t reserved2       ;//: 1;
        uint32_t expect          ;//: 1;  // RO, 1=more data for command expected
        uint32_t data_avail      ;//: 1;  // RO, 0=no more data for response
        uint32_t tpm_go          ;//: 1;  // WO, 1=execute sent command
        uint32_t command_ready   ;//: 1;  // RW, 1=TPM ready to receive new cmd
        uint32_t sts_valid       ;//: 1;  // RO, 1=data_avail and expect bits are
                                 //   valid
        uint32_t burst_count     ;//: 16; // RO, # read/writes bytes before wait
} __attribute__((packed)) tpm_reg_sts_t;

#define pack_tpm_reg_sts_t(s) \
    (uint32_t)( \
    (((uint32_t)(s)->burst_count     & 0x0000FFFFUL) << 8) | \
    (((uint32_t)(s)->sts_valid       & 0x00000001UL) << 7) | \
    (((uint32_t)(s)->command_ready   & 0x00000001UL) << 6) | \
    (((uint32_t)(s)->tpm_go          & 0x00000001UL) << 5) | \
    (((uint32_t)(s)->data_avail      & 0x00000001UL) << 4) | \
    (((uint32_t)(s)->expect          & 0x00000001UL) << 3) | \
    (((uint32_t)(s)->reserved2       & 0x00000001UL) << 2) | \
    (((uint32_t)(s)->response_retry  & 0x00000001UL) << 1) | \
    (((uint32_t)(s)->reserved1       & 0x00000001UL) << 0 ) \
    )

#define unpack_tpm_reg_sts_t(s, value) \
     (s)->burst_count       = (uint32_t)(((uint32_t)value >> 8) & 0x0000FFFFUL); \
     (s)->sts_valid         = (uint32_t)(((uint32_t)value >> 7) & 0x00000001UL); \
     (s)->command_ready     = (uint32_t)(((uint32_t)value >> 6) & 0x00000001UL); \
     (s)->tpm_go            = (uint32_t)(((uint32_t)value >> 5) & 0x00000001UL); \
     (s)->data_avail        = (uint32_t)(((uint32_t)value >> 4) & 0x00000001UL); \
     (s)->expect            = (uint32_t)(((uint32_t)value >> 3) & 0x00000001UL); \
     (s)->reserved2         = (uint32_t)(((uint32_t)value >> 2) & 0x00000001UL); \
     (s)->response_retry    = (uint32_t)(((uint32_t)value >> 1) & 0x00000001UL); \
     (s)->reserved1         = (uint32_t)(((uint32_t)value >> 0) & 0x00000001UL);



/* TPM_DATA_FIFO_x */
#define TPM_REG_DATA_FIFO        0x24
#define SIZE_TPM_REG_DATA_FIFO   0x1
//typedef union {
//        uint8_t _raw[1];                      /* 1-byte reg */
//} tpm_reg_data_fifo_t;

typedef uint8_t tpm_reg_data_fifo_t;
/*
 * assumes that all reg types follow above format:
 *   - packed
 *   - member named '_raw' which is array whose size is that of data to read
 */
#define read_tpm_reg(locality, reg, pdata)      \
    _read_tpm_reg(locality, reg, (pdata)->_raw, sizeof(*(pdata)))

#define write_tpm_reg(locality, reg, pdata)     \
    _write_tpm_reg(locality, reg, (pdata)->_raw, sizeof(*(pdata)))


/*********************************************************************
 * Moved in from tboot's tpm.c; I think it belongs in a .h file. Also
 * facilitates split into tpm.c and tpm_extra.c.
 *********************************************************************/

/* TODO: Give these a more appropriate home */
#define readb(va)       xmhfhw_sysmemaccess_readu8(va)
#define writeb(va, d)   xmhfhw_sysmemaccess_writeu8(va, d)

/*#ifndef __XMHF_VERIFICATION__

	static inline void writeb(uint32_t addr, uint8_t val) {
	    __asm__ __volatile__("movb %%al, %%fs:(%%ebx)\r\n"
				 :
				 : "b"(addr), "a"((uint32_t)val)
				 );
	}

	static inline uint8_t readb(uint32_t addr) {
	    uint32_t ret;
	    __asm__ __volatile("xor %%eax, %%eax\r\n"
			       "movb %%fs:(%%ebx), %%al\r\n"
			       : "=a"(ret)
			       : "b"(addr)
			       );
	    return (uint8_t)ret;
	}

#else //__XMHF_VERIFICATION__

	static inline void writeb(uint32_t addr, uint8_t val) {

	}

	static inline uint8_t readb(uint32_t addr) {
	 return 0;
	}

#endif //__XMHF_VERIFICATION__
*/

//TPM timeouts
#define TIMEOUT_UNIT    (0x100000 / 330) /* ~1ms, 1 tpm r/w need > 330ns */
#define TIMEOUT_A       750  /* 750ms */
#define TIMEOUT_B       2000 /* 2s */
#define TIMEOUT_C       750  /* 750ms */
#define TIMEOUT_D       750  /* 750ms */

typedef struct __attribute__ ((packed)) {
    uint32_t timeout_a;
    uint32_t timeout_b;
    uint32_t timeout_c;
    uint32_t timeout_d;
} tpm_timeout_t;


#define TPM_ACTIVE_LOCALITY_TIME_OUT    \
          (TIMEOUT_UNIT * g_timeout.timeout_a)  /* according to spec */
#define TPM_CMD_READY_TIME_OUT          \
          (TIMEOUT_UNIT * g_timeout.timeout_b)  /* according to spec */
#define TPM_CMD_WRITE_TIME_OUT          \
          (TIMEOUT_UNIT * g_timeout.timeout_d)  /* let it long enough */
#define TPM_DATA_AVAIL_TIME_OUT         \
          (TIMEOUT_UNIT * g_timeout.timeout_c)  /* let it long enough */
#define TPM_RSP_READ_TIME_OUT           \
          (TIMEOUT_UNIT * g_timeout.timeout_d)  /* let it long enough */

/*
//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------
//open TPM locality
int xmhf_tpm_arch_x86vmx_open_locality(int locality);


//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------
//open TPM locality
int xmhf_tpm_arch_x86svm_open_locality(int locality);

*/

static inline uint32_t tpm_get_capability(
                  uint32_t locality, tpm_capability_area_t cap_area,
                  uint32_t sub_cap_size, const uint8_t *sub_cap,
                  uint32_t *resp_size, uint8_t *resp);








static inline void _read_tpm_reg(int locality, uint32_t reg, uint8_t *_raw, size_t size)
{
    size_t i;
    for ( i = 0; i < size; i++ )
        _raw[i] = readb((TPM_LOCALITY_BASE_N(locality) | reg) + i);
}

static inline void _write_tpm_reg(int locality, uint32_t reg, uint8_t *_raw, size_t size)
{
    size_t i;
    for ( i = 0; i < size; i++ )
        writeb((TPM_LOCALITY_BASE_N(locality) | reg) + i, _raw[i]);
}


static tpm_timeout_t g_timeout = {TIMEOUT_A,
                                  TIMEOUT_B,
                                  TIMEOUT_C,
                                  TIMEOUT_D};

static inline bool tpm_validate_locality(uint32_t locality)
{
    uint32_t i;
    tpm_reg_access_t reg_acc;

    for ( i = TPM_VALIDATE_LOCALITY_TIME_OUT; i > 0; i-- ) {
        /*
         * TCG spec defines reg_acc.tpm_reg_valid_sts bit to indicate whether
         * other bits of access reg are valid.( but this bit will also be 1
         * while this locality is not available, so check seize bit too)
         * It also defines that reading reg_acc.seize should always return 0
         */
        {
            uint8_t value;
            _read_tpm_reg(locality, TPM_REG_ACCESS, &value, SIZE_TPM_REG_ACCESS);
            unpack_tpm_reg_access_t(&reg_acc, value);
        }
        if ( reg_acc.tpm_reg_valid_sts == 1 && reg_acc.seize == 0)
            return true;
        cpu_relax(CASM_NOPARAM);
    }

    //if ( i <= 0 )
        //_XDPRINTF_("\nTPM: tpm_validate_locality timeout\n");

    return false;
}

/*
static void dump_locality_access_regs(void) {
    tpm_reg_access_t reg_acc;
    uint32_t locality;

    _XDPRINTF_("\n%s():\n", __FUNCTION__);
    for(locality=0; locality <= 3; locality++) {
        read_tpm_reg(locality, TPM_REG_ACCESS, &reg_acc);
        _XDPRINTF_("  TPM: Locality %d Access reg content: 0x%02x\n",
               locality, (uint32_t)reg_acc._raw[0]);
        if ( reg_acc.tpm_reg_valid_sts == 0 ) {
            _XDPRINTF_("    TPM: Access reg not valid\n");
        }
    }
}*/



static inline uint32_t tpm_get_flags(uint32_t locality, uint32_t flag_id,
                       uint8_t *flags, uint32_t flag_size)
{
    uint32_t ret, offset, resp_size;
    uint8_t sub_cap[sizeof(flag_id)];
    tpm_structure_tag_t tag;

    if ( flags == NULL ) {
        //_XDPRINTF_("TPM: tpm_get_flags() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    offset = 0;
    UNLOAD_INTEGER(sub_cap, offset, flag_id);

    resp_size = flag_size;
    ret = tpm_get_capability(locality, TPM_CAP_FLAG, sizeof(sub_cap),
                             sub_cap, &resp_size, flags);

//#ifdef TPM_TRACE
//    _XDPRINTF_("TPM: get flags %08X, return value = %08X\n", flag_id, ret);
//#endif
    if ( ret != TPM_SUCCESS )
        return ret;

    /* 1.2 spec, main part 2, rev 103 add one more byte to permanent flags, to
       be backward compatible, not assume all expected bytes can be gotten */
    if ( resp_size > flag_size ) {
        //_XDPRINTF_("TPM: tpm_get_flags() response size too small\n");
        return TPM_FAIL;
    }

    offset = 0;
    LOAD_INTEGER(flags, offset, tag);
    offset = 0;
    UNLOAD_BLOB_TYPE(flags, offset, &tag);

    return ret;
}


static inline uint32_t tpm_get_timeout(uint32_t locality,
                       uint8_t *prop, uint32_t prop_size)
{
    uint32_t ret, offset, resp_size, prop_id = TPM_CAP_PROP_TIS_TIMEOUT;
    uint8_t sub_cap[sizeof(prop_id)];
    uint32_t resp[4];

    if ( (prop == NULL) || (prop_size < sizeof(resp)) ) {
        //_XDPRINTF_("TPM: tpm_get_timeout() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    offset = 0;
    UNLOAD_INTEGER(sub_cap, offset, prop_id);

    resp_size = prop_size;
    ret = tpm_get_capability(locality, TPM_CAP_PROPERTY, sizeof(sub_cap),
                             sub_cap, &resp_size, prop);

//#ifdef TPM_TRACE
//    _XDPRINTF_("TPM: get prop %08X, return value = %08X\n", prop_id, ret);
//#endif
    if ( ret != TPM_SUCCESS )
        return ret;

    if ( resp_size != prop_size ) {
        //_XDPRINTF_("TPM: tpm_get_property() response size incorrect\n");
        return TPM_FAIL;
    }

    offset = 0;
    LOAD_INTEGER(prop, offset, resp);
    offset = 0;
    UNLOAD_BLOB_TYPE(prop, offset, &resp);

    return ret;
}


/* ensure TPM is ready to accept commands */
static inline bool is_tpm_ready(uint32_t locality)
{
    tpm_permanent_flags_t pflags;
    tpm_stclear_flags_t vflags;
    uint32_t timeout[4];
    uint32_t ret;

    if ( !tpm_validate_locality(locality) ) {
        //_XDPRINTF_("TPM is not available.\n");
        return false;
    }

    /* make sure tpm is not disabled/deactivated */
    memset(&pflags, 0, sizeof(pflags));
    ret = tpm_get_flags(locality, TPM_CAP_FLAG_PERMANENT,
                        (uint8_t *)&pflags, sizeof(pflags));
    if ( ret != TPM_SUCCESS ) {
        //_XDPRINTF_("TPM is disabled or deactivated.\n");
        return false;
    }
    if ( pflags.disable ) {
        //_XDPRINTF_("TPM is disabled.\n");
        return false;
    }

    memset(&vflags, 0, sizeof(vflags));
    ret = tpm_get_flags(locality, TPM_CAP_FLAG_VOLATILE,
                        (uint8_t *)&vflags, sizeof(vflags));
    if ( ret != TPM_SUCCESS ) {
        //_XDPRINTF_("TPM is disabled or deactivated.\n");
        return false;
    }
    if ( vflags.deactivated ) {
        //_XDPRINTF_("TPM is deactivated.\n");
        return false;
    }

    //_XDPRINTF_("TPM is ready\n");
    //_XDPRINTF_("TPM nv_locked: %s\n", (pflags.nv_locked != 0) ? "TRUE" : "FALSE");

    /* get tpm timeout values */
    ret = tpm_get_timeout(locality, (uint8_t *)&timeout, sizeof(timeout));
    if ( ret != TPM_SUCCESS ){
        //_XDPRINTF_("TPM timeout values are not achieved, "
        //       "default values will be used.\n");
    }else {
        /*
         * timeout_x represents the number of milliseconds for the timeout
         * and timeout[x] represents the number of microseconds.
         */
        g_timeout.timeout_a = timeout[0]/1000;
        g_timeout.timeout_b = timeout[1]/1000;
        g_timeout.timeout_c = timeout[2]/1000;
        g_timeout.timeout_d = timeout[3]/1000;
        //_XDPRINTF_("TPM timeout values: A: %u, B: %u, C: %u, D: %u\n",
        //       g_timeout.timeout_a, g_timeout.timeout_b, g_timeout.timeout_c,
        //       g_timeout.timeout_d);
        /*
         * if any timeout values are less than default values, set to default
         * value (due to bug with some TPMs)
         */
        if ( g_timeout.timeout_a < TIMEOUT_A ) g_timeout.timeout_a = TIMEOUT_A;
        if ( g_timeout.timeout_b < TIMEOUT_B ) g_timeout.timeout_b = TIMEOUT_B;
        if ( g_timeout.timeout_c < TIMEOUT_C ) g_timeout.timeout_c = TIMEOUT_C;
        if ( g_timeout.timeout_d < TIMEOUT_D ) g_timeout.timeout_d = TIMEOUT_D;
    }

    return true;
}


static inline bool release_locality(uint32_t locality)
{
    uint32_t i;
    tpm_reg_access_t reg_acc;
//#ifdef TPM_TRACE
//    _XDPRINTF_("TPM: releasing locality %u\n", locality);
//#endif

    if ( !tpm_validate_locality(locality) )
        return true;

    {
        uint8_t value;
        _read_tpm_reg(locality, TPM_REG_ACCESS, &value, SIZE_TPM_REG_ACCESS);
        unpack_tpm_reg_access_t(&reg_acc, value);
    }

    if ( reg_acc.active_locality == 0 )
        return true;

    /* make inactive by writing a 1 */
    unpack_tpm_reg_access_t(&reg_acc, 0);
    //reg_acc._raw[0]= 0;
    //memset(&reg_acc, 0, SIZE_TPM_REG_ACCESS);
    reg_acc.active_locality = 1;

    {
        uint8_t value = pack_tpm_reg_access_t(&reg_acc);
        _write_tpm_reg(locality, TPM_REG_ACCESS, &value, SIZE_TPM_REG_ACCESS);
    }

    i = 0;
    do {
        {
            uint8_t value;
            _read_tpm_reg(locality, TPM_REG_ACCESS, &value, SIZE_TPM_REG_ACCESS);
            unpack_tpm_reg_access_t(&reg_acc, value);
        }
        if ( reg_acc.active_locality == 0 )
            return true;
        else
            cpu_relax(CASM_NOPARAM);
        i++;
    } while ( i <= TPM_ACTIVE_LOCALITY_TIME_OUT );

    //_XDPRINTF_("TPM: access reg release locality timeout\n");
    return false;
}

//======================================================================
//ARCH. Backends
//======================================================================

//deactivate all TPM localities
static inline void xmhf_tpm_arch_deactivate_all_localities(void) {
    tpm_reg_access_t reg_acc;
    uint32_t locality;

    //_XDPRINTF_("\nTPM: %s()\n", __FUNCTION__);
    for(locality=0; locality <= 3; locality++) {
        unpack_tpm_reg_access_t(&reg_acc, 0);
        reg_acc.active_locality = 1;
        {
            uint8_t value = pack_tpm_reg_access_t(&reg_acc);
            _write_tpm_reg(locality, TPM_REG_ACCESS, &value, SIZE_TPM_REG_ACCESS);
        }
    }
}


//check if TPM is ready for use
static inline bool xmhf_tpm_arch_is_tpm_ready(uint32_t locality){
	return is_tpm_ready(locality);
}



//prepare TPM for use
static inline bool xmhf_tpm_arch_prepare_tpm(void){
    /*
     * must ensure TPM_ACCESS_0.activeLocality bit is clear
     * (: locality is not active)
     */

    return release_locality(0);
}



//======================================================================
// libtpm environment specific function definitions
//======================================================================


static inline uint32_t tpm_wait_cmd_ready(uint32_t locality)
{
    uint32_t            i;
    tpm_reg_access_t    reg_acc;
    tpm_reg_sts_t       reg_sts;

/*     //temporary debug prints */
/*     dump_locality_access_regs(); */
/*     deactivate_all_localities(); */
/*     dump_locality_access_regs(); */

    /* ensure the contents of the ACCESS register are valid */
    {
        uint8_t value;
        _read_tpm_reg(locality, TPM_REG_ACCESS, &value, SIZE_TPM_REG_ACCESS);
        unpack_tpm_reg_access_t(&reg_acc, value);
    }
//#ifdef TPM_TRACE
//    _XDPRINTF_("\nTPM: Access reg content: 0x%02x\n", (uint32_t)reg_acc._raw[0]);
//#endif
    if ( reg_acc.tpm_reg_valid_sts == 0 ) {
        //_XDPRINTF_("TPM: Access reg not valid\n");
        return TPM_FAIL;
    }

    /* request access to the TPM from locality N */
    unpack_tpm_reg_access_t(&reg_acc, 0);
    //memset(&reg_acc, 0, SIZE_TPM_REG_ACCESS);
    reg_acc.request_use = 1;

    {
        uint8_t value = pack_tpm_reg_access_t(&reg_acc);
        _write_tpm_reg(locality, TPM_REG_ACCESS, &value, SIZE_TPM_REG_ACCESS);
    }
    i = 0;
    do {
        {
            uint8_t value;
            _read_tpm_reg(locality, TPM_REG_ACCESS, &value, SIZE_TPM_REG_ACCESS);
            unpack_tpm_reg_access_t(&reg_acc, value);
        }
        if ( reg_acc.active_locality == 1 )
            break;
        else
            cpu_relax(CASM_NOPARAM);
        i++;
    } while ( i <= TPM_ACTIVE_LOCALITY_TIME_OUT);

    if ( i > TPM_ACTIVE_LOCALITY_TIME_OUT ) {
        //_XDPRINTF_("TPM: access reg request use timeout (i=%d)\n", i);
        return TPM_FAIL;
    }

    /* ensure the TPM is ready to accept a command */
//#ifdef TPM_TRACE
//    _XDPRINTF_("TPM: wait for cmd ready ");
//#endif
    i = 0;
    do {
        /* write 1 to TPM_STS_x.commandReady to let TPM enter ready state */
        memset((void *)&reg_sts, 0, sizeof(reg_sts));
        reg_sts.command_ready = 1;
        {
            uint32_t value = pack_tpm_reg_sts_t(&reg_sts);
            _write_tpm_reg(locality, TPM_REG_STS, &value, SIZE_TPM_REG_STS);
        }
        cpu_relax(CASM_NOPARAM);

        /* then see if it has */
        {
            uint32_t value;
            _read_tpm_reg(locality, TPM_REG_STS, &value, SIZE_TPM_REG_STS);
            unpack_tpm_reg_sts_t(&reg_sts, value);
        }
//#ifdef TPM_TRACE
//        _XDPRINTF_(".");
//#endif
        if ( reg_sts.command_ready == 1 )
            break;
        else
            cpu_relax(CASM_NOPARAM);
        i++;
    } while ( i <= TPM_CMD_READY_TIME_OUT );
//#ifdef TPM_TRACE
//    _XDPRINTF_("\n");
//#endif

    if ( i > TPM_CMD_READY_TIME_OUT ) {
        //_XDPRINTF_("TPM: status reg content: %02x %02x %02x\n",
        //       (uint32_t)reg_sts._raw[0],
        //       (uint32_t)reg_sts._raw[1],
        //       (uint32_t)reg_sts._raw[2]);
        //_XDPRINTF_("TPM: tpm timeout for command_ready\n");
        goto RelinquishControl;
    }
    return TPM_SUCCESS;

RelinquishControl:
    /* deactivate current locality */
    unpack_tpm_reg_access_t(&reg_acc, 0);
    reg_acc.active_locality = 1;
    {
        uint8_t value = pack_tpm_reg_access_t(&reg_acc);
        _write_tpm_reg(locality, TPM_REG_ACCESS, &value, SIZE_TPM_REG_ACCESS);
    }

    return TPM_FAIL;
}

/*
 *   locality : TPM locality (0 - 3)
 *   in       : All bytes for a single TPM command, including TAG, SIZE,
 *              ORDINAL, and other arguments. All data should be in big-endian
 *              style. The in MUST NOT be NULL, containing at least 10 bytes.
 *              0   1   2   3   4   5   6   7   8   9   10  ...
 *              -------------------------------------------------------------
 *              | TAG  |     SIZE      |    ORDINAL    |    arguments ...
 *              -------------------------------------------------------------
 *   in_size  : The size of the whole command contained within the in buffer.
 *              It should equal to the SIZE contained in the in buffer.
 *   out      : All bytes of the TPM response to a single command. All data
 *              within it will be in big-endian style. The out MUST not be
 *              NULL, and will return at least 10 bytes.
 *              0   1   2   3   4   5   6   7   8   9   10  ...
 *              -------------------------------------------------------------
 *              | TAG  |     SIZE      |  RETURN CODE  |    other data ...
 *              -------------------------------------------------------------
 *   out_size : In/out paramter. As in, it is the size of the out buffer;
 *              as out, it is the size of the response within the out buffer.
 *              The out_size MUST NOT be NULL.
 *   return   : 0 = success; if not 0, it equal to the RETURN CODE in out buf.
 */

static inline uint32_t tpm_write_cmd_fifo(uint32_t locality, uint8_t *in,
                                   uint32_t in_size, uint8_t *out,
                                   uint32_t *out_size)
{
    uint32_t            i, rsp_size, offset, ret;
    uint16_t            row_size;
    tpm_reg_access_t    reg_acc;
    tpm_reg_sts_t       reg_sts;

    if ( locality >= TPM_NR_LOCALITIES ) {
        //_XDPRINTF_("TPM: Invalid locality for tpm_write_cmd_fifo()\n");
        return TPM_BAD_PARAMETER;
    }
    if ( in == NULL || out == NULL || out_size == NULL ) {
        //_XDPRINTF_("TPM: Invalid parameter for tpm_write_cmd_fifo()\n");
        return TPM_BAD_PARAMETER;
    }
    if ( in_size < CMD_HEAD_SIZE || *out_size < RSP_HEAD_SIZE ) {
        //_XDPRINTF_("TPM: in/out buf size must be larger than 10 bytes\n");
        return TPM_BAD_PARAMETER;
    }

    if ( !tpm_validate_locality(locality) ) {
        //_XDPRINTF_("TPM: Locality %d is not open\n", locality);
        return TPM_FAIL;
    }

    ret = tpm_wait_cmd_ready(locality);
    if ( ret != TPM_SUCCESS )
        return ret;

//#ifdef TPM_TRACE
//    {
//        _XDPRINTF_("TPM: cmd size = %d\nTPM: cmd content: ", in_size);
//        print_hex("TPM: \t", in, in_size);
//    }
//#endif

    /* write the command to the TPM FIFO */
    offset = 0;
    do {
        i = 0;
        do {
            {
                uint32_t value;
                _read_tpm_reg(locality, TPM_REG_STS, &value, SIZE_TPM_REG_STS);
                unpack_tpm_reg_sts_t(&reg_sts, value);
            }
            /* find out how many bytes the TPM can accept in a row */
            row_size = reg_sts.burst_count;
            if ( row_size > 0 )
                break;
            else
                cpu_relax(CASM_NOPARAM);
            i++;
        } while ( i <= TPM_CMD_WRITE_TIME_OUT );
        if ( i > TPM_CMD_WRITE_TIME_OUT ) {
            //_XDPRINTF_("TPM: write cmd timeout\n");
            ret = TPM_FAIL;
            goto RelinquishControl;
        }

        for ( ; row_size > 0 && offset < in_size; row_size--, offset++ )
            _write_tpm_reg(locality, TPM_REG_DATA_FIFO,
                          (tpm_reg_data_fifo_t *)&in[offset], SIZE_TPM_REG_DATA_FIFO);
    } while ( offset < in_size );

    /* command has been written to the TPM, it is time to execute it. */
    memset(&reg_sts, 0,  sizeof(reg_sts));
    reg_sts.tpm_go = 1;
    {
        uint32_t value = pack_tpm_reg_sts_t(&reg_sts);
        _write_tpm_reg(locality, TPM_REG_STS, &value, SIZE_TPM_REG_STS);
    }
    /* check for data available */
    i = 0;
    do {
        {
            uint32_t value;
            _read_tpm_reg(locality,TPM_REG_STS, &value, SIZE_TPM_REG_STS);
            unpack_tpm_reg_sts_t(&reg_sts, value);
        }
        if ( reg_sts.sts_valid == 1 && reg_sts.data_avail == 1 )
            break;
        else
            cpu_relax(CASM_NOPARAM);
        i++;
    } while ( i <= TPM_DATA_AVAIL_TIME_OUT );
    if ( i > TPM_DATA_AVAIL_TIME_OUT ) {
        //_XDPRINTF_("TPM: wait for data available timeout\n");
        ret = TPM_FAIL;
        goto RelinquishControl;
    }

    rsp_size = 0;
    offset = 0;
    do {
        /* find out how many bytes the TPM returned in a row */
        i = 0;
        do {
            {
                uint32_t value;
                _read_tpm_reg(locality,TPM_REG_STS, &value, SIZE_TPM_REG_STS);
                unpack_tpm_reg_sts_t(&reg_sts, value);
            }
            row_size = reg_sts.burst_count;
            if ( row_size > 0 )
                break;
            else
                cpu_relax(CASM_NOPARAM);
            i++;
        } while ( i <= TPM_RSP_READ_TIME_OUT );
        if ( i > TPM_RSP_READ_TIME_OUT ) {
            //_XDPRINTF_("TPM: read rsp timeout\n");
            ret = TPM_FAIL;
            goto RelinquishControl;
        }

        for ( ; row_size > 0 && offset < *out_size; row_size--, offset++ ) {
            if ( offset < *out_size )
                _read_tpm_reg(locality, TPM_REG_DATA_FIFO,
                             (tpm_reg_data_fifo_t *)&out[offset], SIZE_TPM_REG_DATA_FIFO);
            else {
                /* discard the responded bytes exceeding out buf size */
                tpm_reg_data_fifo_t discard;
                _read_tpm_reg(locality, TPM_REG_DATA_FIFO,
                             (tpm_reg_data_fifo_t *)&discard, SIZE_TPM_REG_DATA_FIFO);
            }

            /* get outgoing data size */
            if ( offset == RSP_RST_OFFSET - 1 ) {
                reverse_copy(&rsp_size, &out[RSP_SIZE_OFFSET],
                             sizeof(rsp_size));
            }
        }
    } while ( offset < RSP_RST_OFFSET ||
              (offset < rsp_size && offset < *out_size) );

    *out_size = (*out_size > rsp_size) ? rsp_size : *out_size;

    /* out buffer contains the complete outgoing data, get return code */
    reverse_copy(&ret, &out[RSP_RST_OFFSET], sizeof(ret));

//#ifdef TPM_TRACE
//    {
//        _XDPRINTF_("TPM: response size = %d\n", *out_size);
//        _XDPRINTF_("TPM: response content: ");
//        print_hex("TPM: \t", out, *out_size);
//    }
//#endif

    memset(&reg_sts, 0, sizeof(reg_sts));
    reg_sts.command_ready = 1;
    {
        uint32_t value = pack_tpm_reg_sts_t(&reg_sts);
        _write_tpm_reg(locality, TPM_REG_STS, &value, SIZE_TPM_REG_STS);
    }
RelinquishControl:
    /* deactivate current locality */
    unpack_tpm_reg_access_t(&reg_acc, 0);
    //memset(&reg_acc, 0, SIZE_TPM_REG_ACCESS);
    reg_acc.active_locality = 1;
    {
        uint8_t value = pack_tpm_reg_access_t(&reg_acc);
        _write_tpm_reg(locality, TPM_REG_ACCESS, &value, SIZE_TPM_REG_ACCESS);
    }

    return ret;
}







//open TPM locality
static inline int xmhf_tpm_arch_x86vmx_open_locality(int locality){
        txt_didvid_t didvid;
        txt_ver_fsbif_emif_t ver;

        // display chipset fuse and device and vendor id info
        unpack_txt_didvid_t(&didvid, read_pub_config_reg(TXTCR_DIDVID));
        //_XDPRINTF_("\n%s: chipset ids: vendor: 0x%x, device: 0x%x, revision: 0x%x", __FUNCTION__,
        //       didvid.vendor_id, didvid.device_id, didvid.revision_id);
        unpack_txt_ver_fsbif_emif_t(&ver, read_pub_config_reg(TXTCR_VER_FSBIF));
        if ( (pack_txt_ver_fsbif_emif_t(&ver) & 0xffffffff) == 0xffffffff ||
             (pack_txt_ver_fsbif_emif_t(&ver) & 0xffffffff) == 0x00 )         /* need to use VER.EMIF */
            unpack_txt_ver_fsbif_emif_t(&ver, read_pub_config_reg(TXTCR_VER_EMIF));
        //_XDPRINTF_("\n%s: chipset production fused: %x", __FUNCTION__, ver.prod_fused);

        if(txt_is_launched()) {
            write_priv_config_reg(locality == 1 ? TXTCR_CMD_OPEN_LOCALITY1
                                  : TXTCR_CMD_OPEN_LOCALITY2, 0x01);
            read_priv_config_reg(TXTCR_E2STS);   /* just a fence, so ignore return */
            return 0;
        } else {
            //_XDPRINTF_("\n%s: ERROR: Locality opening UNIMPLEMENTED on Intel without SENTER\n", __FUNCTION__);
            return 1;
        }
}

//open TPM locality
static inline int xmhf_tpm_arch_open_locality(int locality){
    return xmhf_tpm_arch_x86vmx_open_locality(locality);
}




//check if TPM is ready for use
static inline bool xmhf_tpm_is_tpm_ready(uint32_t locality){
		return xmhf_tpm_arch_is_tpm_ready(locality);
}



//open TPM locality
static inline int xmhf_tpm_open_locality(int locality){
    /* We expect locality 1 or 2 */
    if(locality < 1 || locality > 2) {
        return 1;
    }

    if(xmhf_tpm_arch_open_locality(locality)) {
      //_XDPRINTF_("\n%s: FAILED to open TPM locality %d\n", __FUNCTION__, locality);
      return 1;
    };

    if(!xmhf_tpm_is_tpm_ready(locality)) {
        //_XDPRINTF_("\n%s: ERROR TPM is not ready, failed to open locality %d\n", __FUNCTION__, locality);
        return 1;
    }

    //_XDPRINTF_("\n%s: opened TPM locality %d", __FUNCTION__, locality);
    return 0;
}


//deactivate all TPM localities
static inline void xmhf_tpm_deactivate_all_localities(void){
	xmhf_tpm_arch_deactivate_all_localities();
}

//prepare TPM for use
static inline bool xmhf_tpm_prepare_tpm(void){
	return xmhf_tpm_arch_prepare_tpm();
}


/*
 * The _tpm_submit_cmd function comes with 2 global buffers: cmd_buf & rsp_buf.
 * Before calling, caller should fill cmd arguements into cmd_buf via
 * WRAPPER_IN_BUF macro. After calling, caller should fetch result from
 * rsp_buffer via WRAPPER_OUT_BUF macro.
 * cmd_buf content:
 *  0   1   2   3   4   5   6   7   8   9   10  ...
 * -------------------------------------------------------------
 * |  TAG  |     SIZE      |    ORDINAL    |    arguments ...
 * -------------------------------------------------------------
 * rsp_buf content:
 *  0   1   2   3   4   5   6   7   8   9   10  ...
 * -------------------------------------------------------------
 * |  TAG  |     SIZE      |  RETURN CODE  |    other data ...
 * -------------------------------------------------------------
 *
 *   locality : TPM locality (0 - 4)
 *   tag      : The TPM command tag
 *   cmd      : The TPM command ordinal
 *   arg_size : Size of argument data.
 *   out_size : IN/OUT paramter. The IN is the expected size of out data;
 *              the OUT is the size of output data within out buffer.
 *              The out_size MUST NOT be NULL.
 *   return   : TPM_SUCCESS for success, for other error code, refer to the .h
 */

/* static */
static inline uint32_t _tpm_submit_cmd(uint32_t locality, uint16_t tag, uint32_t cmd,
                               uint32_t arg_size, uint32_t *out_size)
{
    uint32_t    ret;
    uint32_t    cmd_size, rsp_size = 0;


    if ( out_size == NULL ) {
        //_XDPRINTF_("TPM: invalid param for _tpm_submit_cmd()\n");
        return TPM_BAD_PARAMETER;
    }

    /*
     * real cmd size should add 10 more bytes:
     *      2 bytes for tag
     *      4 bytes for size
     *      4 bytes for ordinal
     */
    cmd_size = CMD_HEAD_SIZE + arg_size;

    if ( cmd_size > TPM_CMD_SIZE_MAX ) {
        //_XDPRINTF_("TPM: cmd exceeds the max supported size.\n");
        return TPM_BAD_PARAMETER;
    }

    /* copy tag, size & ordinal into buf in a reversed byte order */
    reverse_copy(cmd_buf, &tag, sizeof(tag));
    reverse_copy(cmd_buf + CMD_SIZE_OFFSET, &cmd_size, sizeof(cmd_size));
    reverse_copy(cmd_buf + CMD_ORD_OFFSET, &cmd, sizeof(cmd));

    rsp_size = RSP_HEAD_SIZE + *out_size;
    rsp_size = (rsp_size > TPM_RSP_SIZE_MAX) ? TPM_RSP_SIZE_MAX: rsp_size;
    ret = tpm_write_cmd_fifo(locality, cmd_buf, cmd_size, rsp_buf, &rsp_size);

    /*
     * should subtract 10 bytes from real response size:
     *      2 bytes for tag
     *      4 bytes for size
     *      4 bytes for return code
     */
    rsp_size -= (rsp_size > RSP_HEAD_SIZE) ? RSP_HEAD_SIZE : rsp_size;

    if ( ret != TPM_SUCCESS )
        return ret;

    if ( *out_size == 0 || rsp_size == 0 )
        *out_size = 0;
    else
        *out_size = (rsp_size < *out_size) ? rsp_size : *out_size;

    return ret;
}


/*static inline*/
static inline uint32_t tpm_submit_cmd(uint32_t locality, uint32_t cmd,
                                      uint32_t arg_size, uint32_t *out_size)
{
    uint32_t rv;
    //uint64_t start, end;

    //start = rdtsc64();
    rv = _tpm_submit_cmd(locality, TPM_TAG_RQU_COMMAND, cmd,
                         arg_size, out_size);
    //end = rdtsc64();
    //_XDPRINTF_("TPM: PERF: Command 0x%08x consumed %lld cycles\n", cmd, end-start);
    return rv;
}


/* static */
static inline uint32_t tpm_get_capability(
                  uint32_t locality, tpm_capability_area_t cap_area,
                  uint32_t sub_cap_size, const uint8_t *sub_cap,
                  uint32_t *resp_size, uint8_t *resp)
{
    uint32_t ret, offset, out_size;

    if ( sub_cap == NULL || resp_size == NULL || resp == NULL ) {
        //_XDPRINTF_("TPM: tpm_get_capability() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    offset = 0;
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, cap_area);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, sub_cap_size);
    UNLOAD_BLOB(WRAPPER_IN_BUF, offset, sub_cap, sub_cap_size);

    out_size = sizeof(*resp_size) + *resp_size;

    ret = tpm_submit_cmd(locality, TPM_ORD_GET_CAPABILITY, offset, &out_size);

//#ifdef TPM_TRACE
//    _XDPRINTF_("TPM: get capability, return value = %08X\n", ret);
//#endif
    if ( ret != TPM_SUCCESS ) {
        //_XDPRINTF_("TPM: get capability, return value = %08X\n", ret);
        return ret;
    }

    offset = 0;
    LOAD_INTEGER(WRAPPER_OUT_BUF, offset, *resp_size);
    if ( out_size < sizeof(*resp_size) + *resp_size ) {
        //_XDPRINTF_("TPM: capability response too small\n");
        return TPM_FAIL;
    }
    LOAD_BLOB(WRAPPER_OUT_BUF, offset, resp, *resp_size);

    return ret;
}

#endif	//__ASSEMBLY__

#endif //__XMHF_TPM_ARCH_X86_H__
