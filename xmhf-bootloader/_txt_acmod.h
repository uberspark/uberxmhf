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
 * acmod.c: support functions for use of Intel(r) TXT Authenticated
 *          Code (AC) Modules
 *
 * Copyright (c) 2003-2010, Intel Corporation
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

/*
 * Modified for XMHF by jonmccune@cmu.edu, 2011.01.04
 *
 * XXX TODO: [Almost?] All of this is only needed in init; pull out of
 * common include directory to reduce SL/Runtime TCB.
 */

#ifndef __TXT_ACMOD_H__
#define __TXT_ACMOD_H__

/*
 * authenticated code (AC) module header (ver 0.0)
 */

typedef union {
    uint16_t _raw;
    struct {
        uint16_t  reserved          : 14;
        uint16_t  pre_production    : 1;
        uint16_t  debug_signed      : 1;
    };
} acm_flags_t;

typedef struct {
    uint32_t     module_type;
    uint32_t     header_len;
    uint32_t     header_ver;          /* currently 0.0 */
    uint16_t     chipset_id;
    acm_flags_t  flags;
    uint32_t     module_vendor;
    uint32_t     date;
    uint32_t     size;
    uint32_t     reserved1;
    uint32_t     code_control;
    uint32_t     error_entry_point;
    uint32_t     gdt_limit;
    uint32_t     gdt_base;
    uint32_t     seg_sel;
    uint32_t     entry_point;
    uint8_t      reserved2[64];
    uint32_t     key_size;
    uint32_t     scratch_size;
    uint8_t      rsa2048_pubkey[256];
    uint32_t     pub_exp;
    uint8_t      rsa2048_sig[256];
    uint32_t     scratch[143];
    uint8_t      user_area[];
} acm_hdr_t;

/* value of module_type field */
#define ACM_TYPE_CHIPSET        0x02

/* value of module_vendor field */
#define ACM_VENDOR_INTEL        0x8086

typedef struct {
    uuid_t      uuid;
    uint8_t     chipset_acm_type;
    uint8_t     version;             /* currently 3 */
    uint16_t    length;
    uint32_t    chipset_id_list;
    uint32_t    os_sinit_data_ver;
    uint32_t    min_mle_hdr_ver;
    txt_caps_t  capabilities;
    uint8_t     acm_ver;
    uint8_t     reserved[3];
} acm_info_table_t;

/* ACM UUID value */
#define ACM_UUID_V3        {0x7fc03aaa, 0x46a7, 0x18db, 0xac2e, \
                                {0x69, 0x8f, 0x8d, 0x41, 0x7f, 0x5a}}

/* chipset_acm_type field values */
#define ACM_CHIPSET_TYPE_BIOS         0x00
#define ACM_CHIPSET_TYPE_SINIT        0x01

typedef struct {
    uint32_t  flags;
    uint16_t  vendor_id;
    uint16_t  device_id;
    uint16_t  revision_id;
    uint16_t  reserved;
    uint32_t  extended_id;
} acm_chipset_id_t;

typedef struct {
    uint32_t           count;
    acm_chipset_id_t   chipset_ids[];
} acm_chipset_id_list_t;

extern void print_uuid(const uuid_t *uuid);
extern void print_txt_caps(const char *prefix, txt_caps_t caps);
extern bool is_sinit_acmod(void *acmod_base, size_t acmod_size, bool quiet);
extern bool does_acmod_match_chipset(acm_hdr_t* hdr);
extern acm_hdr_t *copy_sinit(acm_hdr_t *sinit);
extern bool verify_acmod(acm_hdr_t *acm_hdr);
extern uint32_t get_supported_os_sinit_data_ver(acm_hdr_t* hdr);
extern uint32_t get_sinit_capabilities(acm_hdr_t* hdr);
#endif /* __TXT_ACMOD_H__ */

/*
 * Local variables:
 * mode: C
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
