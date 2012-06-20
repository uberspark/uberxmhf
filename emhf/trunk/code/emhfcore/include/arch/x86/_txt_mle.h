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
 * mle.h: Intel(r) TXT MLE header definition
 *
 * Copyright (c) 2003-2008, Intel Corporation
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
 */

#ifndef __MLE_H__
#define __MLE_H__

/*
 * SINIT/MLE capabilities
 */
typedef union {
    uint32_t  _raw;
    struct {
        uint32_t  rlp_wake_getsec     : 1;
        uint32_t  rlp_wake_monitor    : 1;
        uint32_t  ecx_pgtbl           : 1;
        uint32_t  reserved            : 29;
    };
} txt_caps_t;


/* taken from tboot-20101005/include/uuid.h */
typedef struct __packed {
  uint32_t    data1;
  uint16_t    data2;
  uint16_t    data3;
  uint16_t    data4;
  uint8_t     data5[6];
} uuid_t;

/* static inline bool are_uuids_equal(const uuid_t *uuid1, const uuid_t *uuid2) */
/* { */
/*     return (memcmp(uuid1, uuid2, sizeof(*uuid1)) == 0); */
/* } */

/*
 * MLE header structure
 *   describes an MLE for SINIT and OS/loader SW
 */
typedef struct {
    uuid_t      uuid;
    uint32_t    length;
    uint32_t    version;
    uint32_t    entry_point;
    uint32_t    first_valid_page;
    uint32_t    mle_start_off;
    uint32_t    mle_end_off;
    txt_caps_t  capabilities;
    uint32_t    cmdline_start_off;
    uint32_t    cmdline_end_off;
} mle_hdr_t;

#define MLE_HDR_UUID      {0x9082ac5a, 0x476f, 0x74a7, 0x5c0f, \
                              {0x55, 0xa2, 0xcb, 0x51, 0xb6, 0x42}}

/*
 * values supported by current version of tboot
 */
#define MLE_HDR_VER       0x00020001     /* 2.1 */
#define MLE_HDR_CAPS      0x00000007     /* rlp_wake_{getsec, monitor} = 1,
                                            ecx_pgtbl = 1 */

/* from tboot-20101005/include/tb_error.h */
typedef enum {
    TB_ERR_NONE                = 0,         /* succeed */
    TB_ERR_FIXED               = 1,         /* previous error has been fixed */

    TB_ERR_GENERIC,                         /* non-fatal generic error */

    TB_ERR_TPM_NOT_READY,                   /* tpm not ready */
    TB_ERR_SMX_NOT_SUPPORTED,               /* smx not supported */
    TB_ERR_VMX_NOT_SUPPORTED,               /* vmx not supported */
    TB_ERR_TXT_NOT_SUPPORTED,               /* txt not supported */

    TB_ERR_MODULE_VERIFICATION_FAILED,      /* module failed to verify against
                                               policy */
    TB_ERR_MODULES_NOT_IN_POLICY,           /* modules in mbi but not in
                                               policy */
    TB_ERR_POLICY_INVALID,                  /* policy is invalid */
    TB_ERR_POLICY_NOT_PRESENT,              /* no policy in TPM NV */

    TB_ERR_SINIT_NOT_PRESENT,               /* SINIT ACM not provided */
    TB_ERR_ACMOD_VERIFY_FAILED,             /* verifying AC module failed */

    TB_ERR_POST_LAUNCH_VERIFICATION,        /* verification of post-launch
                                               failed */
    TB_ERR_S3_INTEGRITY,                    /* creation or verification of
                                               S3 integrity measurements
                                               failed */

    TB_ERR_FATAL,                           /* generic fatal error */
    TB_ERR_MAX
} tb_error_t;


#endif      /* __MLE_H__ */


/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
