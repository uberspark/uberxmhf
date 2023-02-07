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
 * XMHF: The following file is taken from:
 *  tboot-1.10.5/include/hash.h
 * Changes made include:
 *  Split to hash.h (in libbaremetal) and _txt_hash.h (in xmhf-core).
 * List of symbols in hash.h (others are in _txt_hash.h):
 *  TB_HALG_SHA1_LG
 *  TB_HALG_SHA1
 *  TB_HALG_SHA256
 *  TB_HALG_SM3
 *  TB_HALG_SHA384
 *  TB_HALG_SHA512
 *  TB_HALG_NULL
 *  SHA1_LENGTH
 *  SHA256_LENGTH
 *  SM3_LENGTH
 *  SHA384_LENGTH
 *  SHA512_LENGTH
 *  tb_hash_t
 */

/*
 * hash.h:  definition of and support fns for tb_hash_t type
 *
 * Copyright (c) 2006-2007, Intel Corporation
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

#ifndef __TXT_HASH_H__
#define __TXT_HASH_H__

typedef uint8_t sha1_hash_t[SHA1_LENGTH];
typedef uint8_t sha256_hash_t[SHA256_LENGTH];
typedef uint8_t sm3_hash_t[SM3_LENGTH];
typedef uint8_t sha384_hash_t[SHA384_LENGTH];
typedef uint8_t sha512_hash_t[SHA512_LENGTH];

static inline const char *hash_alg_to_string(uint16_t hash_alg)
{
    if ( hash_alg == TB_HALG_SHA1 || hash_alg == TB_HALG_SHA1_LG )
        return "TB_HALG_SHA1";
    else if ( hash_alg == TB_HALG_SHA256 )
        return "TB_HALG_SHA256";
    else if ( hash_alg == TB_HALG_SM3 )
        return "TB_HALG_SM3";
    else if ( hash_alg == TB_HALG_SHA384 )
        return "TB_HALG_SHA384";
    else if ( hash_alg == TB_HALG_SHA512 )
        return "TB_HALG_SHA512";
    else
        return "unsupported";
}

static inline unsigned int get_hash_size(uint16_t hash_alg)
{
    if ( hash_alg == TB_HALG_SHA1 || hash_alg == TB_HALG_SHA1_LG )
        return SHA1_LENGTH;
    else if ( hash_alg == TB_HALG_SHA256 )
        return SHA256_LENGTH;
    else if ( hash_alg == TB_HALG_SM3 )
        return SM3_LENGTH;
    else if ( hash_alg == TB_HALG_SHA384 )
        return SHA384_LENGTH;
    else if ( hash_alg == TB_HALG_SHA512 )
        return SHA512_LENGTH;
    else
        return 0;
}

extern bool are_hashes_equal(const tb_hash_t *hash1, const tb_hash_t *hash2,
                             uint16_t hash_alg);
extern bool hash_buffer(const unsigned char* buf, size_t size, tb_hash_t *hash,
                        uint16_t hash_alg);
extern bool extend_hash(tb_hash_t *hash1, const tb_hash_t *hash2,
                        uint16_t hash_alg);
extern void print_hash(const tb_hash_t *hash, uint16_t hash_alg);
extern bool import_hash(const char *string, tb_hash_t *hash, uint16_t alg);
extern void copy_hash(tb_hash_t *dest_hash, const tb_hash_t *src_hash,
                      uint16_t hash_alg);


#endif    /* __TXT_HASH_H__ */


/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
