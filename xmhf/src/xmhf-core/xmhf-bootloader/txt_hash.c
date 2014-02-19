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
 * hash.c: support functions for tb_hash_t type
 *
 * Copyright (c) 2006-2010, Intel Corporation
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

#include <xmhf.h> 

/*
 * are_hashes_equal
 *
 * compare whether two hash values are equal.
 *
 */
bool are_hashes_equal(const tb_hash_t *hash1, const tb_hash_t *hash2,
                      uint8_t hash_alg)
{
    if ( ( hash1 == NULL ) || ( hash2 == NULL ) ) {
        printf("Error: hash pointer is zero.\n");
        return false;
    }

    if ( hash_alg == TB_HALG_SHA1 )
        return (memcmp((const char*)hash1, (const char*)hash2, SHA1_LENGTH) == 0);
    else {
        printf("unsupported hash alg (%u)\n", hash_alg);
        return false;
    }
}

/*
 * hash_buffer
 *
 * hash the buffer according to the algorithm
 *
 */
bool hash_buffer(const unsigned char* buf, size_t size, tb_hash_t *hash,
                 uint8_t hash_alg)
{
    if ( hash == NULL ) {
        printf("Error: There is no space for output hash.\n");
        return false;
    }

    if ( hash_alg == TB_HALG_SHA1 ) {
        sha1_buffer(buf, size, hash->sha1);
        return true;
    }
    else {
        printf("unsupported hash alg (%u)\n", hash_alg);
        return false;
    }
}

/*
 * extend_hash
 *
 * perform "extend" of two hashes (i.e. hash1 = SHA(hash1 || hash2)
 *
 */
bool extend_hash(tb_hash_t *hash1, const tb_hash_t *hash2, uint8_t hash_alg)
{
    uint8_t buf[2*get_hash_size(hash_alg)];

    if ( hash1 == NULL || hash2 == NULL ) {
        printf("Error: There is no space for output hash.\n");
        return false;
    }

    if ( hash_alg == TB_HALG_SHA1 ) {
        memcpy(buf, &(hash1->sha1), sizeof(hash1->sha1));
        memcpy(buf + sizeof(hash1->sha1), &(hash2->sha1), sizeof(hash1->sha1));
        sha1_buffer(buf, 2*sizeof(hash1->sha1), hash1->sha1);
        return true;
    }
    else {
        printf("unsupported hash alg (%u)\n", hash_alg);
        return false;
    }
}

void print_hash(const tb_hash_t *hash, uint8_t hash_alg)
{
    if ( hash == NULL ) {
        printf("NULL");
        return;
    }

    if ( hash_alg == TB_HALG_SHA1 )
        print_hex(NULL, (const uint8_t *)hash->sha1, sizeof(hash->sha1));
    else {
        printf("unsupported hash alg (%u)\n", hash_alg);
        return;
    }
}

void copy_hash(tb_hash_t *dest_hash, const tb_hash_t *src_hash,
               uint8_t hash_alg)
{
    if ( dest_hash == NULL || dest_hash == NULL ) {
        printf("hashes are NULL\n");
        return;
    }

    if ( hash_alg == TB_HALG_SHA1 )
        memcpy(dest_hash, src_hash, SHA1_LENGTH);
    else
        printf("unsupported hash alg (%u)\n", hash_alg);
}



/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
