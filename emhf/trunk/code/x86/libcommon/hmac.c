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

/*      $OpenBSD: hmac.c,v 1.2 2008/09/06 22:23:20 djm Exp $    */

/*-
 * Copyright (c) 2008 Damien Bergamini <damien.bergamini@free.fr>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

/*
 * This code implements the HMAC algorithm described in RFC 2104 using
 * the MD5, SHA1 and SHA-256 hash functions.
 */

/*
 * Modified for EMHF. Jonathan McCune.
 */

#include <emhf.h> 

#define SHA1_BLOCK_LENGTH 64
#define SHA1_DIGEST_LENGTH 20

#define bzero(buf, len) memset(buf, 0, len)
#define bcopy(src, dst, len) memcpy(dst, src, len)

void
HMAC_SHA1_Init(HMAC_SHA1_CTX *ctx, const uint8_t *key, unsigned int key_len)
{
    uint8_t k_ipad[SHA1_BLOCK_LENGTH];
    int i;

    if (key_len > SHA1_BLOCK_LENGTH) {
        SHA1_Init(&ctx->ctx);
        SHA1_Update(&ctx->ctx, key, key_len);
        SHA1_Final(ctx->key, &ctx->ctx);
        ctx->key_len = SHA1_DIGEST_LENGTH;
    } else {
        bcopy(key, ctx->key, key_len);
        ctx->key_len = key_len;
    }

    bzero(k_ipad, SHA1_BLOCK_LENGTH);
    bcopy(ctx->key, k_ipad, ctx->key_len);
    for (i = 0; i < SHA1_BLOCK_LENGTH; i++)
        k_ipad[i] ^= 0x36;

    SHA1_Init(&ctx->ctx);
    SHA1_Update(&ctx->ctx, k_ipad, SHA1_BLOCK_LENGTH);

    bzero(k_ipad, sizeof k_ipad);
}

void
HMAC_SHA1_Update(HMAC_SHA1_CTX *ctx, const uint8_t *data, unsigned int len)
{
    SHA1_Update(&ctx->ctx, data, len);
}

void
HMAC_SHA1_Final(uint8_t digest[SHA1_DIGEST_LENGTH], HMAC_SHA1_CTX *ctx)
{
    uint8_t k_opad[SHA1_BLOCK_LENGTH];
    int i;

    SHA1_Final(digest, &ctx->ctx);

    bzero(k_opad, SHA1_BLOCK_LENGTH);
    bcopy(ctx->key, k_opad, ctx->key_len);
    for (i = 0; i < SHA1_BLOCK_LENGTH; i++)
        k_opad[i] ^= 0x5c;

    SHA1_Init(&ctx->ctx);
    SHA1_Update(&ctx->ctx, k_opad, SHA1_BLOCK_LENGTH);
    SHA1_Update(&ctx->ctx, digest, SHA1_DIGEST_LENGTH);
    SHA1_Final(digest, &ctx->ctx);

    bzero(k_opad, sizeof k_opad);
}

void
HMAC_SHA1(const uint8_t *key, uint32_t keylen,
          const uint8_t *msg, uint32_t len,
          uint8_t md[SHA_DIGEST_LENGTH]) {

    HMAC_SHA1_CTX ctx;

    HMAC_SHA1_Init(&ctx, key, keylen);
    HMAC_SHA1_Update(&ctx, msg, len);
    HMAC_SHA1_Final(md, &ctx);
}
