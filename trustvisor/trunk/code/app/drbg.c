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

/** Deterministic Random Bit Generator (DRBG).  This file contains an
 * implementation of CTR_DRBG as per NIST SP 800-90, using AES-128 as
 * a block cipher.
 *
 * Author: jonmccune@cmu.edu
 * Initial implementation: 2011-07-08
 */

#include <drbg.h>

/**
 * Functions based on Pseudo-code in Appendix F.4 of NIST SP 800-90,
 * "CTR_DRBG Example Without A Derivaation Function".
 */

/* Update is for internal use only. */
static ctr_drbg_result_code_t Update(ctr_drbg_ctx *ctx, uint8_t *provided_data /* always SEEDLEN */) {
    INT128 temp1, temp2;
    INT128 *prov1, *prov2;

    if(!ctx || !provided_data) return CTR_DRBG_ERROR;

    /* 2. While() loop will only iterate twice; unroll it */
    aes_setkey_enc(&ctx->aes_ctx, (uint8_t*)&ctx->Key, KEYLEN);
    add1_INT128(&ctx->V); /* 2.1 */
    aes_crypt_ecb(&ctx->aes_ctx, AES_ENCRYPT, (uint8_t*)&ctx->V, (uint8_t*)&temp1); /* 2.2 */
    add1_INT128(&ctx->V); /* 2.1 */
    aes_crypt_ecb(&ctx->aes_ctx, AES_ENCRYPT, (uint8_t*)&ctx->V, (uint8_t*)&temp2); /* 2.2 */

    /* 3. Unneeded. We have precisely 256 bits of temp. */

    /* 4. */
    COMPILE_TIME_ASSERT(sizeof(INT128) == SEEDLEN/8/2);
    prov1 = (INT128*)provided_data;
    prov2 = (INT128*)(provided_data + sizeof(INT128));
    xor_INT128(&temp1, prov1);
    xor_INT128(&temp2, prov2);
    
    memcpy(&ctx->Key, &temp1, sizeof(INT128)); /* 5. */
    memcpy(&ctx->V, &temp2, sizeof(INT128)); /* 6. */

    /* 7. Implicit.  ctx is updated. */
    return CTR_DRBG_SUCCESS;
}

static ctr_drbg_result_code_t Reseed_internal(ctr_drbg_ctx *ctx, uint8_t *seed_material /* always SEEDLEN */) {
    ctr_drbg_result_code_t rv;
    
    if(!ctx || !seed_material) return CTR_DRBG_ERROR;

    rv = Update(ctx, seed_material);
    if(CTR_DRBG_SUCCESS != rv) return rv;

    ctx->reseed_counter = 1;

    return rv;
}

ctr_drbg_result_code_t Reseed(ctr_drbg_ctx *ctx) {
    uint8_t seed_material[SEEDLEN/8];

    if(!ctx) return CTR_DRBG_ERROR;

#if 0    
    Get_256_Bits_Of_TPM_Entropy_Into_seed_material();
#else
    {
        int i;
        for(i=0; i<SEEDLEN/8; i++) seed_material[i] = (uint8_t)i;
    }
#endif

    return Reseed_internal(ctx, seed_material);
}

/* Makes calls to TPM to collect its own entropy. Security_Strength is
 * fixed at 128 bits. */
ctr_drbg_result_code_t Instantiate(ctr_drbg_ctx *ctx) {
    INT128 seed_material;

    if(!ctx) return CTR_DRBG_ERROR;

    memset(ctx, 0, sizeof(ctr_drbg_ctx));

    return Reseed(ctx);    
}


/**
 * This is the main interface to this DRBG.  Note that
 * additional_input is not supported.  This function always returns a
 * number of bits that is a multiple of 8.
 */
ctr_drbg_result_code_t Generate(ctr_drbg_ctx *ctx, uint32_t requested_no_of_bits, uint8_t *output) {
    ctr_drbg_result_code_t rv;
    uint8_t additional_input[SEEDLEN/8];
    uint8_t *temp;
    uint32_t temp_bits;
    uint8_t *p;
    uint32_t bits_so_far;
    
    if(!ctx || !output || requested_no_of_bits < 1) { return CTR_DRBG_ERROR; }

    if(requested_no_of_bits > MAX_NUMBER_OF_BITS_PER_REQUEST) {
        return CTR_DRBG_ERROR;
    }

    if(requested_no_of_bits % 8 != 0) {
        return CTR_DRBG_ERROR;
    }
    
    /* 1. CTR_DRBG_Generare_Algorithm Step 1. */
    if(ctx->reseed_counter > RESEED_INTERVAL) {
        rv = Reseed(ctx);
        if(CTR_DRBG_SUCCESS != rv) {
            return CTR_DRBG_RESEED_NEEDED;
        }
    }

    /* 2. */
    memset(additional_input, 0, SEEDLEN/8);

    /* 3. */
    ASSERT(1 == hamming_weight(KEYLEN));
    temp_bits = requested_no_of_bits % KEYLEN ?
        requested_no_of_bits + KEYLEN & ~(KEYLEN-1)
        : requested_no_of_bits;
    
    temp = (uint8_t*)vmalloc(temp_bits/8);
    if(NULL == temp) { return CTR_DRBG_ERROR; }

    /* 4. */
    p = temp;
    bits_so_far = 0;    
    while(bits_so_far < requested_no_of_bits) {
        add1_INT128(&ctx->V); /* 4.1 */
        /* 4.2 */
        aes_setkey_enc(&ctx->aes_ctx, (uint8_t*)&ctx->Key, KEYLEN);
        aes_crypt_ecb(&ctx->aes_ctx, AES_ENCRYPT, (uint8_t*)&ctx->V, (uint8_t*)p);
        /* 4.3 */
        p += KEYLEN/8;
        bits_so_far += KEYLEN;
    }
    /* 5. */
    memcpy(output, temp, requested_no_of_bits/8);    
    if(temp) { vfree(temp); temp = NULL; }
    
    Update(ctx, additional_input); /* 6. */
    ctx->reseed_counter++; /* 7. */
    return CTR_DRBG_SUCCESS; /* 8. */
}

ctr_drbg_result_code_t Uninstantiate(ctr_drbg_ctx *ctx) {
    uint8_t *p;
    unsigned int i;
    
    if(!ctx) return CTR_DRBG_ERROR;    

    /* Clunky zeroization to prevent compiler from optimizing this
     * away. TODO: Verify that it works. */

    p = (uint8_t*)ctx;
    
    for(i=0; i<sizeof(ctr_drbg_ctx); i++)
        ((unsigned char volatile *)p)[i] = 0;    

    return CTR_DRBG_SUCCESS;
}

/**/






    
