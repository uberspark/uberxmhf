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

/**
 * Consumable interface to CTR_DRBG PRNG.
 *
 * TODO: Support re-seeding.
 */

#include <xmhf.h> 

#include <random.h>
#include <crypto_init.h>

#include <tv_log.h>

/* libtomcrypt prng. this is just a wrapper for our internal drbg */
prng_state g_ltc_prng;
int g_ltc_prng_id;

/**
 * Reseed the CTR_DRBG if needed.  This function is structured to do
 * nothing if a reseed is not required, to simplify the logic in the
 * functions that actually service requests for random bytes.
 *
 * returns: 0 on success
 */
int reseed_ctr_drbg_using_tpm_entropy_if_needed(void) {
    uint8_t EntropyInput[CTR_DRBG_SEED_BITS/8];

    ASSERT(true == g_master_prng_init_completed);
    
    if (g_drbg.reseed_counter < NIST_CTR_DRBG_RESEED_INTERVAL)
        return 0; /* nothing to do */

    eu_err("Low Entropy: Attemping TPM-based PRNG reseed.");
    
    /* Get CTR_DRBG_SEED_BITS of entropy from the hardware TPM */
    EU_VERIFYN( get_hw_tpm_entropy(EntropyInput, CTR_DRBG_SEED_BITS/8),
                eu_err_e("FATAL ERROR: Could not access TPM to reseed PRNG."));

    EU_VERIFYN( nist_ctr_drbg_reseed( &g_drbg, EntropyInput, sizeof(EntropyInput), NULL, 0));
    
    eu_trace("master_crypto_init: PRNG reseeded successfully.");

    return 0;
}


/**
 * Returns a pseudo-random byte or HALT's the whole system if one
 * cannot be generated.
 */
uint8_t rand_byte_or_die(void) {
    uint8_t byte;

    EU_VERIFY( g_master_prng_init_completed);

    EU_VERIFYN( reseed_ctr_drbg_using_tpm_entropy_if_needed());
    EU_VERIFYN( nist_ctr_drbg_generate( &g_drbg, &byte, sizeof(byte), NULL, 0));

    return byte;
}

/**
 * Populates a buffer of pseudo-random bytes or HALT's the whole
 * system if they cannot be generated.
 */
void rand_bytes_or_die(uint8_t *out, unsigned int len) {
    EU_VERIFY( g_master_prng_init_completed);
    EU_VERIFY( out);
    EU_VERIFY( len >= 1);
    
    EU_VERIFYN( reseed_ctr_drbg_using_tpm_entropy_if_needed());

    EU_VERIFYN( nist_ctr_drbg_generate(&g_drbg, out, len, NULL, 0));
}    

/**
 * Best effort to populate an array of *len random-bytes.  Returns 0
 * on success, otherwise returns the number of bytes that were
 * actually available (and updates *len).
 */
int rand_bytes(uint8_t *out, unsigned int *len) {
    int rv=1;

    /* even here we do not want to tolerate failure to initialize */
    EU_VERIFY( g_master_prng_init_completed);

    EU_VERIFY( out);
    EU_VERIFY( len);
    EU_VERIFY( *len >= 1);

    /* at the present time this will either give all requested bytes
     * or fail completely.  no support for partial returns, though
     * that may one day be desirable. */
    EU_VERIFYN( reseed_ctr_drbg_using_tpm_entropy_if_needed());

    EU_CHKN( rv = nist_ctr_drbg_generate(&g_drbg, out, *len, NULL, 0));

    eu_trace("Successfully generated %d pseudo-random bytes", *len);

    rv=0;
 out:
    return rv;
}
