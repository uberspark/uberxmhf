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

#ifndef __DRBG_H__
#define __DRBG_H__

#include <target.h>
#include <aes.h>
#include <puttymem.h>

/* awesome trick from http://www.jaggersoft.com/pubs/CVu11_3.html */
#define COMPILE_TIME_ASSERT(pred)            \
    switch(0){case 0:case pred:;}

struct INT128_t {
    long long high;
    uint64_t low;
} __attribute__ ((packed));
typedef struct INT128_t INT128;

/* stores result in lhs */
static inline void add_INT128(INT128 *lhs, INT128 *rhs) {
    INT128 sum;

    if(!lhs || !rhs) HALT();

    sum.high = lhs->high + rhs->high;
    sum.low = lhs->low + rhs->low;
    /* check for overflow of low 64 bits, add carry to high */
    if (sum.low < lhs->low)
        ++sum.high;

    memcpy(lhs, &sum, sizeof(INT128));
}

static inline void xor_INT128(INT128 *lhs, INT128 *rhs) {
    if(!lhs || !rhs) HALT();

    lhs->high = lhs->high ^ rhs->high;
    lhs->low = lhs->low ^ rhs->low;
}


static inline void add1_INT128(INT128 *lhs) {
    INT128 one;
    one.high = 0;
    one.low = 1;

    add_INT128(lhs, &one);
}

static inline void sub_INT128(INT128 *lhs, INT128 *rhs) {
    INT128 diff;

    if(!lhs || !rhs) HALT();
    
    diff.high = lhs->high - rhs->high;
    diff.low = lhs->low - rhs->low;
    /* check for underflow of low 64 bits, subtract carry from high */
    if (diff.low > lhs->low)
        --diff.high;

    memcpy(lhs, &diff, sizeof(INT128));
}

/**
 * Design notes:
 *
 * We are assuming the use of the TPM's hardware RNG as the source of
 * entropy during instantiation and reseeding.  We are assuming that
 * the TPM's RNG provides high quality entropy.  Thus, no Derivation
 * Function is implemented.
 *
 * For simplicity in this initial implementation, no Additional Input
 * is supported when Generate calls are made requesting random
 * bits. Additional Input is optional in NIST SP 800-90.
 *
 * Likewise, no (optional) Personalization String is implemented.
 */


/**
 * Parameters (units are bits unless otherwise noted) (see Table 3 in
 * Section 10.2.1 of NIST SP 800-90).
 */

/* move to .h */
typedef enum {
    CTR_DRBG_SUCCESS = 0,
    CTR_DRBG_RESEED_NEEDED,
    CTR_DRBG_ERROR
} ctr_drbg_result_code_t;

/* everything in bits */
#define SECURITY_STRENGTH 128 
#define KEYLEN 128
#define OUTLEN 128
#define SEEDLEN 256
/* Since a Derviation Function is not used (i.e., these values would
 * change if a derivation function were to be used): */
/*#define MIN_LENGTH SEEDLEN*/ /* unnecessary, since both are SEEDLEN */
/*#define MAX_LENGTH SEEDLEN*/ /* unnecessary, since both are SEEDLEN */
/*#define MAX_PERSONALIZATION_STRING_LENGTH SEEDLEN*/ /* optional (consider RSA modulus of EK?) */
#define MAX_ADDITIONAL_INPUT_LENGTH SEEDLEN
/* XXX pseudo-code differs from spec in NIST SP 800-90; going with
   spec. can't see a reason that it matters whether requests are
   spread out or not */
#define MAX_NUMBER_OF_BITS_PER_REQUEST 0x80000 /* 2^19 */ 
/* XXX pseudo-code again differs from spec.  spec says 2^48,
 * pseudo-code uses 100,000. Going with pseudo-code since this will
 * still be quite rare in practice. */
#define RESEED_INTERVAL 100000

typedef struct ctr_drbg_internal_state {
    INT128 V;
    INT128 Key;
    uint64_t reseed_counter;
    /*uint32_t security_strength;*/ /* Fixed at 128 */
    /*bool predicition_resisitance_flag;*/ /* optional; we do not support prediction resistance */
    aes_context aes_ctx;
} ctr_drbg_ctx;

/* Functions defined in drbg.c */
ctr_drbg_result_code_t Instantiate(ctr_drbg_ctx *ctx);
ctr_drbg_result_code_t Reseed(ctr_drbg_ctx *ctx);
ctr_drbg_result_code_t Generate(ctr_drbg_ctx *ctx, uint32_t requested_no_of_bits, uint8_t *output);
ctr_drbg_result_code_t Uninstantiate(ctr_drbg_ctx *ctx);

#endif /* __DRBG_H__ */
