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

#include "unity.h"

#define __PRINT_H_ /* avoid indirectly including our print.h, which conflicts with libc stdio.h */

#define dprintf(...) while(0)

#define _PUTTYMEM_H_ /* avoid using puttymem */

#include <com.h> /* required by target.h included from drbg.h FIXME */
#include <drbg.h>

/* replacements for puttymem */
void *safemalloc(size_t size) {
    unsigned u = malloc(size);
    void *r = (void*)u;
    return r;
}

void safefree(void *p) {
    free(p);
}

void *vmemcpy(void *dest, const void *src, size_t n) {
    return memcpy(dest, src, n);
}

void *vmemset(void *s, int c, size_t n) {
    return memset(s, c, n);
}



/* standard unity constructions */
void setUp(void)
{
}

void tearDown(void)
{
}

/**
 * Clever helpers
 */
static uint32_t hamming_weight(uint32_t i)
{
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return ((i + (i >> 4) & 0xF0F0F0F) * 0x1010101) >> 24;
}

/**
 * actual tests
 */
#define maxu64 0xffffffffffffffffull

/**
 * First test the 128-bit integer implementation's carry capabilities.
 */
void test_add_INT128_carry(void) {
    INT128 i;
    i.high = 0;
    i.low = maxu64;

    TEST_ASSERT_EQUAL_HEX64(maxu64, i.low);

    add1_INT128(&i); /* should propagate carry to i.high */

    TEST_ASSERT_EQUAL_HEX64(0, i.low);
    TEST_ASSERT_EQUAL_HEX64(1, i.high);
}

void test_sub_INT128_carry(void) {
    INT128 i, one;
    i.high = 1;
    i.low = 0;

    one.high = 0;
    one.low = 1;

    sub_INT128(&i, &one);

    TEST_ASSERT_EQUAL_HEX64(0, i.high);
    TEST_ASSERT_EQUAL_HEX64(maxu64, i.low);
}



void test_hamming_weight(void) {
    TEST_ASSERT_EQUAL_INT(0, hamming_weight(0));

    TEST_ASSERT_EQUAL_INT(1, hamming_weight(128));

    TEST_ASSERT_EQUAL_INT(7, hamming_weight(127));

    TEST_ASSERT_EQUAL_INT(8, hamming_weight(255));
}

void test_drbg_ctr_MACROS(void) {
    TEST_ASSERT_EQUAL_INT(1, hamming_weight(SECURITY_STRENGTH));    
    TEST_ASSERT_EQUAL_INT(1, hamming_weight(KEYLEN));    
    TEST_ASSERT_EQUAL_INT(1, hamming_weight(OUTLEN));    
    TEST_ASSERT_EQUAL_INT(1, hamming_weight(SEEDLEN));    
}

#define KEYLEN_ALIGNED_BITS_TO_GENERATE (KEYLEN*20)
#define KEYLEN_MISALIGNED_BITS_TO_GENERATE (KEYLEN_ALIGNED_BITS_TO_GENERATE+(KEYLEN/2))

void test_ctr_drbg_GENERIC(void) {
    ctr_drbg_ctx ctx;
    ctr_drbg_result_code_t rc;
    uint8_t buf[KEYLEN_MISALIGNED_BITS_TO_GENERATE/8];

    /* Basic instantiation */
    rc = Instantiate(&ctx);
    TEST_ASSERT_EQUAL_INT(CTR_DRBG_SUCCESS, rc);

    /* Reseed counter should be set to 1 during instantiate */
    TEST_ASSERT_EQUAL_HEX64(1, ctx.reseed_counter);

    /* Generate some bits; number of bits is a multiple of KEYLEN */
    rc = Generate(&ctx, KEYLEN_ALIGNED_BITS_TO_GENERATE, buf);
    TEST_ASSERT_EQUAL_INT(CTR_DRBG_SUCCESS, rc);
    TEST_ASSERT_EQUAL_HEX64(2, ctx.reseed_counter);    

    /* Generate some bits; number of bits is NOT a multiple of KEYLEN */
    rc = Generate(&ctx, KEYLEN_MISALIGNED_BITS_TO_GENERATE, buf);
    TEST_ASSERT_EQUAL_INT(CTR_DRBG_SUCCESS, rc);
    TEST_ASSERT_EQUAL_HEX64(3, ctx.reseed_counter);

    /* Generate some bits; number of bits is a multiple of KEYLEN */
    rc = Generate(&ctx, KEYLEN_ALIGNED_BITS_TO_GENERATE, buf);
    TEST_ASSERT_EQUAL_INT(CTR_DRBG_SUCCESS, rc);
    TEST_ASSERT_EQUAL_HEX64(4, ctx.reseed_counter);    

    /* Generate some bits; number of bits is NOT a multiple of KEYLEN */
    rc = Generate(&ctx, KEYLEN_MISALIGNED_BITS_TO_GENERATE, buf);
    TEST_ASSERT_EQUAL_INT(CTR_DRBG_SUCCESS, rc);
    TEST_ASSERT_EQUAL_HEX64(5, ctx.reseed_counter);
}



/* uint8_t r[100]; */
/* ctr_drbg_ctx ctx; */
/* int i; */

/* Instantiate(&ctx); */
/* printf("\nDRBG test:\n"); */
/* for(i=0; i<5; i++) { */
/*     Generate(&ctx, 100*8, r); */
/*     printf("    %02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x\n", */
/*            r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9]); */
/* } */
/* Uninstantiate(&ctx); */

      
