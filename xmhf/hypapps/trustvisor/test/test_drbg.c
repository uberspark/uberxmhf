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

#include "unity.h"

#define __PRINT_H_ /* avoid indirectly including our print.h, which conflicts with libc stdio.h */

#define dprintf(...) while(0)

#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <nist_ctr_drbg.h>


/* standard unity constructions */
void setUp(void)
{
}

void tearDown(void)
{
}

/**
   [AES-256 use df]
   [PredictionResistance = False]
   [EntropyInputLen = 256]
   [NonceLen = 128]
   [PersonalizationStringLen = 0]
   [AdditionalInputLen = 0]
 */

typedef struct {
    unsigned char EntropyInput[32];
    unsigned char Nonce[16];
    unsigned char PersonalizationString[1];
    unsigned char AdditionalInput[1];
    unsigned char INTERMEDIATE_Key[32];
    unsigned char INTERMEDIATE_V[16];
    unsigned char INTERMEDIATE_ReturnedBits[16];
    unsigned char EntropyInputReseed[32];
    unsigned char AdditionalInputReseed[1];
    unsigned char AdditionalInput2[1];
    unsigned char ReturnedBits[16];
} EntropyInputLen256NonceLen128PersonalizationStringLen0AdditionalInputLen0_t;

#include "nist_test_vectors.h"

void do_buffer(NIST_CTR_DRBG* drbg, char* buffer, int length)
{
	nist_ctr_drbg_generate(drbg, buffer, length, NULL, 0);

	/* printf("%d: ", length); */
	/* nist_dump_hex(buffer, length); */
	/* printf("\n"); */
}

void do_initialize_instantiate_and_buffer(EntropyInputLen256NonceLen128PersonalizationStringLen0AdditionalInputLen0_t *s,
                                          NIST_CTR_DRBG* drbg, char* buffer) {

	nist_ctr_initialize();

	nist_ctr_drbg_instantiate(drbg, s->EntropyInput, sizeof(s->EntropyInput), s->Nonce, sizeof(s->Nonce), NULL, 0);
    do_buffer(drbg, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
}

void do_reseed_and_buffer(EntropyInputLen256NonceLen128PersonalizationStringLen0AdditionalInputLen0_t *s,
                          NIST_CTR_DRBG* drbg, char* buffer) {

	nist_ctr_drbg_reseed(drbg, s->EntropyInputReseed, sizeof(s->EntropyInputReseed), NULL, 0);

    do_buffer(drbg, buffer, sizeof(s->ReturnedBits));
}


void test_AES256_use_df_EntropyInputLen256_NonceLen128_PersonalizationStringLen0_AdditionalInputLen0(void) {
	NIST_CTR_DRBG drbg;
	char buffer[256];
    EntropyInputLen256NonceLen128PersonalizationStringLen0AdditionalInputLen0_t *s;

    s = &count0;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));

    s = &count1;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));

    s = &count2;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));

    s = &count3;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));

    s = &count4;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));

    s = &count5;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));

    s = &count6;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));

    s = &count7;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));

    s = &count8;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));

    s = &count9;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));

    s = &count10;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));

    s = &count11;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));

    s = &count12;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));

    s = &count13;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));

    s = &count14;
    do_initialize_instantiate_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->INTERMEDIATE_ReturnedBits, buffer, sizeof(s->INTERMEDIATE_ReturnedBits));
    do_reseed_and_buffer(s, &drbg, buffer);
    TEST_ASSERT_EQUAL_MEMORY(s->ReturnedBits, buffer, sizeof(s->ReturnedBits));
}

void test_uninstantiate_actually_zeros(void) {
    NIST_CTR_DRBG drbg;
    NIST_CTR_DRBG drbg0;

    /* First give us a reference struct set to 0 ourselves, to compare against. */
    memset(&drbg0, 0x00, sizeof(NIST_CTR_DRBG));
    
    /* Second set the DRBG struct to have all bits set. */
    memset(&drbg, 0xff, sizeof(NIST_CTR_DRBG));

    /* Third invoke the library's zeroize function */
    nist_zeroize(&drbg, sizeof(NIST_CTR_DRBG));

    /* Fourth check that it worked */
    TEST_ASSERT_EQUAL_MEMORY(&drbg, &drbg0, sizeof(NIST_CTR_DRBG));
}
