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

#include <com.h> /* required by target.h included from drbg.h FIXME */
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

/**
 * OLD STUFF BELOW
 */

void test_AES256_use_df__COUNT0(void) {
	int i;
	NIST_CTR_DRBG drbg;
	char buffer[256];
    EntropyInputLen256NonceLen128PersonalizationStringLen0AdditionalInputLen0_t *s[] = {
        &count0, &count1, &count2, &count3, &count4, &count5, &count6, &count7, &count8, &count9, &count10, &count11, &count12, &count13, &count14
    };

    i=2;
    
	nist_ctr_initialize();

	nist_ctr_drbg_instantiate(&drbg, s[i]->EntropyInput, sizeof(s[i]->EntropyInput), s[i]->Nonce, sizeof(s[i]->Nonce), NULL, 0);
    do_buffer(&drbg, buffer, sizeof(s[i]->INTERMEDIATE_ReturnedBits));
    TEST_ASSERT_EQUAL_MEMORY(s[i]->INTERMEDIATE_ReturnedBits, buffer, sizeof(s[i]->INTERMEDIATE_ReturnedBits));
    
	nist_ctr_drbg_reseed(&drbg, s[i]->EntropyInputReseed, sizeof(s[i]->EntropyInputReseed), NULL, 0);

    do_buffer(&drbg, buffer, 16);
    TEST_ASSERT_EQUAL_MEMORY(s[i]->ReturnedBits, buffer, sizeof(s[i]->ReturnedBits));
}

void test_AES256_use_df_COUNT_0(void) {
	int i;
	NIST_CTR_DRBG drbg;
	char buffer[256];
    /*
      [AES-256 use df]
      [PredictionResistance = False]
      [EntropyInputLen = 256]
      [NonceLen = 128]
      [PersonalizationStringLen = 0]
      [AdditionalInputLen = 0]
      
      COUNT = 0
      EntropyInput = 5a194d5e2b31581454def675fb7958fec7db873e5689fc9d03217c68d8033820
      Nonce = 1b54b8ff0642bff521f15c1c0b665f3f
      PersonalizationString = 
      AdditionalInput = 
      INTERMEDIATE Key = b839fa3b11b77ac80f101e14afa7f85211048d745d8eaaa4bda9dca2a56259c1
      INTERMEDIATE V = b0ee8dfa67ecfd5c8dca69adc0b75e8d
      INTERMEDIATE ReturnedBits = 3f6db52dff53ae68e92abcd8131ef8bf
      EntropyInputReseed = f9e65e04d856f3a9c44a4cbdc1d00846f5983d771c1b137e4e0f9d8ef409f92e
      AdditionalInputReseed = 
      AdditionalInput = 
      ReturnedBits = a054303d8a7ea9889d903e077c6f218f
    */
    unsigned char EntropyInput[] = "\x5a\x19\x4d\x5e\x2b\x31\x58\x14\x54\xde\xf6\x75\xfb\x79\x58\xfe\xc7\xdb\x87\x3e\x56\x89\xfc\x9d\x03\x21\x7c\x68\xd8\x03\x38\x20";
    unsigned char Nonce[] = "\x1b\x54\xb8\xff\x06\x42\xbf\xf5\x21\xf1\x5c\x1c\x0b\x66\x5f\x3f";
    unsigned char PersonalizationString[] = "";
    unsigned char INTERMEDIATE_Key[] = "\xb8\x39\xfa\x3b\x11\xb7\x7a\xc8\x0f\x10\x1e\x14\xaf\xa7\xf8\x52\x11\x04\x8d\x74\x5d\x8e\xaa\xa4\xbd\xa9\xdc\xa2\xa5\x62\x59\xc1";
    unsigned char INTERMEDIATE_V[] = "\xb0\xee\x8d\xfa\x67\xec\xfd\x5c\x8d\xca\x69\xad\xc0\xb7\x5e\x8d";
    unsigned char INTERMEDIATE_ReturnedBits[] = "\x3f\x6d\xb5\x2d\xff\x53\xae\x68\xe9\x2a\xbc\xd8\x13\x1e\xf8\xbf";
    unsigned char EntropyInputReseed[] = "\xf9\xe6\x5e\x04\xd8\x56\xf3\xa9\xc4\x4a\x4c\xbd\xc1\xd0\x08\x46\xf5\x98\x3d\x77\x1c\x1b\x13\x7e\x4e\x0f\x9d\x8e\xf4\x09\xf9\x2e";
    unsigned char AdditionalInputReseed[] = "";
    unsigned char AdditionalInput2[] = "";
    unsigned char ReturnedBits[] = "\xa0\x54\x30\x3d\x8a\x7e\xa9\x88\x9d\x90\x3e\x07\x7c\x6f\x21\x8f";
    
	nist_ctr_initialize();

	nist_ctr_drbg_instantiate(&drbg, EntropyInput, 32, Nonce, 16, NULL, 0);
    do_buffer(&drbg, buffer, 16);
    TEST_ASSERT_EQUAL_MEMORY(INTERMEDIATE_ReturnedBits, buffer, 16);
    
    /* nist_dump_ctr_drbg(&drbg); */
    /* nist_dump_aes_ctx(&drbg.ctx);     */
    
	nist_ctr_drbg_reseed(&drbg, EntropyInputReseed, 32, NULL, 0);
    /* nist_dump_ctr_drbg(&drbg); */
    /* nist_dump_aes_ctx(&drbg.ctx); */

    do_buffer(&drbg, buffer, 16);
    TEST_ASSERT_EQUAL_MEMORY(ReturnedBits, buffer, 16);
}



/* #define KEYLEN_ALIGNED_BITS_TO_GENERATE (KEYLEN*20) */
/* #define KEYLEN_MISALIGNED_BITS_TO_GENERATE (KEYLEN_ALIGNED_BITS_TO_GENERATE+(KEYLEN/2)) */

/* void test_ctr_drbg_GENERIC(void) { */
/*     ctr_drbg_ctx ctx; */
/*     ctr_drbg_result_code_t rc; */
/*     uint8_t buf[KEYLEN_MISALIGNED_BITS_TO_GENERATE/8]; */

/*     /\* Basic instantiation *\/ */
/*     rc = Instantiate(&ctx); */
/*     TEST_ASSERT_EQUAL_INT(CTR_DRBG_SUCCESS, rc); */

/*     /\* Reseed counter should be set to 1 during instantiate *\/ */
/*     TEST_ASSERT_EQUAL_HEX64(1, ctx.reseed_counter); */

/*     /\* Generate some bits; number of bits is a multiple of KEYLEN *\/ */
/*     rc = Generate(&ctx, KEYLEN_ALIGNED_BITS_TO_GENERATE, buf); */
/*     TEST_ASSERT_EQUAL_INT(CTR_DRBG_SUCCESS, rc); */
/*     TEST_ASSERT_EQUAL_HEX64(2, ctx.reseed_counter);     */

/*     /\* Generate some bits; number of bits is NOT a multiple of KEYLEN *\/ */
/*     rc = Generate(&ctx, KEYLEN_MISALIGNED_BITS_TO_GENERATE, buf); */
/*     TEST_ASSERT_EQUAL_INT(CTR_DRBG_SUCCESS, rc); */
/*     TEST_ASSERT_EQUAL_HEX64(3, ctx.reseed_counter); */

/*     /\* Generate some bits; number of bits is a multiple of KEYLEN *\/ */
/*     rc = Generate(&ctx, KEYLEN_ALIGNED_BITS_TO_GENERATE, buf); */
/*     TEST_ASSERT_EQUAL_INT(CTR_DRBG_SUCCESS, rc); */
/*     TEST_ASSERT_EQUAL_HEX64(4, ctx.reseed_counter);     */

/*     /\* Generate some bits; number of bits is NOT a multiple of KEYLEN *\/ */
/*     rc = Generate(&ctx, KEYLEN_MISALIGNED_BITS_TO_GENERATE, buf); */
/*     TEST_ASSERT_EQUAL_INT(CTR_DRBG_SUCCESS, rc); */
/*     TEST_ASSERT_EQUAL_HEX64(5, ctx.reseed_counter); */
/* } */



