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

void
do_buffer(NIST_CTR_DRBG* drbg, char* buffer, int length)
{
	nist_ctr_drbg_generate(drbg, buffer, length, NULL, 0);

	printf("%d:\n", length);
	nist_dump_hex(buffer, length);
	printf("\n");
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
    
    unsigned char EntropyInput[] = {
        0x5a, 0x19, 0x4d, 0x5e, 0x2b, 0x31, 0x58, 0x14,
        0x54, 0xde, 0xf6, 0x75, 0xfb, 0x79, 0x58, 0xfe,
        0xc7, 0xdb, 0x87, 0x3e, 0x56, 0x89, 0xfc, 0x9d,
        0x03, 0x21, 0x7c, 0x68, 0xd8, 0x03, 0x38, 0x20
    };
    
    unsigned char Nonce[] = {
        0x1b, 0x54, 0xb8, 0xff, 0x06, 0x42, 0xbf, 0xf5,
        0x21, 0xf1, 0x5c, 0x1c, 0x0b, 0x66, 0x5f, 0x3f
    };
    
    unsigned char EntropyInputReseed[] = {
        0xf9, 0xe6, 0x5e, 0x04, 0xd8, 0x56, 0xf3, 0xa9,
        0xc4, 0x4a, 0x4c, 0xbd, 0xc1, 0xd0, 0x08, 0x46,
        0xf5, 0x98, 0x3d, 0x77, 0x1c, 0x1b, 0x13, 0x7e,
        0x4e, 0x0f, 0x9d, 0x8e, 0xf4, 0x09, 0xf9, 0x2e
    };

    unsigned char INTERMEDIATEReturnedBits[] = 
        "\x3f\x6d\xb5\x2d\xff\x53\xae\x68\xe9\x2a\xbc\xd8\x13\x1e\xf8\xbf";
    
    unsigned char ReturnedBits[] =
        "\xa0\x54\x30\x3d\x8a\x7e\xa9\x88\x9d\x90\x3e\x07\x7c\x6f\x21\x8f";
    
    
    printf("NIST TEST VECTOR\n");

	nist_ctr_initialize();

	nist_ctr_drbg_instantiate(&drbg, EntropyInput, 32, Nonce, 16, NULL, 0);
    do_buffer(&drbg, buffer, 16);
    TEST_ASSERT_EQUAL_MEMORY(INTERMEDIATEReturnedBits, buffer, 16);
    
    nist_dump_ctr_drbg(&drbg);
    nist_dump_aes_ctx(&drbg.ctx);    
    
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



