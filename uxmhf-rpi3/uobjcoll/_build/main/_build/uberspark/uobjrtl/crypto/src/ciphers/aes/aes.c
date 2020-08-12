/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

/* LibTomCrypt, modular cryptographic library -- Tom St Denis
 *
 * LibTomCrypt is a library that provides various cryptographic
 * algorithms in a highly modular and flexible manner.
 *
 * The library is free for all purposes without any express
 * guarantee it works.
 *
 * Tom St Denis, tomstdenis@gmail.com, http://libtom.org
 */

/* AES implementation by Tom St Denis
 *
 * Derived from the Public Domain source code by

---
  * rijndael-alg-fst.c
  *
  * @version 3.0 (December 2000)
  *
  * Optimised ANSI C code for the Rijndael cipher (now AES)
  *
  * @author Vincent Rijmen <vincent.rijmen@esat.kuleuven.ac.be>
  * @author Antoon Bosselaers <antoon.bosselaers@esat.kuleuven.ac.be>
  * @author Paulo Barreto <paulo.barreto@terra.com.br>
---
 */

#include <uberspark/uobjrtl/crypto/include/ciphers/aes/aes.h>


const struct ltc_cipher_descriptor rijndael_desc =
{
    "rijndael",
    6,
    16, 32, 16, 10
};

static u32 setup_mix(u32 temp)
{
   return (Te4_3[byte(temp, 2)]) ^
          (Te4_2[byte(temp, 1)]) ^
          (Te4_1[byte(temp, 0)]) ^
          (Te4_0[byte(temp, 3)]);
}


 /**
  *  Initialize the AES (Rijndael) block cipher
  *  @param key The symmetric key you wish to pass
  *  @param keylen The key length in bytes
  *  @param num_rounds The number of rounds desired (0 for default)
  *  @param skey The key in as scheduled by this function.
  *  @return CRYPT_OK if successful
  *
  *  @uobjrtl_namespace{uberspark/uobjrtl/crypto}
  * 
  * @headers_begin 
  * #include <uberspark/uobjrtl/crypto/include/ciphers/aes/aes.h>
  * @headers_end
  */
int uberspark_uobjrtl_crypto__ciphers_aes__rijndael_setup(const unsigned char *key, int keylen, int num_rounds, symmetric_key *skey)
{
    int i;
    u32 temp, *rk;
    u32 *rrk;

    LTC_ARGCHK(key  != NULL);
    LTC_ARGCHK(skey != NULL);

    if (keylen != 16 && keylen != 24 && keylen != 32) {
       return CRYPT_INVALID_KEYSIZE;
    }

    if (num_rounds != 0 && num_rounds != (10 + ((keylen/8)-2)*2)) {
       return CRYPT_INVALID_ROUNDS;
    }

    skey->rijndael.Nr = 10 + ((keylen/8)-2)*2;

    /* setup the forward key */
    i                 = 0;
    rk                = skey->rijndael.eK;
    LOAD32H(rk[0], key     );
    LOAD32H(rk[1], key +  4);
    LOAD32H(rk[2], key +  8);
    LOAD32H(rk[3], key + 12);
    if (keylen == 16) {
        for (;;) {
            temp  = rk[3];
            rk[4] = rk[0] ^ setup_mix(temp) ^ rcon[i];
            rk[5] = rk[1] ^ rk[4];
            rk[6] = rk[2] ^ rk[5];
            rk[7] = rk[3] ^ rk[6];
            if (++i == 10) {
               break;
            }
            rk += 4;
        }
    } else if (keylen == 24) {
        LOAD32H(rk[4], key + 16);
        LOAD32H(rk[5], key + 20);
        for (;;) {
            temp = rk[5];
            rk[ 6] = rk[ 0] ^ setup_mix(temp) ^ rcon[i];
            rk[ 7] = rk[ 1] ^ rk[ 6];
            rk[ 8] = rk[ 2] ^ rk[ 7];
            rk[ 9] = rk[ 3] ^ rk[ 8];
            if (++i == 8) {
                break;
            }
            rk[10] = rk[ 4] ^ rk[ 9];
            rk[11] = rk[ 5] ^ rk[10];
            rk += 6;
        }
    } else if (keylen == 32) {
        LOAD32H(rk[4], key + 16);
        LOAD32H(rk[5], key + 20);
        LOAD32H(rk[6], key + 24);
        LOAD32H(rk[7], key + 28);
        for (;;) {
            temp = rk[7];
            rk[ 8] = rk[ 0] ^ setup_mix(temp) ^ rcon[i];
            rk[ 9] = rk[ 1] ^ rk[ 8];
            rk[10] = rk[ 2] ^ rk[ 9];
            rk[11] = rk[ 3] ^ rk[10];
            if (++i == 7) {
                break;
            }
            temp = rk[11];
            rk[12] = rk[ 4] ^ setup_mix(RORc(temp, 8));
            rk[13] = rk[ 5] ^ rk[12];
            rk[14] = rk[ 6] ^ rk[13];
            rk[15] = rk[ 7] ^ rk[14];
            rk += 8;
        }
    } else {
       /* this can't happen */
       /* coverity[dead_error_line] */
       return CRYPT_ERROR;
    }

    /* setup the inverse key now */
    rk   = skey->rijndael.dK;
    rrk  = skey->rijndael.eK + (28 + keylen) - 4;

    /* apply the inverse MixColumn transform to all round keys but the first and the last: */
    /* copy first */
    *rk++ = *rrk++;
    *rk++ = *rrk++;
    *rk++ = *rrk++;
    *rk   = *rrk;
    rk -= 3; rrk -= 3;

    for (i = 1; i < skey->rijndael.Nr; i++) {
        rrk -= 4;
        rk  += 4;
        temp = rrk[0];
        rk[0] =
            Tks0[byte(temp, 3)] ^
            Tks1[byte(temp, 2)] ^
            Tks2[byte(temp, 1)] ^
            Tks3[byte(temp, 0)];
        temp = rrk[1];
        rk[1] =
            Tks0[byte(temp, 3)] ^
            Tks1[byte(temp, 2)] ^
            Tks2[byte(temp, 1)] ^
            Tks3[byte(temp, 0)];
        temp = rrk[2];
        rk[2] =
            Tks0[byte(temp, 3)] ^
            Tks1[byte(temp, 2)] ^
            Tks2[byte(temp, 1)] ^
            Tks3[byte(temp, 0)];
        temp = rrk[3];
        rk[3] =
            Tks0[byte(temp, 3)] ^
            Tks1[byte(temp, 2)] ^
            Tks2[byte(temp, 1)] ^
            Tks3[byte(temp, 0)];

    }

    /* copy last */
    rrk -= 4;
    rk  += 4;
    *rk++ = *rrk++;
    *rk++ = *rrk++;
    *rk++ = *rrk++;
    *rk   = *rrk;

    return CRYPT_OK;
}

/**
 * Encrypts a block of text with AES
 * @param pt The input plaintext (16 bytes)
 * @param ct The output ciphertext (16 bytes)
 * @param skey The key as scheduled
 * @return CRYPT_OK if successful
 *
 *  @uobjrtl_namespace{uberspark/uobjrtl/crypto}
 *
 * @headers_begin 
 * #include <uberspark/uobjrtl/crypto/include/ciphers/aes/aes.h>
 * @headers_end
 */
int uberspark_uobjrtl_crypto__ciphers_aes__rijndael_ecb_encrypt(const unsigned char *pt, unsigned char *ct, symmetric_key *skey)
{
    u32 s0, s1, s2, s3, t0, t1, t2, t3, *rk;
    int Nr, r;

    LTC_ARGCHK(pt != NULL);
    LTC_ARGCHK(ct != NULL);
    LTC_ARGCHK(skey != NULL);

    Nr = skey->rijndael.Nr;
    rk = skey->rijndael.eK;

    /*
     * map byte array block to cipher state
     * and add initial round key:
     */
    LOAD32H(s0, pt      ); s0 ^= rk[0];
    LOAD32H(s1, pt  +  4); s1 ^= rk[1];
    LOAD32H(s2, pt  +  8); s2 ^= rk[2];
    LOAD32H(s3, pt  + 12); s3 ^= rk[3];


    /*
     * Nr - 1 full rounds:
     */
    r = Nr >> 1;
    for (;;) {
        t0 =
            Te0(byte(s0, 3)) ^
            Te1(byte(s1, 2)) ^
            Te2(byte(s2, 1)) ^
            Te3(byte(s3, 0)) ^
            rk[4];
        t1 =
            Te0(byte(s1, 3)) ^
            Te1(byte(s2, 2)) ^
            Te2(byte(s3, 1)) ^
            Te3(byte(s0, 0)) ^
            rk[5];
        t2 =
            Te0(byte(s2, 3)) ^
            Te1(byte(s3, 2)) ^
            Te2(byte(s0, 1)) ^
            Te3(byte(s1, 0)) ^
            rk[6];
        t3 =
            Te0(byte(s3, 3)) ^
            Te1(byte(s0, 2)) ^
            Te2(byte(s1, 1)) ^
            Te3(byte(s2, 0)) ^
            rk[7];

        rk += 8;
        if (--r == 0) {
            break;
        }

        s0 =
            Te0(byte(t0, 3)) ^
            Te1(byte(t1, 2)) ^
            Te2(byte(t2, 1)) ^
            Te3(byte(t3, 0)) ^
            rk[0];
        s1 =
            Te0(byte(t1, 3)) ^
            Te1(byte(t2, 2)) ^
            Te2(byte(t3, 1)) ^
            Te3(byte(t0, 0)) ^
            rk[1];
        s2 =
            Te0(byte(t2, 3)) ^
            Te1(byte(t3, 2)) ^
            Te2(byte(t0, 1)) ^
            Te3(byte(t1, 0)) ^
            rk[2];
        s3 =
            Te0(byte(t3, 3)) ^
            Te1(byte(t0, 2)) ^
            Te2(byte(t1, 1)) ^
            Te3(byte(t2, 0)) ^
            rk[3];
    }


    /*
     * apply last round and
     * map cipher state to byte array block:
     */
    s0 =
        (Te4_3[byte(t0, 3)]) ^
        (Te4_2[byte(t1, 2)]) ^
        (Te4_1[byte(t2, 1)]) ^
        (Te4_0[byte(t3, 0)]) ^
        rk[0];
    STORE32H(s0, ct);
    s1 =
        (Te4_3[byte(t1, 3)]) ^
        (Te4_2[byte(t2, 2)]) ^
        (Te4_1[byte(t3, 1)]) ^
        (Te4_0[byte(t0, 0)]) ^
        rk[1];
    STORE32H(s1, ct+4);
    s2 =
        (Te4_3[byte(t2, 3)]) ^
        (Te4_2[byte(t3, 2)]) ^
        (Te4_1[byte(t0, 1)]) ^
        (Te4_0[byte(t1, 0)]) ^
        rk[2];
    STORE32H(s2, ct+8);
    s3 =
        (Te4_3[byte(t3, 3)]) ^
        (Te4_2[byte(t0, 2)]) ^
        (Te4_1[byte(t1, 1)]) ^
        (Te4_0[byte(t2, 0)]) ^
        rk[3];
    STORE32H(s3, ct+12);

    return CRYPT_OK;
}


/**
 * Decrypts a block of text with AES
 * @param ct The input ciphertext (16 bytes)
 * @param pt The output plaintext (16 bytes)
 * @param skey The key as scheduled
 * @return CRYPT_OK if successful
 *
 *  @uobjrtl_namespace{uberspark/uobjrtl/crypto}
 *
 * @headers_begin 
 * #include <uberspark/uobjrtl/crypto/include/ciphers/aes/aes.h>
 * @headers_end
 */
int uberspark_uobjrtl_crypto__ciphers_aes__rijndael_ecb_decrypt(const unsigned char *ct, unsigned char *pt, symmetric_key *skey)
{
    u32 s0, s1, s2, s3, t0, t1, t2, t3, *rk;
    int Nr, r;

    LTC_ARGCHK(pt != NULL);
    LTC_ARGCHK(ct != NULL);
    LTC_ARGCHK(skey != NULL);

    Nr = skey->rijndael.Nr;
    rk = skey->rijndael.dK;

    /*
     * map byte array block to cipher state
     * and add initial round key:
     */
    LOAD32H(s0, ct      ); s0 ^= rk[0];
    LOAD32H(s1, ct  +  4); s1 ^= rk[1];
    LOAD32H(s2, ct  +  8); s2 ^= rk[2];
    LOAD32H(s3, ct  + 12); s3 ^= rk[3];


    /*
     * Nr - 1 full rounds:
     */
    r = Nr >> 1;
    for (;;) {

        t0 =
            Td0(byte(s0, 3)) ^
            Td1(byte(s3, 2)) ^
            Td2(byte(s2, 1)) ^
            Td3(byte(s1, 0)) ^
            rk[4];
        t1 =
            Td0(byte(s1, 3)) ^
            Td1(byte(s0, 2)) ^
            Td2(byte(s3, 1)) ^
            Td3(byte(s2, 0)) ^
            rk[5];
        t2 =
            Td0(byte(s2, 3)) ^
            Td1(byte(s1, 2)) ^
            Td2(byte(s0, 1)) ^
            Td3(byte(s3, 0)) ^
            rk[6];
        t3 =
            Td0(byte(s3, 3)) ^
            Td1(byte(s2, 2)) ^
            Td2(byte(s1, 1)) ^
            Td3(byte(s0, 0)) ^
            rk[7];

        rk += 8;
        if (--r == 0) {
            break;
        }


        s0 =
            Td0(byte(t0, 3)) ^
            Td1(byte(t3, 2)) ^
            Td2(byte(t2, 1)) ^
            Td3(byte(t1, 0)) ^
            rk[0];
        s1 =
            Td0(byte(t1, 3)) ^
            Td1(byte(t0, 2)) ^
            Td2(byte(t3, 1)) ^
            Td3(byte(t2, 0)) ^
            rk[1];
        s2 =
            Td0(byte(t2, 3)) ^
            Td1(byte(t1, 2)) ^
            Td2(byte(t0, 1)) ^
            Td3(byte(t3, 0)) ^
            rk[2];
        s3 =
            Td0(byte(t3, 3)) ^
            Td1(byte(t2, 2)) ^
            Td2(byte(t1, 1)) ^
            Td3(byte(t0, 0)) ^
            rk[3];
    }

    /*
     * apply last round and
     * map cipher state to byte array block:
     */
    s0 =
        (Td4[byte(t0, 3)] & 0xff000000) ^
        (Td4[byte(t3, 2)] & 0x00ff0000) ^
        (Td4[byte(t2, 1)] & 0x0000ff00) ^
        (Td4[byte(t1, 0)] & 0x000000ff) ^
        rk[0];
    STORE32H(s0, pt);
    s1 =
        (Td4[byte(t1, 3)] & 0xff000000) ^
        (Td4[byte(t0, 2)] & 0x00ff0000) ^
        (Td4[byte(t3, 1)] & 0x0000ff00) ^
        (Td4[byte(t2, 0)] & 0x000000ff) ^
        rk[1];
    STORE32H(s1, pt+4);
    s2 =
        (Td4[byte(t2, 3)] & 0xff000000) ^
        (Td4[byte(t1, 2)] & 0x00ff0000) ^
        (Td4[byte(t0, 1)] & 0x0000ff00) ^
        (Td4[byte(t3, 0)] & 0x000000ff) ^
        rk[2];
    STORE32H(s2, pt+8);
    s3 =
        (Td4[byte(t3, 3)] & 0xff000000) ^
        (Td4[byte(t2, 2)] & 0x00ff0000) ^
        (Td4[byte(t1, 1)] & 0x0000ff00) ^
        (Td4[byte(t0, 0)] & 0x000000ff) ^
        rk[3];
    STORE32H(s3, pt+12);

    return CRYPT_OK;
}


/** 
 * Terminate the context
 * @param skey    The scheduled key
 *
 *  @uobjrtl_namespace{uberspark/uobjrtl/crypto}
 *
 * @headers_begin 
 * #include <uberspark/uobjrtl/crypto/include/ciphers/aes/aes.h>
 * @headers_end
 */
void uberspark_uobjrtl_crypto__ciphers_aes__rijndael_done(symmetric_key *skey)
{
  (void)skey;
}


/**
 * Gets suitable key size
 * @param keysize [in/out] The length of the recommended key (in bytes).  This function will store the suitable size back in this variable.
 * @return CRYPT_OK if the input key size is acceptable.
 *
 *  @uobjrtl_namespace{uberspark/uobjrtl/crypto}
 *
 * @headers_begin 
 * #include <uberspark/uobjrtl/crypto/include/ciphers/aes/aes.h>
 * @headers_end
 */
int uberspark_uobjrtl_crypto__ciphers_aes__rijndael_keysize(int *keysize)
{
   LTC_ARGCHK(keysize != NULL);

   if (*keysize < 16)
      return CRYPT_INVALID_KEYSIZE;
   if (*keysize < 24) {
      *keysize = 16;
      return CRYPT_OK;
   } else if (*keysize < 32) {
      *keysize = 24;
      return CRYPT_OK;
   } else {
      *keysize = 32;
      return CRYPT_OK;
   }
}




#if 0
/**
  Performs a self-test of the AES block cipher
  @return CRYPT_OK if functional, CRYPT_NOP if self-test has been disabled
*/
int uberspark_uobjrtl_crypto__ciphers_aes__rijndael_test(void)
{
 int err;
 static const struct {
     int keylen;
     unsigned char key[32], pt[16], ct[16];
 } tests[] = {
    { 16,
      { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f },
      { 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
        0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff },
      { 0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30,
        0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4, 0xc5, 0x5a }
    }, {
      24,
      { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17 },
      { 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
        0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff },
      { 0xdd, 0xa9, 0x7c, 0xa4, 0x86, 0x4c, 0xdf, 0xe0,
        0x6e, 0xaf, 0x70, 0xa0, 0xec, 0x0d, 0x71, 0x91 }
    }, {
      32,
      { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
        0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f },
      { 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
        0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff },
      { 0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf,
        0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49, 0x60, 0x89 }
    }
 };

  symmetric_key key;
  unsigned char tmp[2][16];
  int i, y;

  for (i = 0; i < (int)(sizeof(tests)/sizeof(tests[0])); i++) {
    XMEMSET((unsigned char *)&key, 0, sizeof(key));
    if ((err = uberspark_uobjrtl_crypto__ciphers_aes__rijndael_setup(tests[i].key, tests[i].keylen, 0, &key)) != CRYPT_OK) {
       return err;
    }

    uberspark_uobjrtl_crypto__ciphers_aes__rijndael_ecb_encrypt(tests[i].pt, tmp[0], &key);
    uberspark_uobjrtl_crypto__ciphers_aes__rijndael_ecb_decrypt(tmp[0], tmp[1], &key);
    if (XMEMCMP(tmp[0], tests[i].ct, 16) || XMEMCMP(tmp[1], tests[i].pt, 16)) {
        return CRYPT_FAIL_TESTVECTOR;
    }

    /* now see if we can encrypt all zero bytes 1000 times, decrypt and come back where we started */
    for (y = 0; y < 16; y++) tmp[0][y] = 0;
    for (y = 0; y < 1000; y++) uberspark_uobjrtl_crypto__ciphers_aes__rijndael_ecb_encrypt(tmp[0], tmp[0], &key);
    for (y = 0; y < 1000; y++) uberspark_uobjrtl_crypto__ciphers_aes__rijndael_ecb_decrypt(tmp[0], tmp[0], &key);
    for (y = 0; y < 16; y++) if (tmp[0][y] != 0) return CRYPT_FAIL_TESTVECTOR;
  }
  return CRYPT_OK;
}
#endif
