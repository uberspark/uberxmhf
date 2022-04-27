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

/*
 * hmac-sha2 implementation
 * author: amit vasudevan (amitvasudevan@acm.org)
 *         matt mccormack (matthew.mccormack@live.com)
 * adapted from libtomcrypto
 */


#include <string.h>
#include <xmhfcrypto.h>
#include <sha256.h>
#include <hmac-sha256.h>


#define LTC_HMAC_SHA2_BLOCKSIZE 64

/**
   Initialize an HMAC context.
   @param hmac     The HMAC state
   @param hash     The index of the hash you want to use
   @param key      The secret key
   @param keylen   The length of the secret key (octets)
   @return CRYPT_OK if successful
**/
int hmac_sha256_init(hmac_state *hmac, const unsigned char *key, unsigned long keylen) {
    unsigned char buf[LTC_HMAC_SHA2_BLOCKSIZE];
    unsigned long hashsize;
    unsigned long i, z;
    int err;

    LTC_ARGCHK(hmac != NULL);
    LTC_ARGCHK(key  != NULL);

    hmac->hash = 0;
    hashsize   = 32;

    /* valid key length? */
    if (keylen == 0) {
        return CRYPT_INVALID_KEYSIZE;
    }

    /* (1) make sure we have a large enough key */
    if(keylen > LTC_HMAC_SHA2_BLOCKSIZE) {
        z = LTC_HMAC_SHA2_BLOCKSIZE;
        if ((err = sha256_memory(key, keylen, hmac->key, &z)) != CRYPT_OK) {
           goto LBL_ERR;
        }
        keylen = hashsize;
    } else {
        XMEMCPY(hmac->key, key, (size_t)keylen);
    }

    if(keylen < LTC_HMAC_SHA2_BLOCKSIZE) {
    	memset((hmac->key) + keylen, 0, (size_t)(LTC_HMAC_BLOCKSIZE - keylen));
    }

    /* Create the initial vector for step (3) */
    for(i=0; i < LTC_HMAC_SHA2_BLOCKSIZE;   i++) {
       buf[i] = hmac->key[i] ^ 0x36;
    }

    /* Pre-pend that to the hash data */
    if ((err = sha256_init(&hmac->md)) != CRYPT_OK) {
       goto LBL_ERR;
    }

    if ((err = sha256_process(&hmac->md, buf, LTC_HMAC_SHA2_BLOCKSIZE)) != CRYPT_OK) {
       goto LBL_ERR;
    }

    goto done;
LBL_ERR:
done:
   return err;
}


/**
  Process data through HMAC
  @param hmac    The hmac state
  @param in      The data to send through HMAC
  @param inlen   The length of the data to HMAC (octets)
  @return CRYPT_OK if successful
**/
int hmac_sha256_process(hmac_state *hmac, const unsigned char *in, unsigned long inlen) {
    LTC_ARGCHK(hmac != NULL);
    LTC_ARGCHK(in != NULL);
    return sha256_process(&hmac->md, in, inlen);
}


/**
   Terminate an HMAC session
   @param hmac    The HMAC state
   @param out     [out] The destination of the HMAC authentication tag
   @param outlen  [in/out]  The max size and resulting size of the HMAC 
                  authentication tag
   @return CRYPT_OK if successful
**/
int hmac_sha256_done(hmac_state *hmac, unsigned char *out, unsigned long *outlen) {
    unsigned char buf[LTC_HMAC_SHA2_BLOCKSIZE], isha[32];
    unsigned long hashsize, i;
    int err;

    LTC_ARGCHK(hmac  != NULL);
    LTC_ARGCHK(out   != NULL);

    /* get the hash message digest size */
    hashsize = 32;

    /* Get the hash of the first HMAC vector plus the data */
    if ((err = sha256_done(&hmac->md, isha)) != CRYPT_OK) {
       goto LBL_ERR;
    }

    /* Create the second HMAC vector vector for step (3) */
    for(i=0; i < LTC_HMAC_SHA2_BLOCKSIZE; i++) {
        buf[i] = hmac->key[i] ^ 0x5C;
    }

    /* Now calculate the "outer" hash for step (5), (6), and (7) */
    if ((err = sha256_init(&hmac->md)) != CRYPT_OK) { goto LBL_ERR; }
    if ((err = sha256_process(&hmac->md, buf, LTC_HMAC_SHA2_BLOCKSIZE)) != CRYPT_OK) { goto LBL_ERR; }
    if ((err = sha256_process(&hmac->md, isha, hashsize)) != CRYPT_OK) { goto LBL_ERR; }
    if ((err = sha256_done(&hmac->md, buf)) != CRYPT_OK) { goto LBL_ERR; }

    /* copy to output  */
    for (i = 0; i < hashsize && i < *outlen; i++) {
        out[i] = buf[i];
    }
    *outlen = i;

    err = CRYPT_OK;
LBL_ERR:
    return err;
}


/**
   HMAC a block of memory to produce the authentication tag
   @param hash      The index of the hash to use
   @param key       The secret key
   @param keylen    The length of the secret key (octets)
   @param in        The data to HMAC
   @param inlen     The length of the data to HMAC (octets)
   @param out       [out] Destination of the authentication tag
   @param outlen    [in/out] Max size and resulting size of authentication tag
   @return CRYPT_OK if successful
**/
int hmac_sha256_memory(const unsigned char *key,  unsigned long keylen,
                       const unsigned char *in,   unsigned long inlen,
                       unsigned char *out,  unsigned long *outlen) {
    hmac_state hmac;
    int         err;

    LTC_ARGCHK(key    != NULL);
    LTC_ARGCHK(in     != NULL);
    LTC_ARGCHK(out    != NULL);
    LTC_ARGCHK(outlen != NULL);

    if ((err = hmac_sha256_init(&hmac, key, keylen)) != CRYPT_OK) { goto LBL_ERR; }
    if ((err = hmac_sha256_process(&hmac, in, inlen)) != CRYPT_OK) { goto LBL_ERR; }
    if ((err = hmac_sha256_done(&hmac, out, outlen)) != CRYPT_OK) { goto LBL_ERR; }
    err = CRYPT_OK;
LBL_ERR:
   return err;
}
