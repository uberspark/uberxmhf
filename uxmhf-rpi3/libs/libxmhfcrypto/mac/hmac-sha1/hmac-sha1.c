/*
 * hmac-sha1 implementation
 * author: amit vasudevan (amitvasudevan@acm.org)
 * adapted from libtomcrypto
 */

#include <string.h>
#include <xmhfcrypto.h>
#include <sha1.h>
#include <hmac-sha1.h>


#define LTC_HMAC_SHA1_BLOCKSIZE 64

/**
   Initialize an HMAC context.
   @param hmac     The HMAC state
   @param hash     The index of the hash you want to use
   @param key      The secret key
   @param keylen   The length of the secret key (octets)
   @return CRYPT_OK if successful
*/
//int hmac_init(hmac_state *hmac, int hash, const unsigned char *key, unsigned long keylen)
int hmac_sha1_init(hmac_state *hmac, const unsigned char *key, unsigned long keylen)
{
    //unsigned char *buf;
	unsigned char buf[LTC_HMAC_SHA1_BLOCKSIZE];
    unsigned long hashsize;
    unsigned long i, z;
    int err;

    LTC_ARGCHK(hmac != NULL);
    LTC_ARGCHK(key  != NULL);

    /* valid hash? */
    //if ((err = hash_is_valid(hash)) != CRYPT_OK) {
    //    return err;
    //}
    //hmac->hash = hash;
    hmac->hash = 0;
    hashsize   = 20;

    /* valid key length? */
    if (keylen == 0) {
        return CRYPT_INVALID_KEYSIZE;
    }

    /* allocate ram for buf */
    //buf = XMALLOC(LTC_HMAC_BLOCKSIZE);
    //if (buf == NULL) {
    //   return CRYPT_MEM;
    //}

    /* allocate memory for key */
    //hmac->key = XMALLOC(LTC_HMAC_BLOCKSIZE);
    //if (hmac->key == NULL) {
    //   XFREE(buf);
    //   return CRYPT_MEM;
    //}

    /* (1) make sure we have a large enough key */
    if(keylen > LTC_HMAC_SHA1_BLOCKSIZE) {
        z = LTC_HMAC_SHA1_BLOCKSIZE;
        //if ((err = hash_memory(hash, key, keylen, hmac->key, &z)) != CRYPT_OK) {
        //   goto LBL_ERR;
        //}
        keylen = hashsize;
    } else {
        XMEMCPY(hmac->key, key, (size_t)keylen);
    }

    if(keylen < LTC_HMAC_SHA1_BLOCKSIZE) {
       //zeromem((hmac->key) + keylen, (size_t)(LTC_HMAC_BLOCKSIZE - keylen));
    	memset((hmac->key) + keylen, 0, (size_t)(LTC_HMAC_BLOCKSIZE - keylen));
    }

    /* Create the initial vector for step (3) */
    for(i=0; i < LTC_HMAC_SHA1_BLOCKSIZE;   i++) {
       buf[i] = hmac->key[i] ^ 0x36;
    }

    /* Pre-pend that to the hash data */
    if ((err = sha1_init(&hmac->md)) != CRYPT_OK) {
       goto LBL_ERR;
    }

    if ((err = sha1_process(&hmac->md, buf, LTC_HMAC_SHA1_BLOCKSIZE)) != CRYPT_OK) {
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
*/
int hmac_sha1_process(hmac_state *hmac, const unsigned char *in, unsigned long inlen)
{
    int err;
    LTC_ARGCHK(hmac != NULL);
    LTC_ARGCHK(in != NULL);
    //if ((err = hash_is_valid(hmac->hash)) != CRYPT_OK) {
    //    return err;
    //}
    return sha1_process(&hmac->md, in, inlen);
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
*/
//int hmac_memory(int hash,
//                const unsigned char *key,  unsigned long keylen,
//                const unsigned char *in,   unsigned long inlen,
//                      unsigned char *out,  unsigned long *outlen)
int hmac_sha1_memory(const unsigned char *key,  unsigned long keylen,
                const unsigned char *in,   unsigned long inlen,
                      unsigned char *out,  unsigned long *outlen)
{
    //hmac_state *hmac;
	hmac_state hmac;
    int         err;

    LTC_ARGCHK(key    != NULL);
    LTC_ARGCHK(in     != NULL);
    LTC_ARGCHK(out    != NULL);
    LTC_ARGCHK(outlen != NULL);

    /* make sure hash descriptor is valid */
    //if ((err = hash_is_valid(hash)) != CRYPT_OK) {
    //   return err;
    //}

    /* is there a descriptor? */
    //if (hash_descriptor[hash].hmac_block != NULL) {
    //    return hash_descriptor[hash].hmac_block(key, keylen, in, inlen, out, outlen);
    //}

    /* nope, so call the hmac functions */
    /* allocate ram for hmac state */
    //hmac = XMALLOC(sizeof(hmac_state));
    //if (hmac == NULL) {
    //   return CRYPT_MEM;
    //}

    if ((err = hmac_sha1_init(&hmac, key, keylen)) != CRYPT_OK) {
       goto LBL_ERR;
    }

    if ((err = hmac_sha1_process(&hmac, in, inlen)) != CRYPT_OK) {
       goto LBL_ERR;
    }

    if ((err = hmac_sha1_done(&hmac, out, outlen)) != CRYPT_OK) {
       goto LBL_ERR;
    }

   err = CRYPT_OK;
LBL_ERR:

   return err;
}
