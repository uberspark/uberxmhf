/*
 * hmac-sha1 implementation
 * author: amit vasudevan (amitvasudevan@acm.org)
 * adapted from libtomcrypto
 */

#include <string.h>
#include <xmhfcrypto.h>
#include <hmac-sha1.h>


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
