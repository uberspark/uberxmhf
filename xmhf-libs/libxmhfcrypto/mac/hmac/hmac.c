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

#undef DESC_DEF_ONLY
#define LTC_SOURCE

#include <xmhf.h>
#include <xmhfcrypto.h>

#define LTC_HMAC_BLOCKSIZE hash_descriptor[hash].blocksize

/**
   LTC_HMAC a block of memory to produce the authentication tag
   @param hash      The index of the hash to use 
   @param key       The secret key 
   @param keylen    The length of the secret key (octets)
   @param in        The data to LTC_HMAC
   @param inlen     The length of the data to LTC_HMAC (octets)
   @param out       [out] Destination of the authentication tag
   @param outlen    [in/out] Max size and resulting size of authentication tag
   @return CRYPT_OK if successful
*/
int hmac_memory(int hash, 
                const unsigned char *key,  unsigned long keylen,
                const unsigned char *in,   unsigned long inlen, 
                      unsigned char *out,  unsigned long *outlen)
{
    hmac_state *hmac;
    int         err;

    LTC_ARGCHK(key    != NULL);
    LTC_ARGCHK(in     != NULL);
    LTC_ARGCHK(out    != NULL); 
    LTC_ARGCHK(outlen != NULL);

    /* make sure hash descriptor is valid */
    if ((err = hash_is_valid(hash)) != CRYPT_OK) {
       return err;
    }

    /* is there a descriptor? */
    if (hash_descriptor[hash].hmac_block != NULL) {
        return hash_descriptor[hash].hmac_block(key, keylen, in, inlen, out, outlen);
    }

    /* nope, so call the hmac functions */
    /* allocate ram for hmac state */
    hmac = XMALLOC(sizeof(hmac_state));
    if (hmac == NULL) {
       return CRYPT_MEM;
    }

    if ((err = hmac_init(hmac, hash, key, keylen)) != CRYPT_OK) {
       goto LBL_ERR;
    }

    if ((err = hmac_process(hmac, in, inlen)) != CRYPT_OK) {
       goto LBL_ERR;
    }

    if ((err = hmac_done(hmac, out, outlen)) != CRYPT_OK) {
       goto LBL_ERR;
    }

   err = CRYPT_OK;
LBL_ERR:
   XFREE(hmac);
   return err;   
}


/**
   Initialize an LTC_HMAC context.
   @param hmac     The LTC_HMAC state 
   @param hash     The index of the hash you want to use 
   @param key      The secret key
   @param keylen   The length of the secret key (octets)
   @return CRYPT_OK if successful
*/
int hmac_init(hmac_state *hmac, int hash, const unsigned char *key, unsigned long keylen)
{
    unsigned char *buf;
    unsigned long hashsize;
    unsigned long i, z;
    int err;

    LTC_ARGCHK(hmac != NULL);
    LTC_ARGCHK(key  != NULL);

    /* valid hash? */
    if ((err = hash_is_valid(hash)) != CRYPT_OK) {
        return err;
    }
    hmac->hash = hash;
    hashsize   = hash_descriptor[hash].hashsize;

    /* valid key length? */
    if (keylen == 0) {
        return CRYPT_INVALID_KEYSIZE;
    }

    /* allocate ram for buf */
    buf = XMALLOC(LTC_HMAC_BLOCKSIZE);
    if (buf == NULL) {
       return CRYPT_MEM;
    }

    /* allocate memory for key */
    hmac->key = XMALLOC(LTC_HMAC_BLOCKSIZE);
    if (hmac->key == NULL) {
       XFREE(buf);
       return CRYPT_MEM;
    }

    /* (1) make sure we have a large enough key */
    if(keylen > LTC_HMAC_BLOCKSIZE) {
        z = LTC_HMAC_BLOCKSIZE;
        if ((err = hash_memory(hash, key, keylen, hmac->key, &z)) != CRYPT_OK) {
           goto LBL_ERR;
        }
        if(hashsize < LTC_HMAC_BLOCKSIZE) {
            zeromem((hmac->key) + hashsize, (size_t)(LTC_HMAC_BLOCKSIZE - hashsize));
        }
        keylen = hashsize;
    } else {
        XMEMCPY(hmac->key, key, (size_t)keylen);
        if(keylen < LTC_HMAC_BLOCKSIZE) {
            zeromem((hmac->key) + keylen, (size_t)(LTC_HMAC_BLOCKSIZE - keylen));
        }
    }

    /* Create the initial vector for step (3) */
    for(i=0; i < LTC_HMAC_BLOCKSIZE;   i++) {
       buf[i] = hmac->key[i] ^ 0x36;
    }

    /* Pre-pend that to the hash data */
    if ((err = hash_descriptor[hash].init(&hmac->md)) != CRYPT_OK) {
       goto LBL_ERR;
    }

    if ((err = hash_descriptor[hash].process(&hmac->md, buf, LTC_HMAC_BLOCKSIZE)) != CRYPT_OK) {
       goto LBL_ERR;
    }
    goto done;
LBL_ERR:
    /* free the key since we failed */
    XFREE(hmac->key);
done:
   XFREE(buf);
   return err;    
}

/** 
  Process data through LTC_HMAC
  @param hmac    The hmac state
  @param in      The data to send through LTC_HMAC
  @param inlen   The length of the data to LTC_HMAC (octets)
  @return CRYPT_OK if successful
*/
int hmac_process(hmac_state *hmac, const unsigned char *in, unsigned long inlen)
{
    int err;
    LTC_ARGCHK(hmac != NULL);
    LTC_ARGCHK(in != NULL);
    if ((err = hash_is_valid(hmac->hash)) != CRYPT_OK) {
        return err;
    }
    return hash_descriptor[hmac->hash].process(&hmac->md, in, inlen);
}



/**
   Terminate an LTC_HMAC session
   @param hmac    The LTC_HMAC state
   @param out     [out] The destination of the LTC_HMAC authentication tag
   @param outlen  [in/out]  The max size and resulting size of the LTC_HMAC authentication tag
   @return CRYPT_OK if successful
*/
int hmac_done(hmac_state *hmac, unsigned char *out, unsigned long *outlen)
{
    unsigned char *buf, *isha;
    unsigned long hashsize, i;
    int hash, err;

    LTC_ARGCHK(hmac  != NULL);
    LTC_ARGCHK(out   != NULL);

    /* test hash */
    hash = hmac->hash;
    if((err = hash_is_valid(hash)) != CRYPT_OK) {
        return err;
    }

    /* get the hash message digest size */
    hashsize = hash_descriptor[hash].hashsize;

    /* allocate buffers */
    buf  = XMALLOC(LTC_HMAC_BLOCKSIZE);
    isha = XMALLOC(hashsize);
    if (buf == NULL || isha == NULL) { 
       if (buf != NULL) {
          XFREE(buf);
       } 
       if (isha != NULL) {
          XFREE(isha);
       }  
       return CRYPT_MEM;
    }

    /* Get the hash of the first LTC_HMAC vector plus the data */
    if ((err = hash_descriptor[hash].done(&hmac->md, isha)) != CRYPT_OK) {
       goto LBL_ERR;
    }

    /* Create the second LTC_HMAC vector vector for step (3) */
    for(i=0; i < LTC_HMAC_BLOCKSIZE; i++) {
        buf[i] = hmac->key[i] ^ 0x5C;
    }

    /* Now calculate the "outer" hash for step (5), (6), and (7) */
    if ((err = hash_descriptor[hash].init(&hmac->md)) != CRYPT_OK) {
       goto LBL_ERR;
    }
    if ((err = hash_descriptor[hash].process(&hmac->md, buf, LTC_HMAC_BLOCKSIZE)) != CRYPT_OK) {
       goto LBL_ERR;
    }
    if ((err = hash_descriptor[hash].process(&hmac->md, isha, hashsize)) != CRYPT_OK) {
       goto LBL_ERR;
    }
    if ((err = hash_descriptor[hash].done(&hmac->md, buf)) != CRYPT_OK) {
       goto LBL_ERR;
    }

    /* copy to output  */
    for (i = 0; i < hashsize && i < *outlen; i++) {
        out[i] = buf[i];
    }
    *outlen = i;

    err = CRYPT_OK;
LBL_ERR:
    XFREE(hmac->key);
    XFREE(isha);
    XFREE(buf);

    return err;
}

/**
   LTC_HMAC multiple blocks of memory to produce the authentication tag
   @param hash      The index of the hash to use 
   @param key       The secret key 
   @param keylen    The length of the secret key (octets)
   @param out       [out] Destination of the authentication tag
   @param outlen    [in/out] Max size and resulting size of authentication tag
   @param in        The data to LTC_HMAC
   @param inlen     The length of the data to LTC_HMAC (octets)
   @param ...       tuples of (data,len) pairs to LTC_HMAC, terminated with a (NULL,x) (x=don't care)
   @return CRYPT_OK if successful
*/
int hmac_memory_multi(int hash, 
                const unsigned char *key,  unsigned long keylen,
                      unsigned char *out,  unsigned long *outlen,
                const unsigned char *in,   unsigned long inlen, ...)

{
    hmac_state          *hmac;
    int                  err;
    va_list              args;
    const unsigned char *curptr;
    unsigned long        curlen;

    LTC_ARGCHK(key    != NULL);
    LTC_ARGCHK(in     != NULL);
    LTC_ARGCHK(out    != NULL); 
    LTC_ARGCHK(outlen != NULL);

    /* allocate ram for hmac state */
    hmac = XMALLOC(sizeof(hmac_state));
    if (hmac == NULL) {
       return CRYPT_MEM;
    }

    if ((err = hmac_init(hmac, hash, key, keylen)) != CRYPT_OK) {
       goto LBL_ERR;
    }

    va_start(args, inlen);
    curptr = in; 
    curlen = inlen;
    for (;;) {
       /* process buf */
       if ((err = hmac_process(hmac, curptr, curlen)) != CRYPT_OK) {
          goto LBL_ERR;
       }
       /* step to next */
       curptr = va_arg(args, const unsigned char*);
       if (curptr == NULL) {
          break;
       }
       curlen = va_arg(args, unsigned long);
    }
    if ((err = hmac_done(hmac, out, outlen)) != CRYPT_OK) {
       goto LBL_ERR;
    }
LBL_ERR:
   XFREE(hmac);
   va_end(args);
   return err;   
}

