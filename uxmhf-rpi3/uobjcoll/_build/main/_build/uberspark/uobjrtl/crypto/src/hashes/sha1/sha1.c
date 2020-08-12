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


#include <uberspark/uobjrtl/crypto/include/hashes/sha1/sha1.h>

#define F0(x,y,z)  (z ^ (x & (y ^ z)))
#define F1(x,y,z)  (x ^ y ^ z)
#define F2(x,y,z)  ((x & y) | (z & (x | y)))
#define F3(x,y,z)  (x ^ y ^ z)


/**
 *  Perform a SHA-1 compression round
 *  @param md     The hash state
 *  @param buf    The data to hash
 *  @return CRYPT_OK 
 *
 *  @uobjrtl_namespace{uberspark/uobjrtl/crypto}
 * 
 * @headers_begin 
 * #include <uberspark/uobjrtl/crypto/include/hashes/sha1/sha1.h>
 * @headers_end
 */
int  uberspark_uobjrtl_crypto__hashes_sha1__sha1_compress(hash_state *md, unsigned char *buf)
{
    uint32_t a,b,c,d,e,W[80],i;

    /* copy the state into 512-bits into W[0..15] */
    for (i = 0; i < 16; i++) {
        LOAD32H(W[i], buf + (4*i));
    }

    /* copy state */
    a = md->sha1.state[0];
    b = md->sha1.state[1];
    c = md->sha1.state[2];
    d = md->sha1.state[3];
    e = md->sha1.state[4];

    /* expand it */
    for (i = 16; i < 80; i++) {
        W[i] = ROL(W[i-3] ^ W[i-8] ^ W[i-14] ^ W[i-16], 1);
    }

    /* compress */
    /* round one */
    #define FF0(a,b,c,d,e,i) e = (ROLc(a, 5) + F0(b,c,d) + e + W[i] + 0x5a827999UL); b = ROLc(b, 30);
    #define FF1(a,b,c,d,e,i) e = (ROLc(a, 5) + F1(b,c,d) + e + W[i] + 0x6ed9eba1UL); b = ROLc(b, 30);
    #define FF2(a,b,c,d,e,i) e = (ROLc(a, 5) + F2(b,c,d) + e + W[i] + 0x8f1bbcdcUL); b = ROLc(b, 30);
    #define FF3(a,b,c,d,e,i) e = (ROLc(a, 5) + F3(b,c,d) + e + W[i] + 0xca62c1d6UL); b = ROLc(b, 30);


    for (i = 0; i < 20; ) {
       FF0(a,b,c,d,e,i++);
       FF0(e,a,b,c,d,i++);
       FF0(d,e,a,b,c,i++);
       FF0(c,d,e,a,b,i++);
       FF0(b,c,d,e,a,i++);
    }

    /* round two */
    for (; i < 40; )  {
       FF1(a,b,c,d,e,i++);
       FF1(e,a,b,c,d,i++);
       FF1(d,e,a,b,c,i++);
       FF1(c,d,e,a,b,i++);
       FF1(b,c,d,e,a,i++);
    }

    /* round three */
    for (; i < 60; )  {
       FF2(a,b,c,d,e,i++);
       FF2(e,a,b,c,d,i++);
       FF2(d,e,a,b,c,i++);
       FF2(c,d,e,a,b,i++);
       FF2(b,c,d,e,a,i++);
    }

    /* round four */
    for (; i < 80; )  {
       FF3(a,b,c,d,e,i++);
       FF3(e,a,b,c,d,i++);
       FF3(d,e,a,b,c,i++);
       FF3(c,d,e,a,b,i++);
       FF3(b,c,d,e,a,i++);
    }

    #undef FF0
    #undef FF1
    #undef FF2
    #undef FF3

    /* store */
    md->sha1.state[0] = md->sha1.state[0] + a;
    md->sha1.state[1] = md->sha1.state[1] + b;
    md->sha1.state[2] = md->sha1.state[2] + c;
    md->sha1.state[3] = md->sha1.state[3] + d;
    md->sha1.state[4] = md->sha1.state[4] + e;

    return CRYPT_OK;
}


/**
 *  Initialize the hash state
 *  @param md   The hash state you wish to initialize
 *  @return CRYPT_OK if successful
 *
 *  @uobjrtl_namespace{uberspark/uobjrtl/crypto}
 * 
 * @headers_begin 
 * #include <uberspark/uobjrtl/crypto/include/hashes/sha1/sha1.h>
 * @headers_end
 */
int uberspark_uobjrtl_crypto__hashes_sha1__sha1_init(hash_state * md)
{
   LTC_ARGCHK(md != NULL);
   md->sha1.state[0] = 0x67452301UL;
   md->sha1.state[1] = 0xefcdab89UL;
   md->sha1.state[2] = 0x98badcfeUL;
   md->sha1.state[3] = 0x10325476UL;
   md->sha1.state[4] = 0xc3d2e1f0UL;
   md->sha1.curlen = 0;
   md->sha1.length = 0;
   return CRYPT_OK;
}

/**
 *  Process a block of memory though the hash
 *  @param md     The hash state
 *  @param in     The data to hash
 *  @param inlen  The length of the data (octets)
 *  @return CRYPT_OK if successful
 *
 *  @uobjrtl_namespace{uberspark/uobjrtl/crypto}
 *
 * @headers_begin 
 * #include <uberspark/uobjrtl/crypto/include/hashes/sha1/sha1.h>
 * @headers_end
 */
int uberspark_uobjrtl_crypto__hashes_sha1__sha1_process (hash_state * md, const unsigned char *in, unsigned long inlen)
{
    unsigned long n;
    int           err;
    LTC_ARGCHK(md != NULL);
    LTC_ARGCHK(in != NULL);
    if (md-> sha1 .curlen > sizeof(md-> sha1 .buf)) {
       return CRYPT_INVALID_ARG;
    }
    if ((md-> sha1 .length + inlen) < md-> sha1 .length) {
      return CRYPT_HASH_OVERFLOW;
    }
    while (inlen > 0) {
        if (md-> sha1 .curlen == 0 && inlen >= 64) {
           if ((err = uberspark_uobjrtl_crypto__hashes_sha1__sha1_compress (md, (unsigned char *)in)) != CRYPT_OK) {
              return err;
           }
           md-> sha1 .length += 64 * 8;
           in             += 64;
           inlen          -= 64;
        } else {
           n = MIN(inlen, (64 - md-> sha1 .curlen));
           XMEMCPY(md-> sha1 .buf + md-> sha1.curlen, in, (size_t)n);
           md-> sha1 .curlen += n;
           in             += n;
           inlen          -= n;
           if (md-> sha1 .curlen == 64) {
              if ((err = uberspark_uobjrtl_crypto__hashes_sha1__sha1_compress (md, md-> sha1 .buf)) != CRYPT_OK) {
                 return err;
              }
              md-> sha1 .length += 8*64;
              md-> sha1 .curlen = 0;
           }
       }
    }
    return CRYPT_OK;
}


/**
 *  Terminate the hash to get the digest
 *  @param md  The hash state
 *  @param out [out] The destination of the hash (20 bytes)
 *  @return CRYPT_OK if successful
 *
 *  @uobjrtl_namespace{uberspark/uobjrtl/crypto}
 *
 * @headers_begin 
 * #include <uberspark/uobjrtl/crypto/include/hashes/sha1/sha1.h>
 * @headers_end
 */
int uberspark_uobjrtl_crypto__hashes_sha1__sha1_done(hash_state * md, unsigned char *out)
{
    int i;

    LTC_ARGCHK(md  != NULL);
    LTC_ARGCHK(out != NULL);

    if (md->sha1.curlen >= sizeof(md->sha1.buf)) {
       return CRYPT_INVALID_ARG;
    }

    /* increase the length of the message */
    md->sha1.length += md->sha1.curlen * 8;

    /* append the '1' bit */
    md->sha1.buf[md->sha1.curlen++] = (unsigned char)0x80;

    /* if the length is currently above 56 bytes we append zeros
     * then compress.  Then we can fall back to padding zeros and length
     * encoding like normal.
     */
    if (md->sha1.curlen > 56) {
        while (md->sha1.curlen < 64) {
            md->sha1.buf[md->sha1.curlen++] = (unsigned char)0;
        }
        uberspark_uobjrtl_crypto__hashes_sha1__sha1_compress(md, md->sha1.buf);
        md->sha1.curlen = 0;
    }

    /* pad upto 56 bytes of zeroes */
    while (md->sha1.curlen < 56) {
        md->sha1.buf[md->sha1.curlen++] = (unsigned char)0;
    }

    /* store length */
    STORE64H(md->sha1.length, md->sha1.buf+56);
    uberspark_uobjrtl_crypto__hashes_sha1__sha1_compress(md, md->sha1.buf);

    /* copy output */
    for (i = 0; i < 5; i++) {
        STORE32H(md->sha1.state[i], out+(4*i));
    }

    return CRYPT_OK;
}



/**
 * Hash a block of memory and store the digest.
 * @param in     The data you wish to hash
 * @param inlen  The length of the data to hash (octets)
 * @param out    [out] Where to store the digest
 * @param outlen [in/out] Max size and resulting size of the digest
 * @return CRYPT_OK if successful
 *
 *  @uobjrtl_namespace{uberspark/uobjrtl/crypto}
 *
 * @headers_begin 
 * #include <uberspark/uobjrtl/crypto/include/hashes/sha1/sha1.h>
 * @headers_end
 */
//int hash_memory(int hash, const unsigned char *in, unsigned long inlen, unsigned char *out, unsigned long *outlen)
int uberspark_uobjrtl_crypto__hashes_sha1__sha1_memory(const unsigned char *in, unsigned long inlen, unsigned char *out, unsigned long *outlen)
{
    //hash_state *md;
	hash_state md;
    int err;

    LTC_ARGCHK(in     != NULL);
    LTC_ARGCHK(out    != NULL);
    LTC_ARGCHK(outlen != NULL);

    //if ((err = hash_is_valid(hash)) != CRYPT_OK) {
    //    return err;
    //}

    if (*outlen < 20) {
       *outlen = 20;
       return CRYPT_BUFFER_OVERFLOW;
    }

    //md = XMALLOC(sizeof(hash_state));
    //if (md == NULL) {
    //   return CRYPT_MEM;
    //}

    if ((err = uberspark_uobjrtl_crypto__hashes_sha1__sha1_init(&md)) != CRYPT_OK) {
       goto LBL_ERR;
    }
    if ((err = uberspark_uobjrtl_crypto__hashes_sha1__sha1_process(&md, in, inlen)) != CRYPT_OK) {
       goto LBL_ERR;
    }
    err = uberspark_uobjrtl_crypto__hashes_sha1__sha1_done(&md, out);
    *outlen = 20;
LBL_ERR:

    return err;
}




/**
 * Hash multiple (non-adjacent) blocks of memory at once.
 * @param out    [out] Where to store the digest
 * @param outlen [in/out] Max size and resulting size of the digest
 * @param in     The data you wish to hash
 * @param inlen  The length of the data to hash (octets)
 * @param ...    tuples of (data,len) pairs to hash, terminated with a (NULL,x) (x=don't care)
 * @return CRYPT_OK if successful
 *
 *  @uobjrtl_namespace{uberspark/uobjrtl/crypto}
 *
 * @headers_begin 
 * #include <uberspark/uobjrtl/crypto/include/hashes/sha1/sha1.h>
 * @headers_end
 */
int uberspark_uobjrtl_crypto__hashes_sha1__sha1_memory_multi(unsigned char *out, unsigned long *outlen,
                      const unsigned char *in, unsigned long inlen, ...)
{
    //hash_state          *md;
    hash_state          md;
    int                  err;
    va_list              args;
    const unsigned char *curptr;
    unsigned long        curlen;

    LTC_ARGCHK(in     != NULL);
    LTC_ARGCHK(out    != NULL);
    LTC_ARGCHK(outlen != NULL);

    //if ((err = hash_is_valid(hash)) != CRYPT_OK) {
    //    return err;
    //}

    if (*outlen < 20) {
       *outlen = 20;
       return CRYPT_BUFFER_OVERFLOW;
    }

    //md = XMALLOC(sizeof(hash_state));
    //if (md == NULL) {
    //   return CRYPT_MEM;
    //}

    if ((err = uberspark_uobjrtl_crypto__hashes_sha1__sha1_init(&md)) != CRYPT_OK) {
       goto LBL_ERR;
    }

    va_start(args, inlen);
    curptr = in;
    curlen = inlen;
    for (;;) {
       /* process buf */
       if ((err = uberspark_uobjrtl_crypto__hashes_sha1__sha1_process(&md, curptr, curlen)) != CRYPT_OK) {
          goto LBL_ERR;
       }
       /* step to next */
       curptr = va_arg(args, const unsigned char*);
       if (curptr == NULL) {
          break;
       }
       curlen = va_arg(args, unsigned long);
    }
    err = uberspark_uobjrtl_crypto__hashes_sha1__sha1_done(&md, out);
    *outlen = 20;
LBL_ERR:
    //XFREE(md);
    va_end(args);
    return err;
}


#if 0
/**
  Self-test the hash
  @return CRYPT_OK if successful, CRYPT_NOP if self-tests have been disabled
*/
int  uberspark_uobjrtl_crypto__hashes_sha1__sha1_test(void)
{
  static const struct {
      char *msg;
      unsigned char hash[20];
  } tests[] = {
    { "abc",
      { 0xa9, 0x99, 0x3e, 0x36, 0x47, 0x06, 0x81, 0x6a,
        0xba, 0x3e, 0x25, 0x71, 0x78, 0x50, 0xc2, 0x6c,
        0x9c, 0xd0, 0xd8, 0x9d }
    },
    { "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
      { 0x84, 0x98, 0x3E, 0x44, 0x1C, 0x3B, 0xD2, 0x6E,
        0xBA, 0xAE, 0x4A, 0xA1, 0xF9, 0x51, 0x29, 0xE5,
        0xE5, 0x46, 0x70, 0xF1 }
    }
  };

  int i;
  unsigned char tmp[20];
  hash_state md;

  for (i = 0; i < (int)(sizeof(tests) / sizeof(tests[0]));  i++) {
      uberspark_uobjrtl_crypto__hashes_sha1__sha1_init(&md);
      uberspark_uobjrtl_crypto__hashes_sha1__sha1_process(&md, (unsigned char*)tests[i].msg, (unsigned long)XSTRLEN(tests[i].msg));
      uberspark_uobjrtl_crypto__hashes_sha1__sha1_done(&md, tmp);
      //if (compare_testvector(tmp, sizeof(tmp), tests[i].hash, sizeof(tests[i].hash), "SHA1", i)) {
      //   return CRYPT_FAIL_TESTVECTOR;
      //}
  }
  return CRYPT_OK;
}
#endif
