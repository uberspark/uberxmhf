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
#include <euchk.h>

#include <sha1.h> 

#define F0(x,y,z)  (z ^ (x & (y ^ z)))
#define F1(x,y,z)  (x ^ y ^ z)
#define F2(x,y,z)  ((x & y) | (z & (x | y)))
#define F3(x,y,z)  (x ^ y ^ z)

static int  sha1_compress(hash_state *md, unsigned char *buf)
{
    u32 a,b,c,d,e,W[80],i;
    u32 t;

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
       FF0(a,b,c,d,e,i++); t = e; e = d; d = c; c = b; b = a; a = t;
    }

    for (; i < 40; ) {
       FF1(a,b,c,d,e,i++); t = e; e = d; d = c; c = b; b = a; a = t;
    }

    for (; i < 60; ) {
       FF2(a,b,c,d,e,i++); t = e; e = d; d = c; c = b; b = a; a = t;
    }

    for (; i < 80; ) {
       FF3(a,b,c,d,e,i++); t = e; e = d; d = c; c = b; b = a; a = t;
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


int sha1_buffer(const unsigned char *buffer, size_t len,
                unsigned char md[SHA_DIGEST_LENGTH]){
  int rv=0;
  hash_state hs;
  
  EU_CHKN( rv = sha1_init( &hs));
  EU_CHKN( rv = sha1_process( &hs, buffer, len));
  EU_CHKN( rv = sha1_done( &hs, md));

 out:
  return rv;
}

void hashandprint(const char* prefix, const u8 *bytes, size_t len) {
    u8 digest[SHA_DIGEST_LENGTH];

    printf("\nhashandprint: processing 0x%08x bytes at addr 0x%08x", len, (u32)bytes);

    EU_VERIFYN( sha1_buffer(bytes, len, digest));

    printf("%s: %*D\n", prefix, SHA_DIGEST_LENGTH, digest, " ");
}

/**
   Initialize the hash state
   @param md   The hash state you wish to initialize
   @return CRYPT_OK if successful
*/
int sha1_init(hash_state * md)
{
   assert(md != NULL);
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
   Terminate the hash to get the digest
   @param md  The hash state
   @param out [out] The destination of the hash (20 bytes)
   @return CRYPT_OK if successful
*/
int sha1_done(hash_state * md, unsigned char *out)
{
    int i;

    assert(md  != NULL);
    assert(out != NULL);

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
        sha1_compress(md, md->sha1.buf);
        md->sha1.curlen = 0;
    }

    /* pad upto 56 bytes of zeroes */
    while (md->sha1.curlen < 56) {
        md->sha1.buf[md->sha1.curlen++] = (unsigned char)0;
    }

    /* store length */
    STORE64H(md->sha1.length, md->sha1.buf+56);
    sha1_compress(md, md->sha1.buf);

    /* copy output */
    for (i = 0; i < 5; i++) {
        STORE32H(md->sha1.state[i], out+(4*i));
    }

#ifdef LTC_CLEAN_STACK
    zeromem(md, sizeof(hash_state));
#endif

    return CRYPT_OK;
}


/**
  Self-test the hash
  @return CRYPT_OK if successful, CRYPT_NOP if self-tests have been disabled
*/  
int  sha1_test(void)
{
    return CRYPT_NOP;
 
}



/**
   Process a block of memory though the hash
   @param md     The hash state
   @param in     The data to hash
   @param inlen  The length of the data (octets)
   @return CRYPT_OK if successful
*/
HASH_PROCESS(sha1_process, sha1_compress, sha1, 64)

const struct ltc_hash_descriptor sha1_desc =
{
    "sha1",
    2,
    20,
    64,

    /* OID */
   { 1, 3, 14, 3, 2, 26,  },
   6,

    &sha1_init,
    &sha1_process,
    &sha1_done,
    &sha1_test,
    NULL
};
