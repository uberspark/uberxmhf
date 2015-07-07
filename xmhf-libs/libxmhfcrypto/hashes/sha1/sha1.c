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
#include <sha1.h>



#define F0(x,y,z)  (z ^ (x & (y ^ z)))
#define F1(x,y,z)  (x ^ y ^ z)
#define F2(x,y,z)  ((x & y) | (z & (x | y)))
#define F3(x,y,z)  (x ^ y ^ z)

#if 0
/*@
	requires \valid(md);
	requires \valid(((unsigned char*)buf)+(0..63));
	assigns md->sha1.state[0..4];
	ensures \result == CRYPT_OK;
@*/
static int  sha1_compress(hash_state *md, unsigned char *buf);
#endif // 0


#if 0
/*@
	requires \valid(md);
	requires \valid(((unsigned char*)buf)+(0..63));
	assigns md->sha1.state[0..4];
	ensures \result == CRYPT_OK;
@*/
static int  sha1_compress(hash_state *md, unsigned char *buf)
{
    u32 a,b,c,d,e,W[80],i;
    u32 t;

    /* copy the state into 512-bits into W[0..15] */
    	/*@
		loop invariant I2: 0 <= i <= 16;
		loop assigns W[0..15], i;
		loop variant 16 - i;
	@*/
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
    	/*@
		loop invariant I3: 16 <= i <= 80;
		loop assigns W[16..79], i;
		loop variant 80 - i;
	@*/
    for (i = 16; i < 80; i++) {
        W[i] = ROL(W[i-3] ^ W[i-8] ^ W[i-14] ^ W[i-16], 1);
    }



    /* compress */
    /* round one */
    #define FF0(a,b,c,d,e,i) e = (ROLc(a, 5) + F0(b,c,d) + e + W[i] + 0x5a827999UL); b = ROLc(b, 30);
    #define FF1(a,b,c,d,e,i) e = (ROLc(a, 5) + F1(b,c,d) + e + W[i] + 0x6ed9eba1UL); b = ROLc(b, 30);
    #define FF2(a,b,c,d,e,i) e = (ROLc(a, 5) + F2(b,c,d) + e + W[i] + 0x8f1bbcdcUL); b = ROLc(b, 30);
    #define FF3(a,b,c,d,e,i) e = (ROLc(a, 5) + F3(b,c,d) + e + W[i] + 0xca62c1d6UL); b = ROLc(b, 30);

    	/*@
		loop invariant I4: 0 <= i <= 20;
		loop assigns i,t,e,d,c,b,a;
		loop variant 20 - i;
	@*/
    for (i = 0; i < 20; ) {
       FF0(a,b,c,d,e,i++); t = e; e = d; d = c; c = b; b = a; a = t;
    }


    	/*@
		loop invariant I4: 20 <= i <= 40;
		loop assigns i,t,e,d,c,b,a;
		loop variant 40 - i;
	@*/


    for (; i < 40; ) {
       FF1(a,b,c,d,e,i++); t = e; e = d; d = c; c = b; b = a; a = t;
    }

    	/*@
		loop invariant I4: 40 <= i <= 60;
		loop assigns i,t,e,d,c,b,a;
		loop variant 60 - i;
	@*/
    for (; i < 60; ) {
       FF2(a,b,c,d,e,i++); t = e; e = d; d = c; c = b; b = a; a = t;
    }



    	/*@
		loop invariant I4: 60 <= i <= 80;
		loop assigns i,t,e,d,c,b,a;
		loop variant 80 - i;
	@*/

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
#endif // 0



#if 0
/*@
	requires len >= 0;
	requires \valid(((unsigned char*)buffer)+(0..len-1));
	requires \valid(((unsigned char*)&md)+(0..19));
	//TODO: assign md
@*/
int sha1(const unsigned char *buffer, size_t len,
                unsigned char md[SHA_DIGEST_LENGTH]){

	int rv=CRYPT_OK;
	hash_state hs;

	//sha1_init
	hs.sha1.state[0] = 0x67452301UL;
	hs.sha1.state[1] = 0xefcdab89UL;
	hs.sha1.state[2] = 0x98badcfeUL;
	hs.sha1.state[3] = 0x10325476UL;
	hs.sha1.state[4] = 0xc3d2e1f0UL;
	hs.sha1.curlen = 0;
	hs.sha1.length = 0;


#if 0
	//sha1_process
	{
		unsigned long n;
		int           err;
		const unsigned char *in = buffer;
		size_t inlen = len;

		if (hs.sha1.curlen > sizeof(hs.sha1.buf)) {
			return CRYPT_INVALID_ARG;
		}

		while (inlen > 0) {
			if (hs.sha1.curlen == 0 && inlen >= 64) {
			   if ((err = sha1_compress (&hs, (unsigned char *)in)) != CRYPT_OK) {
				return err;
			   }
			   hs.sha1.length += 64 * 8;
			   in             += 64;
			   inlen          -= 64;
			} else {
			   n = MIN(inlen, (64 - hs.sha1.curlen));
			   memcpy(hs.sha1.buf + hs.sha1.curlen, in, (size_t)n);
			   hs.sha1.curlen += n;
			   in             += n;
			   inlen          -= n;
			   if (hs.sha1.curlen == 64) {
			      if ((err = sha1_compress (&hs, (unsigned char *)hs.sha1.buf)) != CRYPT_OK) {
				 return err;
			      }
			      hs.sha1.length += 8*64;
			      hs.sha1.curlen = 0;
			   }
			}
		}
	}

	//sha1_done
	{
		int i;
		unsigned char *out = md;

		if (hs.sha1.curlen >= sizeof(hs.sha1.buf)) {
			return CRYPT_INVALID_ARG;
		}

		/* increase the length of the message */
		hs.sha1.length += hs.sha1.curlen * 8;

		/* append the '1' bit */
		hs.sha1.buf[hs.sha1.curlen++] = (unsigned char)0x80;

		/* if the length is currently above 56 bytes we append zeros
		* then compress.  Then we can fall back to padding zeros and length
		* encoding like normal.
		*/
		if (hs.sha1.curlen > 56) {
			while (hs.sha1.curlen < 64) {
				hs.sha1.buf[hs.sha1.curlen++] = (unsigned char)0;
			}
			sha1_compress(&hs, hs.sha1.buf);
			hs.sha1.curlen = 0;
		}

		/* pad upto 56 bytes of zeroes */
		while (hs.sha1.curlen < 56) {
			hs.sha1.buf[hs.sha1.curlen++] = (unsigned char)0;
		}

		/* store length */
		STORE64H(hs.sha1.length, hs.sha1.buf+56);
		sha1_compress(&hs, hs.sha1.buf);

		/* copy output */
		for (i = 0; i < 5; i++) {
			STORE32H(hs.sha1.state[i], out+(4*i));
		}

	}

#endif // 0

	return rv;
}


#endif // 0


/*@
	requires len >= 0;
	requires \valid(((unsigned char*)message)+(0..len-1));
	requires \valid(((unsigned char*)&md)+(0..19));
	//TODO: assign md
@*/
int sha1(const uint8_t *message, uint32_t len, unsigned char md[SHA_DIGEST_LENGTH]){
	hash_state hs;
	unsigned char *out = md;
	int rv=CRYPT_OK;
	uint32_t i;
	uint8_t block[64];
	uint32_t rem;

	//init
	hs.sha1.state[0] = 0x67452301UL;
	hs.sha1.state[1] = 0xefcdab89UL;
	hs.sha1.state[2] = 0x98badcfeUL;
	hs.sha1.state[3] = 0x10325476UL;
	hs.sha1.state[4] = 0xc3d2e1f0UL;
	hs.sha1.curlen = 0;
	hs.sha1.length = 0;

#if 0
	for (i = 0; len - i >= 64; i += 64)
		sha1_compress(&hs, message + i);

	rem = len - i;
	memcpy(block, message + i, rem);

	block[rem] = 0x80;
	rem++;
	if (64 - rem >= 8)
		memset(block + rem, 0, 56 - rem);
	else {
		memset(block + rem, 0, 64 - rem);
		sha1_compress(&hs, block);
		memset(block, 0, 56);
	}

	uint64_t longLen = ((uint64_t)len) << 3;
	for (i = 0; i < 8; i++)
		block[64 - 1 - i] = (uint8_t)(longLen >> (i * 8));
	sha1_compress(&hs, block);

	/* copy output */
	for (i = 0; i < 5; i++) {
		STORE32H(hs.sha1.state[i], out+(4*i));
	}
#endif

	return rv;
}




















