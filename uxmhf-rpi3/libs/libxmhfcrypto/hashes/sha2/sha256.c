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
 *         Matt McCormack (matthew.mccormack@live.com)
 *
 */

#include <string.h>
#include <xmhfcrypto.h>
#include <sha256.h>

/* Various logical functions */
#define Ch(x,y,z)       (z ^ (x & (y ^ z)))
#define Maj(x,y,z)      (((x | y) & z) | (x & y))
#define S(x, n)         RORc((x),(n))
#define R(x, n)         (((x)&0xFFFFFFFFUL)>>(n))
#define Sigma0(x)       (S(x, 2) ^ S(x, 13) ^ S(x, 22))
#define Sigma1(x)       (S(x, 6) ^ S(x, 11) ^ S(x, 25))
#define Gamma0(x)       (S(x, 7) ^ S(x, 18) ^ R(x, 3))
#define Gamma1(x)       (S(x, 17) ^ S(x, 19) ^ R(x, 10))


int sha256_compress(hash_state * md, const unsigned char *buf) {
  uint32_t S[8], W[64], t0, t1;
  int i;

  /* copy state into S */
  for (i = 0; i < 8; i++) {
      S[i] = md->sha256.state[i];
  }

  /* copy the state into 512-bits into W[0..15] */
  for (i = 0; i < 16; i++) {
      LOAD32H(W[i], buf + (4*i));
  }

  /* fill W[16..63] */
  for (i = 16; i < 64; i++) {
      W[i] = Gamma1(W[i - 2]) + W[i - 7] + Gamma0(W[i - 15]) + W[i - 16];
  }

  #define RND(a,b,c,d,e,f,g,h,i,ki)                    \
     t0 = h + Sigma1(e) + Ch(e, f, g) + ki + W[i];   \
     t1 = Sigma0(a) + Maj(a, b, c);                  \
     d += t0;                                        \
     h  = t0 + t1;

  RND(S[0],S[1],S[2],S[3],S[4],S[5],S[6],S[7],0,0x428a2f98);
  RND(S[7],S[0],S[1],S[2],S[3],S[4],S[5],S[6],1,0x71374491);
  RND(S[6],S[7],S[0],S[1],S[2],S[3],S[4],S[5],2,0xb5c0fbcf);
  RND(S[5],S[6],S[7],S[0],S[1],S[2],S[3],S[4],3,0xe9b5dba5);
  RND(S[4],S[5],S[6],S[7],S[0],S[1],S[2],S[3],4,0x3956c25b);
  RND(S[3],S[4],S[5],S[6],S[7],S[0],S[1],S[2],5,0x59f111f1);
  RND(S[2],S[3],S[4],S[5],S[6],S[7],S[0],S[1],6,0x923f82a4);
  RND(S[1],S[2],S[3],S[4],S[5],S[6],S[7],S[0],7,0xab1c5ed5);
  RND(S[0],S[1],S[2],S[3],S[4],S[5],S[6],S[7],8,0xd807aa98);
  RND(S[7],S[0],S[1],S[2],S[3],S[4],S[5],S[6],9,0x12835b01);
  RND(S[6],S[7],S[0],S[1],S[2],S[3],S[4],S[5],10,0x243185be);
  RND(S[5],S[6],S[7],S[0],S[1],S[2],S[3],S[4],11,0x550c7dc3);
  RND(S[4],S[5],S[6],S[7],S[0],S[1],S[2],S[3],12,0x72be5d74);
  RND(S[3],S[4],S[5],S[6],S[7],S[0],S[1],S[2],13,0x80deb1fe);
  RND(S[2],S[3],S[4],S[5],S[6],S[7],S[0],S[1],14,0x9bdc06a7);
  RND(S[1],S[2],S[3],S[4],S[5],S[6],S[7],S[0],15,0xc19bf174);
  RND(S[0],S[1],S[2],S[3],S[4],S[5],S[6],S[7],16,0xe49b69c1);
  RND(S[7],S[0],S[1],S[2],S[3],S[4],S[5],S[6],17,0xefbe4786);
  RND(S[6],S[7],S[0],S[1],S[2],S[3],S[4],S[5],18,0x0fc19dc6);
  RND(S[5],S[6],S[7],S[0],S[1],S[2],S[3],S[4],19,0x240ca1cc);
  RND(S[4],S[5],S[6],S[7],S[0],S[1],S[2],S[3],20,0x2de92c6f);
  RND(S[3],S[4],S[5],S[6],S[7],S[0],S[1],S[2],21,0x4a7484aa);
  RND(S[2],S[3],S[4],S[5],S[6],S[7],S[0],S[1],22,0x5cb0a9dc);
  RND(S[1],S[2],S[3],S[4],S[5],S[6],S[7],S[0],23,0x76f988da);
  RND(S[0],S[1],S[2],S[3],S[4],S[5],S[6],S[7],24,0x983e5152);
  RND(S[7],S[0],S[1],S[2],S[3],S[4],S[5],S[6],25,0xa831c66d);
  RND(S[6],S[7],S[0],S[1],S[2],S[3],S[4],S[5],26,0xb00327c8);
  RND(S[5],S[6],S[7],S[0],S[1],S[2],S[3],S[4],27,0xbf597fc7);
  RND(S[4],S[5],S[6],S[7],S[0],S[1],S[2],S[3],28,0xc6e00bf3);
  RND(S[3],S[4],S[5],S[6],S[7],S[0],S[1],S[2],29,0xd5a79147);
  RND(S[2],S[3],S[4],S[5],S[6],S[7],S[0],S[1],30,0x06ca6351);
  RND(S[1],S[2],S[3],S[4],S[5],S[6],S[7],S[0],31,0x14292967);
  RND(S[0],S[1],S[2],S[3],S[4],S[5],S[6],S[7],32,0x27b70a85);
  RND(S[7],S[0],S[1],S[2],S[3],S[4],S[5],S[6],33,0x2e1b2138);
  RND(S[6],S[7],S[0],S[1],S[2],S[3],S[4],S[5],34,0x4d2c6dfc);
  RND(S[5],S[6],S[7],S[0],S[1],S[2],S[3],S[4],35,0x53380d13);
  RND(S[4],S[5],S[6],S[7],S[0],S[1],S[2],S[3],36,0x650a7354);
  RND(S[3],S[4],S[5],S[6],S[7],S[0],S[1],S[2],37,0x766a0abb);
  RND(S[2],S[3],S[4],S[5],S[6],S[7],S[0],S[1],38,0x81c2c92e);
  RND(S[1],S[2],S[3],S[4],S[5],S[6],S[7],S[0],39,0x92722c85);
  RND(S[0],S[1],S[2],S[3],S[4],S[5],S[6],S[7],40,0xa2bfe8a1);
  RND(S[7],S[0],S[1],S[2],S[3],S[4],S[5],S[6],41,0xa81a664b);
  RND(S[6],S[7],S[0],S[1],S[2],S[3],S[4],S[5],42,0xc24b8b70);
  RND(S[5],S[6],S[7],S[0],S[1],S[2],S[3],S[4],43,0xc76c51a3);
  RND(S[4],S[5],S[6],S[7],S[0],S[1],S[2],S[3],44,0xd192e819);
  RND(S[3],S[4],S[5],S[6],S[7],S[0],S[1],S[2],45,0xd6990624);
  RND(S[2],S[3],S[4],S[5],S[6],S[7],S[0],S[1],46,0xf40e3585);
  RND(S[1],S[2],S[3],S[4],S[5],S[6],S[7],S[0],47,0x106aa070);
  RND(S[0],S[1],S[2],S[3],S[4],S[5],S[6],S[7],48,0x19a4c116);
  RND(S[7],S[0],S[1],S[2],S[3],S[4],S[5],S[6],49,0x1e376c08);
  RND(S[6],S[7],S[0],S[1],S[2],S[3],S[4],S[5],50,0x2748774c);
  RND(S[5],S[6],S[7],S[0],S[1],S[2],S[3],S[4],51,0x34b0bcb5);
  RND(S[4],S[5],S[6],S[7],S[0],S[1],S[2],S[3],52,0x391c0cb3);
  RND(S[3],S[4],S[5],S[6],S[7],S[0],S[1],S[2],53,0x4ed8aa4a);
  RND(S[2],S[3],S[4],S[5],S[6],S[7],S[0],S[1],54,0x5b9cca4f);
  RND(S[1],S[2],S[3],S[4],S[5],S[6],S[7],S[0],55,0x682e6ff3);
  RND(S[0],S[1],S[2],S[3],S[4],S[5],S[6],S[7],56,0x748f82ee);
  RND(S[7],S[0],S[1],S[2],S[3],S[4],S[5],S[6],57,0x78a5636f);
  RND(S[6],S[7],S[0],S[1],S[2],S[3],S[4],S[5],58,0x84c87814);
  RND(S[5],S[6],S[7],S[0],S[1],S[2],S[3],S[4],59,0x8cc70208);
  RND(S[4],S[5],S[6],S[7],S[0],S[1],S[2],S[3],60,0x90befffa);
  RND(S[3],S[4],S[5],S[6],S[7],S[0],S[1],S[2],61,0xa4506ceb);
  RND(S[2],S[3],S[4],S[5],S[6],S[7],S[0],S[1],62,0xbef9a3f7);
  RND(S[1],S[2],S[3],S[4],S[5],S[6],S[7],S[0],63,0xc67178f2);

  #undef RND

  /* feedback */
  for (i = 0; i < 8; i++) {
    md->sha256.state[i] = md->sha256.state[i] + S[i];
  }
  return CRYPT_OK;
}

/**
   Initialize the hash state
   @param md   The hash state you wish to initialize
   @return CRYPT_OK if successful
*/
int sha256_init(hash_state * md) {
  LTC_ARGCHK(md != NULL);

  md->sha256.curlen = 0;
  md->sha256.length = 0;
  md->sha256.state[0] = 0x6A09E667UL;
  md->sha256.state[1] = 0xBB67AE85UL;
  md->sha256.state[2] = 0x3C6EF372UL;
  md->sha256.state[3] = 0xA54FF53AUL;
  md->sha256.state[4] = 0x510E527FUL;
  md->sha256.state[5] = 0x9B05688CUL;
  md->sha256.state[6] = 0x1F83D9ABUL;
  md->sha256.state[7] = 0x5BE0CD19UL;
  return CRYPT_OK;
}

/**
   Process a block of memory though the hash
   @param md     The hash state
   @param in     The data to hash
   @param inlen  The length of the data (octets)
   @return CRYPT_OK if successful
*/
int sha256_process (hash_state * md, const unsigned char *in,
		    unsigned long inlen) {
  unsigned long n;
  int           err;
  LTC_ARGCHK(md != NULL);
  LTC_ARGCHK(in != NULL);
  if (md->sha256.curlen > sizeof(md->sha256.buf)) {
    return CRYPT_INVALID_ARG;
  }
  if ((md->sha256.length + inlen) < md->sha256.length) {
    return CRYPT_HASH_OVERFLOW;
  }
  while (inlen > 0) {
    if (md->sha256.curlen == 0 && inlen >= 64) {
      if ((err = sha256_compress (md, (unsigned char *)in)) != CRYPT_OK) {
	return err;
      }
      md->sha256.length += 64 * 8;
      in                += 64;
      inlen             -= 64;
    } else {
      n = MIN(inlen, (64 - md-> sha256.curlen));
      XMEMCPY(md->sha256.buf + md->sha256.curlen, in, (size_t)n);
      md->sha256.curlen += n;
      in                += n;
      inlen             -= n;
      if (md->sha256.curlen == 64) {
	if ((err = sha256_compress (md, md->sha256.buf)) != CRYPT_OK) {
	  return err;
	}
	md->sha256.length += 8*64;
	md->sha256.curlen = 0;
      }
    }
  }
  return CRYPT_OK;
}

/**
   Terminate the hash to get the digest
   @param md  The hash state
   @param out [out] The destination of the hash (32 bytes)
   @return CRYPT_OK if successful
*/
int sha256_done(hash_state * md, unsigned char *out) {
  int i;

  LTC_ARGCHK(md  != NULL);
  LTC_ARGCHK(out != NULL);

  if (md->sha256.curlen >= sizeof(md->sha256.buf)) {
    return CRYPT_INVALID_ARG;
  }

  /* increase the length of the message */
  md->sha256.length += md->sha256.curlen * 8;

  /* append the '1' bit */
  md->sha256.buf[md->sha256.curlen++] = (unsigned char)0x80;

  /* if the length is currently above 56 bytes we append zeros
   * then compress.  Then we can fall back to padding zeros and length
   * encoding like normal.
   */
  if (md->sha256.curlen > 56) {
    while (md->sha256.curlen < 64) {
      md->sha256.buf[md->sha256.curlen++] = (unsigned char)0;
    }
    sha256_compress(md, md->sha256.buf);
    md->sha256.curlen = 0;
  }

  /* pad upto 56 bytes of zeroes */
  while (md->sha256.curlen < 56) {
    md->sha256.buf[md->sha256.curlen++] = (unsigned char)0;
  }

  /* store length */
  STORE64H(md->sha256.length, md->sha256.buf+56);
  sha256_compress(md, md->sha256.buf);

  /* copy output */
  for (i = 0; i < 8; i++) {
    STORE32H(md->sha256.state[i], out+(4*i));
  }
  return CRYPT_OK;
}

/**
  Self-test the hash
  @return CRYPT_OK if successful, CRYPT_NOP if self-tests have been disabled
*/
int sha256_test(void) {
  static const struct {
    const char *msg;
    unsigned char hash[32];
  } tests[] = {
    { "abc",
      { 0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
        0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
        0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
        0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad }
    },
    { "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
      { 0x24, 0x8d, 0x6a, 0x61, 0xd2, 0x06, 0x38, 0xb8,
        0xe5, 0xc0, 0x26, 0x93, 0x0c, 0x3e, 0x60, 0x39,
        0xa3, 0x3c, 0xe4, 0x59, 0x64, 0xff, 0x21, 0x67,
        0xf6, 0xec, 0xed, 0xd4, 0x19, 0xdb, 0x06, 0xc1 }
    },
  };
  
  int i;
  unsigned char tmp[32];
  hash_state md;

  for (i = 0; i < (int)(sizeof(tests) / sizeof(tests[0])); i++) {
    sha256_init(&md);
    sha256_process(&md, (unsigned char*)tests[i].msg, (unsigned long)strlen(tests[i].msg));
    sha256_done(&md, tmp);
  }
  return CRYPT_OK;
}

/**
  Hash a block of memory and store the digest.
  @param hash   The index of the hash you wish to use
  @param in     The data you wish to hash
  @param inlen  The length of the data to hash (octets)
  @param out    [out] Where to store the digest
  @param outlen [in/out] Max size and resulting size of the digest
  @return CRYPT_OK if successful
*/
//int hash_memory(int hash, const unsigned char *in, unsigned long inlen, unsigned char *out, unsigned long *outlen)
int sha256_memory(const unsigned char *in, unsigned long inlen,
		  unsigned char *out, unsigned long *outlen) {
  hash_state md;
  int err;

  LTC_ARGCHK(in     != NULL);
  LTC_ARGCHK(out    != NULL);
  LTC_ARGCHK(outlen != NULL);

  if (*outlen < 32) {
    *outlen = 32;
    return CRYPT_BUFFER_OVERFLOW;
  }

  if ((err = sha256_init(&md)) != CRYPT_OK) {
    goto LBL_ERR;
  }
  if ((err = sha256_process(&md, in, inlen)) != CRYPT_OK) {
    goto LBL_ERR;
  }
  err = sha256_done(&md, out);
  *outlen = 32;
LBL_ERR:

  return err;
}

/**
  Hash multiple (non-adjacent) blocks of memory at once.
  @param hash   The index of the hash you wish to use
  @param out    [out] Where to store the digest
  @param outlen [in/out] Max size and resulting size of the digest
  @param in     The data you wish to hash
  @param inlen  The length of the data to hash (octets)
  @param ...    tuples of (data,len) pairs to hash, terminated with a (NULL,x) (x=don't care)
  @return CRYPT_OK if successful
*/
int sha256_memory_multi(unsigned char *out, unsigned long *outlen,
                        const unsigned char *in, unsigned long inlen, ...) {
  hash_state           md;
  int                  err;
  va_list              args;
  const unsigned char *curptr;
  unsigned long        curlen;

  LTC_ARGCHK(in     != NULL);
  LTC_ARGCHK(out    != NULL);
  LTC_ARGCHK(outlen != NULL);

  if (*outlen < 32) {
    *outlen = 32;
    return CRYPT_BUFFER_OVERFLOW;
  }

  if ((err = sha256_init(&md)) != CRYPT_OK) {
    goto LBL_ERR;
  }

  va_start(args, inlen);
  curptr = in;
  curlen = inlen;
  for (;;) {
    /* process buf */
    if ((err = sha256_process(&md, curptr, curlen)) != CRYPT_OK) {
      goto LBL_ERR;
    }
    /* step to next */
    curptr = va_arg(args, const unsigned char*);
    if (curptr == NULL) {
      break;
    }
    curlen = va_arg(args, unsigned long);
  }
  err = sha256_done(&md, out);
  *outlen = 32;
LBL_ERR:
    va_end(args);
    return err;
}
