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

/* pseudo random number generator based on secure block cipher (AES) 
 * written by Zongwei Zhou for EMHF project 
 *
 * reference: page 45-56, in NIST Special Publication 800-90 (SP 800-90)
 * "Recommendations for Random Number Generation 
 * Using Deterministic Random Bit Generators(Revised)"
 * */

#include  <target.h>
#include  "./include/aes.h"
#include  "./include/scode.h"
#include  "./include/puttymem.h"
#include  "./include/random.h"

#ifdef USE_AES_CRT
#define  KEY_LEN_BYTES (TPM_AES_KEY_LEN>>3) 
#define  OUT_LEN_BYTES 16
#define  SEED_LEN_BYTES (KEY_LEN_BYTES+OUT_LEN_BYTES)

#define  RANDOM_BUFFER_SIZE (OUT_LEN_BYTES<<5)

/* XXX FIXME: needs spinlock protection in MP mode */
s32 reseed_crt = 0; /* reseed interval is 2^32 */
u8 randbuf[RANDOM_BUFFER_SIZE]="";
s32 randbuf_idx = 0;
s8 key[KEY_LEN_BYTES]="";
s8 v[OUT_LEN_BYTES]="";
aes_context rand_ctx;

void rand_incre (s8 * data, u32 len)
{
	u32 i;
	for( i=0 ; i< len ; i++ )  {
		data[i] = data[i]+1;
		if (data[i] != 0)
			break;
	}
}

void rand_xor (s8 * data, s8 * xordata, u32 len)
{
	u32 i;
	for( i=0 ; i< len ; i++ )  {
		data[i] = (data[i])^(xordata[i]);
	}
}

void rand_update ( s8* data )
{
	s8 newkey[KEY_LEN_BYTES];
	s8 newv[OUT_LEN_BYTES];

    /* JMM: Suspect BUG: missing V++ */
	aes_crypt_ecb(&rand_ctx, AES_ENCRYPT, v, newkey );
	rand_xor(newkey, data, KEY_LEN_BYTES);
	rand_incre(v, OUT_LEN_BYTES);
	aes_crypt_ecb(&rand_ctx, AES_ENCRYPT, v, newv);
	rand_xor(newv, data+KEY_LEN_BYTES, OUT_LEN_BYTES);

	vmemcpy(key, newkey, KEY_LEN_BYTES);
	vmemcpy(v, newv, OUT_LEN_BYTES);
	aes_setkey_enc(&rand_ctx, key, TPM_AES_KEY_LEN);

	reseed_crt++;
}

void rand_reseed (void)
{
	int i;
	s8 entropy[SEED_LEN_BYTES];
	/* XXX FIXME: get random number from hardware TPM */
	for( i=0 ; i<SEED_LEN_BYTES ; i++ )  {
		entropy[i]=(s8)(*(randbuf+i));
	}
	rand_update(entropy);
}

void rand_gen (char * out, int len)
{
	int i;
	s8 udata[SEED_LEN_BYTES]="";

	if (reseed_crt == 0) {
		rand_reseed();
	}

	for( i=0 ; i<(len/OUT_LEN_BYTES) ; i++ )  {
		aes_crypt_ecb(&rand_ctx, AES_ENCRYPT, v, out+i*OUT_LEN_BYTES);
		rand_incre(v, OUT_LEN_BYTES);
	}

	vmemset(udata, 0, SEED_LEN_BYTES);
	rand_update(udata);
}

void rand_init (void)
{
	/* initiate PNG key */
	reseed_crt = 0;
	vmemset(key, 0, KEY_LEN_BYTES);
	vmemset(v, 0, OUT_LEN_BYTES);
	aes_setkey_enc( &rand_ctx, key, TPM_AES_KEY_LEN);
	rand_reseed();

	/* generate some random bytes for future use */
	rand_gen(randbuf, RANDOM_BUFFER_SIZE);
	randbuf_idx = 0;
}

inline unsigned char rand_byte (void)
{
	if (randbuf_idx == RANDOM_BUFFER_SIZE) {
		randbuf_idx = 0;
		rand_gen(randbuf, RANDOM_BUFFER_SIZE);
	}
	return randbuf[randbuf_idx++];
}

int rand_bytes (unsigned char * out, int len)
{
	int i, newlen;
	unsigned char * tmp;
	/* check maximum rand bytes per requeset (2^16) */
	if (((len & 0xFFFF0000)>>16) != 0) {
		printf("[TV] Rand ERROR: exceed max bytes per request!\n");
		return 0;
	}

	if (len < (RANDOM_BUFFER_SIZE<<2)) {
		/* if rand_bytes len is small,
		 * get bytes from randbuf
		 * */
		for( i=0 ; i< len ; i++ )  {
			out[i] = rand_byte();
		}
	} else {
		/* if rand_bytes len is large,
		 * directly generate the entire block
		 * to avoid multiple rand_update 
		 * */
		if (len%RANDOM_BUFFER_SIZE != 0)
			newlen = (len/RANDOM_BUFFER_SIZE+1)*RANDOM_BUFFER_SIZE;
		tmp = (unsigned char *)vmalloc(newlen);
		rand_gen(tmp, newlen);
		vmemcpy(out, tmp, len);
		vfree(tmp);
	}
	return len;
}

#endif

#ifdef USE_ARC4
/*
 * ARC4 key schedule
 */
void arc4_setup( arc4_context *ctx, unsigned char *key, int keylen )
{
	int i, j, k, *m, a;

	ctx->x = 0;
	ctx->y = 0;
	m = ctx->m;

	for( i = 0; i < 256; i++ )
		m[i] = i;

	j = k = 0;

	for( i = 0; i < 256; i++ )
	{
		a = m[i];
		j = (unsigned char)( j + a + key[k] );
		m[i] = m[j]; m[j] = a;
		if( ++k >= keylen ) k = 0;
	}
}

/*
 * ARC4 cipher function
 */
void arc4_crypt( arc4_context *ctx, unsigned char *buf, int buflen )
{
	int i, x, y, *m, a, b;

	x = ctx->x;
	y = ctx->y;
	m = ctx->m;

	for( i = 0; i < buflen; i++ )
	{
		x = (unsigned char)( x + 1 ); a = m[x];
		y = (unsigned char)( y + a );
		m[x] = b = m[y];
		m[y] = a;
		buf[i] ^= m[(unsigned char)( a + b )];
	}

	ctx->x = x;
	ctx->y = y;
}

#define RANDOM_BUFFER_SIZE 256
#define  ENTROPY_LEN 32
s32 reseed_crt = 0; /* reseed interval is 2^32 */
u8 randbuf[RANDOM_BUFFER_SIZE]="";
s32 randbuf_idx = 0;
arc4_context arc4_ctx_rand;

void arc4GetRandom(unsigned char *buffer, int numBytes) 
{
	int i;
	s8 entropy[ENTROPY_LEN];

	if(!reseed_crt) {
		/* XXX FIXME: get random number from hardware TPM */
		for( i=0 ; i<ENTROPY_LEN ; i++ )  {
			entropy[i]=(s8)(*(randbuf+i));
		}
		arc4_setup(&arc4_ctx_rand, entropy, ENTROPY_LEN);
		reseed_crt++;
	}

	arc4_crypt(&arc4_ctx_rand, buffer, numBytes);
	reseed_crt++;
}

void rand_init (void)
{
	/* initiate PNG key */
	reseed_crt = 0;

	/* generate some random bytes for future use */
	arc4GetRandom(randbuf, RANDOM_BUFFER_SIZE);
	randbuf_idx = 0;
}

unsigned char rand_byte(void) 
{
	if (randbuf_idx == RANDOM_BUFFER_SIZE) {
		randbuf_idx = 0;
		arc4GetRandom(randbuf, RANDOM_BUFFER_SIZE);
	}
	return randbuf[randbuf_idx++];
}

int rand_bytes (unsigned char * out, int len)
{
	int i;
	/* check maximum rand bytes per requeset (2^16) */
	if (((len & 0xFFFF0000)>>16) != 0) {
		printf("[TV] Rand ERROR: exceed max bytes per request!\n");
		return 0;
	}

	for( i=0 ; i< len ; i++ )  {
		out[i] = rand_byte();
	}
	return len;

}
#endif
