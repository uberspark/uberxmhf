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

#include <stdarg.h>

/*#define LTC_MECC			1
#define LTC_MECC_FP			1
#define LTC_ECC_SHAMIR		1
*/
#undef LTC_MECC
#undef LTC_MECC_FP			
#undef LTC_ECC_SHAMIR		
#define LTC_MRSA			1

ltc_math_descriptor ltc_mp;


int ltc_init_multi(void **a, ...)
{
   void    **cur = a;
   int       np  = 0;
   va_list   args;

   va_start(args, a);
   while (cur != NULL) {
       if (mp_init(cur) != CRYPT_OK) {
          /* failed */
          va_list clean_list;

          va_start(clean_list, a);
          cur = a;
          while (np--) {
              mp_clear(*cur);
              cur = va_arg(clean_list, void**);
          }
          va_end(clean_list);
          return CRYPT_MEM;
       }
       ++np;
       cur = va_arg(args, void**);
   }
   va_end(args);
   return CRYPT_OK;   
}

void ltc_deinit_multi(void *a, ...)
{
   void     *cur = a;
   va_list   args;

   va_start(args, a);
   while (cur != NULL) {
       mp_clear(cur);
       cur = va_arg(args, void *);
   }
   va_end(args);
}


/**
  @file rand_prime.c
  Generate a random prime, Tom St Denis
*/  

#define USE_BBS 1

int rand_prime(void *N, long len, prng_state *prng, int wprng)
{
   int            err, res, type;
   unsigned char *buf;

   LTC_ARGCHK(N != NULL);

   /* get type */
   if (len < 0) {
      type = USE_BBS;
      len = -len;
   } else {
      type = 0;
   }

   /* allow sizes between 2 and 512 bytes for a prime size */
   if (len < 2 || len > 512) { 
      return CRYPT_INVALID_PRIME_SIZE;
   }
   
   /* valid PRNG? Better be! */
   if ((err = prng_is_valid(wprng)) != CRYPT_OK) {
      return err; 
   }

   /* allocate buffer to work with */
   buf = XCALLOC(1, len);
   if (buf == NULL) {
       return CRYPT_MEM;
   }

   do {
      /* generate value */
      if (prng_descriptor[wprng].read(buf, len, prng) != (unsigned long)len) {
         XFREE(buf);
         return CRYPT_ERROR_READPRNG;
      }

      /* munge bits */
      buf[0]     |= 0x80 | 0x40;
      buf[len-1] |= 0x01 | ((type & USE_BBS) ? 0x02 : 0x00);
 
      /* load value */
      if ((err = mp_read_unsigned_bin(N, buf, len)) != CRYPT_OK) {
         XFREE(buf);
         return err;
      }

      /* test */
      if ((err = mp_prime_is_prime(N, 8, &res)) != CRYPT_OK) {
         XFREE(buf);
         return err;
      }
   } while (res == LTC_MP_NO);

#ifdef LTC_CLEAN_STACK
   zeromem(buf, len);
#endif

   XFREE(buf);
   return CRYPT_OK;
}

