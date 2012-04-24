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

#include <stdint.h>
#include <string.h> 

void *memmove(void *dst_void, const void *src_void, u32 length){
  char *dst = dst_void;
  const char *src = src_void;

  if (src < dst && dst < src + length){
      // Have to copy backwards 
      src += length;
      dst += length;
      while (length--){
	     *--dst = *--src;
	     }
  }else{
      while (length--){
	     *dst++ = *src++;
	    }
  }

  return dst_void;
}

#if ARCH_X86 /* FIXME - currently never enabled */
char *strchr(const char *s, int c)
{
    long d0;
    register char *__res;
    __asm__ __volatile__ (
        "   mov  %%al,%%ah  \n"
        "1: lodsb           \n"
        "   cmp  %%ah,%%al  \n"
        "   je   2f         \n"
        "   test %%al,%%al  \n"
        "   jne  1b         \n"
        "   mov  $1,%1      \n"
        "2: mov  %1,%0      \n"
        "   dec  %0         \n"
        : "=a" (__res), "=&S" (d0) : "1" (s), "0" (c) );
    return __res;
}
#else
char *strchr(const char *s, int c)
{
  char *rv=NULL;
  while(*s != '\0') {
    if (*s == c) {
      rv=(char*)s;
      break;
    }
    s++;
  }
  return (char*)rv;
}
#endif

u32 strnlen(const char * s, u32 count){
	const char *sc;

	for (sc = s; count-- && *sc != '\0'; ++sc);
	return (u32)(sc - s);
}

#if ARCH_X86 /* FIXME - currently never enabled */
void *memcpy(void * to, const void * from, u32 n){
  int d0, d1, d2;

  __asm__ __volatile__(
  	"rep ; movsl\n\t"
  	"movl %4,%%ecx\n\t"
  	"andl $3,%%ecx\n\t"
#if 1	/* want to pay 2 byte penalty for a chance to skip microcoded rep? */
  	"jz 1f\n\t"
#endif
  	"rep ; movsb\n\t"
  	"1:"
  	: "=&c" (d0), "=&D" (d1), "=&S" (d2)
  	: "0" (n/4), "g" (n), "1" ((long) to), "2" ((long) from)
  	: "memory");
  return (to);
}
#else
void *memcpy(void * to, const void * from, u32 n)
{
  size_t i;
  for(i=0; i<n; i++) {
    ((uint8_t*)to)[i] = ((uint8_t*)from)[i];
  }
  return to;
}
#endif

void *memset (void *str, int c, size_t len) {
  register u8 *st = str;

  while (len-- > 0)
    *st++ = (u8)c;
  return str;
}

#ifndef HAVE_MEMCMP
int
memcmp(const void *s1, const void *s2, size_t n)
{
    if (n != 0) {
        const unsigned char *p1 = s1, *p2 = s2;

        do {
            if (*p1++ != *p2++)
                return (*--p1 - *--p2);
        } while (--n != 0);
    }
    return (0);
}
#endif /* HAVE_MEMCMP */
