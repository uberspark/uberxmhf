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

/* memcpy.c - routines for memory copying on 32-bit x86
 * Modified from Xen for TrustVisor by Arvind Seshadri and Elaine Shi
 */

#include <types.h>

void *init_memcpy(void * to, const void * from, u32 n) __attribute__ ((section ("_init_text")));
void *init_memset(void * s, u32 c, u32 count) __attribute__ ((section ("_init_text")));
u32 init_memcmp(void *s1, void *s2, u32 count) __attribute__ ((section ("_init_text")));

inline void *init_memcpy(void * to, const void * from, u32 n)
{
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

/*
 * memset(x,0,y) is a reasonably common thing to do, so we want to fill
 * things 32 bits at a time even when we don't know the size of the
 * area at compile-time..
 */
inline void *init_memset(void * s, u32 c, u32 count)
{
  int d0, d1;
  int tmp = c & 0xff;

  c = tmp | (tmp << 8) | (tmp << 16) | (tmp << 24);

  __asm__ __volatile__(
  	"rep ; stosl\n\t"
  	"testb $2,%b3\n\t"
  	"je 1f\n\t"
  	"stosw\n"
  	"1:\ttestb $1,%b3\n\t"
  	"je 2f\n\t"
  	"stosb\n"
  	"2:"
  	:"=&c" (d0), "=&D" (d1)
  	:"a" (c), "q" (count), "0" (count/4), "1" ((long) s)
  	:"memory");
  return (s);	
}

u32 init_memcmp(void *s1, void *s2, u32 count)
{
  u32 i;
  for (i = 0; i < count; i ++)
    if (((u8 *)s1)[i] != ((u8 *)s2)[i])
      return 1;
  return 0;
}

inline void *memcpy(void * to, const void * from, u32 n)
{
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

/*
 * memset(x,0,y) is a reasonably common thing to do, so we want to fill
 * things 32 bits at a time even when we don't know the size of the
 * area at compile-time..
 */
inline void *memset(void * s, u32 c, u32 count)
{
  int d0, d1;
  int tmp = c & 0xff;

  c = tmp | (tmp << 8) | (tmp << 16) | (tmp << 24);

  __asm__ __volatile__(
  	"rep ; stosl\n\t"
  	"testb $2,%b3\n\t"
  	"je 1f\n\t"
  	"stosw\n"
  	"1:\ttestb $1,%b3\n\t"
  	"je 2f\n\t"
  	"stosb\n"
  	"2:"
  	:"=&c" (d0), "=&D" (d1)
  	:"a" (c), "q" (count), "0" (count/4), "1" ((long) s)
  	:"memory");
  return (s);	
}

inline u32 memcmp(void *s1, void *s2, u32 count)
{
  u32 i;
  for (i = 0; i < count; i ++)
    if (((u8 *)s1)[i] != ((u8 *)s2)[i])
      return 1;
  return 0;
}

inline char *strchr(const char *s, int c)
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

u32 strlen(const char * s)
{
	const char *sc;

	for (sc = s; *sc != '\0'; ++sc)
		/* nothing */;
	return (u32)(sc - s);
}

u32 strnlen(const char * s, u32 count)
{
	const char *sc;

	for (sc = s; count-- && *sc != '\0'; ++sc)
		/* nothing */;
	return (u32)(sc - s);
}

/* copy at most 'count' characters (including trailing '\0') from src
 *  to dst. dst in null terminated.
 */
char* strncpy(char *dest, const char *src, u32 count)
{
	char *tmp = dest;
	
	count--;
	dest[count] = '\0';
	while (count-- && (*dest++ = *src++) != '\0')
		/* nothing */;
	return tmp;
}
