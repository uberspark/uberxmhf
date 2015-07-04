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

/**
 * libc string functions for use in a stand-alone environment
 */
#ifndef __STRING_H__
#define __STRING_H__

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdarg.h>

#ifndef __ASSEMBLY__


/*@
  predicate Length_of_str_is{L}(char *s, integer n) =
      n >= 0 && \valid(s+(0..n)) && s[n] == 0 &&
      \forall integer k ; (0 <= k < n) ==> (s[k] != 0) ;
  axiomatic Length
  {
    logic integer Length{L}(char *s) reads s[..];
    axiom string_length{L}:
       \forall integer n, char *s ; Length_of_str_is(s, n) ==> Length(s) == n ;
  }
@*/




/*@
  requires n >= 0;
  requires \valid(((char*)s1)+(0..n-1));
  requires \valid(((char*)s2)+(0..n-1));
  requires \separated(((char*)s1)+(0..n-1), ((char*)s2)+(0..n-1));
  assigns \nothing;
  //behavior eq:
  //  assumes n >= 0;
  //  assumes \forall integer i; 0 <= i < n ==> ((unsigned char*)s1)[i] == ((unsigned char*)s2)[i];
  //  ensures \result == 0;
  //behavior not_eq:
  //  assumes n > 0;
  //  assumes \exists integer i; 0 <= i < n && ((unsigned char*)s1)[i] != ((unsigned char*)s2)[i];
  //  ensures \result != 0;
  //complete behaviors;
  //disjoint behaviors;
@*/
int memcmp(const void *s1, const void *s2, size_t n);


/*@
    requires \separated(((char*)src)+(0..n-1), ((char*)dst)+(0..n-1));
    requires n >= 0;
    requires \valid(((char*)dst)+(0..n-1));
    requires \valid(((char*)src)+(0..n-1));
    assigns ((char*)dst)[0..n-1];
    ensures \forall integer i; 0 <= i < n ==> ((char*)dst)[i] == ((char*)src)[i];
    ensures \result == dst;
 */
void *memcpy(void *dst, const void *src, size_t n);



/*@
	requires n >= 0;
	requires \valid(((char*)dst)+(0..n-1));
	requires \valid(((char*)src)+(0..n-1));
	// this function does not requires \separate. refer to manpages
	assigns ((char*)dst)[0..n-1];
	//ensures \forall integer i; 0 <= i < n ==> ((char*)dst)[i] == \old(((char*)src)[i]);
	//ensures \result == dst;
@*/
void *memmove(void *dst, const void *src, size_t n);


/*@
	requires n >= 0;
	requires \valid(((char*)dst)+(0..n-1));
	requires -128 <= c <= 127;
	assigns ((char*)dst)[0..n-1];
	ensures \forall integer i; 0 <= i < n ==> ((char*)dst)[i] == c;
	ensures \result == dst;
@*/
void *memset(void* dst, int c, size_t n);


/*@
  requires \exists integer i; Length_of_str_is(s,i);
  requires -128 <= c <= 127;
  assigns \nothing;
@*/
char *strchr(const char *s, int c);


/*@
  requires \exists integer i; Length_of_str_is(s1,i);
  requires \exists integer i; Length_of_str_is(s2,i);
  requires \separated(s1+(0..Length(s1)), s2+(0..Length(s2)));
  assigns \nothing;
  behavior eq:
	assumes \exists integer i; Length_of_str_is(s1,i) && Length_of_str_is(s2,i) &&
		  \forall integer j; 0 <= j <= i ==> s1[j] == s2[j];
	ensures \result == 0;
  behavior not_eq_i_j:
	assumes \exists integer i,j; i != j && Length_of_str_is(s1,i) && Length_of_str_is(s2,j);
	ensures \result != 0;
  behavior not_eq:
	assumes \exists integer i; Length_of_str_is(s1,i) && Length_of_str_is(s2,i) &&
		  \exists integer j; 0 <= j <= i && s1[j] != s2[j];
	ensures \result != 0;
	complete behaviors;
	disjoint behaviors;
@*/
int strcmp(const char *s1, const char *s2);

/*@
   requires \exists integer i; Length_of_str_is(s,i);
   assigns \nothing;
   //ensures \exists integer i; Length_of_str_is(s,i) && \result == i;
   ensures \result == Length(s);
 @*/
int strlen(const char *s);


int strncmp(const char *s1, const char *s2, size_t n);
char *strncpy(char * dst, const char * src, size_t n);
u32 strnlen(const char * s, uint32_t count);
unsigned long strtoul(const char *cp,const char **endp, unsigned int base);

#endif /* __ASSEMBLY__ */

#endif /* __STRING_H__ */
