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



void *memmove(void *dst_void, const void *src_void, uint32_t length);


/*@
	requires n >= 0;
	requires \valid(((char*)dst)+(0..n-1));
	requires -128 <= c <= 127;
	assigns ((char*)dst)[0..n-1];
	ensures \forall integer i; 0 <= i < n ==> ((char*)dst)[i] == c;
	ensures \result == dst;
@*/
void *memset(void* dst, int c, size_t n);


char *strchr(const char *s, int c);
int strcmp(const char * cs,const char * ct);
size_t strlen(const char * s);
int strncmp(const char *s1, const char *s2, size_t n);
char *strncpy(char * dst, const char * src, size_t n);
u32 strnlen(const char * s, uint32_t count);
unsigned long strtoul(const char *cp,const char **endp, unsigned int base);

#endif /* __ASSEMBLY__ */

#endif /* __STRING_H__ */
