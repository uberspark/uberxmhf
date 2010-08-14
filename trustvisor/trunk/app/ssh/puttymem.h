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

/*
 * PuTTY memory-handling header.
 */

#ifndef PUTTY_PUTTYMEM_H
#define PUTTY_PUTTYMEM_H

#include "malloc.h"

/* #define memset myMemset */
/* #define memcpy myMemcpy */
/* #define memmove myMemmove */

#define smalloc(z) safemalloc(z,1)
#define snmalloc safemalloc
#define sfree safefree

#ifndef size_t
typedef unsigned int size_t;
#endif /* size_t */

#ifndef INT_MAX
#define INT_MAX 0x7FFFFFFF
#endif

void *safemalloc(size_t, size_t);
void safefree(void *);

/*
 * Direct use of smalloc within the code should be avoided where
 * possible, in favour of these type-casting macros which ensure
 * you don't mistakenly allocate enough space for one sort of
 * structure and assign it to a different sort of pointer.
 */
#define snew(type) ((type *)snmalloc(1, sizeof(type)))
#define snewn(n, type) ((type *)snmalloc((n), sizeof(type)))

/***********************************************************************
 * Replacements for string.h (see man pages for details)
 ***********************************************************************/
void * memset(void *b, int c, size_t len); 
void * memcpy(void *dst, const void *src, size_t len); 
void * memmove(void *dst, const void *src, size_t len); 
int memcmp(const void *b1, const void *b2, size_t len);

#define strncmp(s1, s2, size) memcmp(s1, s2, size)

size_t strlen(const char *s);
size_t strnlen(const char *s, size_t maxlen);

#define stpncpy(dst, src, n) simple_stpncpy(dst, src, n) 

char *simple_stpncpy (char *dst, const char *src, size_t n);

#define strcspn(s, rej) simple_strcspn(s, rej)
size_t simple_strcspn (const char *s, const char *rej);
char *strcat(char *s, char *append);
char *strcat1(char *s, char append);
char *strstr (const char *str1, const char *str2);
int atoi(char *s);
#endif
