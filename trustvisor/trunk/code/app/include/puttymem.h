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
 * Edited by Zongwei Zhou
 */

//#include "malloc.h"
#include <types.h>

#define vmalloc(z) safemalloc(z,1)
#define vnmalloc safemalloc
#define vfree safefree

#ifndef INT_MAX
#define INT_MAX 0x7FFFFFFF
#endif

void *safemalloc(size_t, size_t);
void safefree(void *);

void mem_init(void); 
/*
 * Direct use of smalloc within the code should be avoided where
 * possible, in favour of these type-casting macros which ensure
 * you don't mistakenly allocate enough space for one sort of
 * structure and assign it to a different sort of pointer.
 */
#define vnew(type) ((type *)vnmalloc(1, sizeof(type)))
#define vnewn(n, type) ((type *)vnmalloc((n), sizeof(type)))

/***********************************************************************
 * Replacements for string.h (see man pages for details)
 ***********************************************************************/
void * vmemset(void *b, int c, size_t len); 
void * vmemcpy(void *dst, const void *src, size_t len); 
void * vmemmove(void *dst, const void *src, size_t len); 
int vmemcmp(const void *b1, const void *b2, size_t len);

#define vstrncmp(s1, s2, size) vmemcmp(s1, s2, size)
size_t vstrcpy(char *dst, char *src);
size_t vstrlen(const char *s);
size_t vstrnlen(const char *s, size_t maxlen);

#define vstpncpy(dst, src, n) vsimple_stpncpy(dst, src, n) 

char *vsimple_stpncpy (char *dst, const char *src, size_t n);

#define vstrcspn(s, rej) vsimple_strcspn(s, rej)
size_t vsimple_strcspn (const char *s, const char *rej);
char *vstrcat(char *s, char *append);
char *vstrcat1(char *s, char append);
//char *vstrstr (const char *str1, const char *str2);
int vatoi(char *s);
