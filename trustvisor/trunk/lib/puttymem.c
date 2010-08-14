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
 * Platform-independent routines shared between all PuTTY programs.
 */
#include "types.h"
#include "string.h"
#include "puttymem.h"
//#include "util.h" /* For perf stuff */

/* ----------------------------------------------------------------------
 * My own versions of malloc, realloc and free. Because I want
 * malloc and realloc to bomb out and exit the program if they run
 * out of memory, realloc to reliably call malloc if passed a NULL
 * pointer, and free to reliably do nothing if passed a NULL
 * pointer. We can also put trace printouts in, if we need to; and
 * we can also replace the allocator with an ElectricFence-like
 * one.
 */

/* int totalmem = 0; */
void *safemalloc(size_t n, size_t size)
{
	void *p;

  //  struct st_timer_vars tv;
    //start_timer(&tv);

		 /*totalmem += size;
		 printf("Allocated %d bytes so far\n", totalmem);*/
	if (n > INT_MAX / size) {
		p = NULL;
	} else {
		size *= n;
		p = static_malloc(size);
	}

   // stop_timer(&tv);
   // update_sum(&perf.sum_rsag_malloc, &tv);
    
	if (!p) {
		return NULL;
	}
	return p;
}


void safefree(void *ptr)
{
	if (ptr) {
		static_free(ptr);
	}
}


/***********************************************************************
 * Replacements for string.h (see man pages for details)
 ***********************************************************************/
/*
void * memset(void *b, int c, size_t len) {
	int index;
	for (index = 0; index < len; index++) {
		((char *)b)[index] = (unsigned char) c;
	}
	return b;
}

void * memcpy(void *dst, const void *src, size_t len) {
	int index;
	for (index = 0; index < len; index++) {
		((unsigned char *) dst)[index] = ((unsigned char *) src)[index];
	}
	return dst;
}

void * memmove(void *dst, const void *src, size_t len) {
	int index;
	if (dst < src) {
		
		for (index = 0; index < len; index++) {
			((unsigned char *) dst)[index] = ((unsigned char *) src)[index];
		}
	} else if (dst == src) {

	} else {
		
		for (index = 0; index < len; index++) {
			((unsigned char *) dst)[len - index - 1] = ((unsigned char *) src)[len - index - 1];
		}
	}

	return dst;
}

int memcmp(const void *b1, const void *b2, size_t len) {
	int index, diff;
	for (index = 0; index < len; index++) {
		diff = ((unsigned char *) b1)[index] - ((unsigned char *) b2)[index];
		if (diff != 0) {
			return diff;
		}
	}
	return 0;
}

size_t strnlen(const char *s, size_t maxlen) {
        size_t len = 0;

        while (s && *s) {
                len++;
                if(len >= maxlen) {
                    return maxlen;
                }
                s++;
        }

        return len;
}

size_t strlen(const char *s) {
	size_t len = 0;

	while (s && *s) {
		len++;
		s++;
	}

	return len;
}
*/
/* taken from glibc */
char *
simple_stpncpy (char *dst, const char *src, size_t n)
{
  while (n--)
    if ((*dst++ = *src++) == '\0')
      {
        size_t i;

        for (i = 0; i < n; ++i)
          dst[i] = '\0';
        return dst - 1;
      }
  return dst;
}

size_t
simple_strcspn (const char *s, const char *rej)
{
  const char *r, *str = s;
  char c;

  while ((c = *s++) != '\0')
    for (r = rej; *r != '\0'; ++r)
      if (*r == c)
        return s - str - 1;
  return s - str - 1;
}
/*
char *strcat(char *s, char *append) {
	char *save = s;

	for (; *s; ++s);
	while ((*s++ = *append++) != 0);
	return(save);
}


char *strcat1(char *s, char append) {
    char tmp[2];
    tmp[0] = append;
    tmp[1] = '\0';
    return strcat(s, tmp);
}

char *strstr (const char *str1, const char *str2) {
    char *cp = (char *) str1;
    char *s1, *s2;
    
    if ( !*str2 )
        return((char *)str1);

    while (*cp) {
        s1 = cp;
        s2 = (char *) str2;

        while( *s1 && *s2 && !(*s1-*s2) )
            s1++, s2++;

        if (!*s2)
            return(cp);

        cp++;
    }

    return NULL;
}

int atoi(char *s) {
    int i,num=0,flag=0;
    for(i=0;i<=strlen(s);i++) {
        if(s[i] >= '0' && s[i] <= '9')
            num = num * 10 + s[i] -'0';        
        else if(s[0] == '-' && i==0) 
            flag =1;
        else break;
    }
    
    if(flag == 1)
        num = num * -1;

    return num;
}
*/
