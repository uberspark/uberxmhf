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

#include <stdint.h>
#include <string.h>

/*
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
}*/


/*@
	requires n >= 0;
	requires \valid(((char*)dst)+(0..n-1));
	requires \valid(((char*)src)+(0..n-1));
	// this function does not requires \separate. refer to manpages
	assigns ((char*)dst)[0..n-1];
	//ensures \forall integer i; 0 <= i < n ==> ((char*)dst)[i] == \old(((char*)src)[i]);
	//ensures \result == dst;
@*/
void *memmove(void *dst, const void *src, size_t n)
{
	const char *p = src;
	char *q = dst;

	if (q < p) {
		/*@
			//loop invariant \base_addr(p) == \base_addr(src);
			//loop invariant \base_addr(q) == \base_addr(dst);
			//loop invariant q < p;
			loop invariant 0 <= n <= \at(n, Pre);
			loop invariant p == ((char*)src)+(\at(n, Pre) - n);
			loop invariant q == ((char*)dst)+(\at(n, Pre) - n);
			loop invariant (char*)src <= p <= (char*)src+\at(n, Pre);
			loop invariant (char*)dst <= q <= (char*)dst+\at(n, Pre);
			//loop invariant \forall integer i; 0 <= i < (\at(n, Pre) - n) ==> ((char*)dst)[i] == \at(((char*)src)[i], Pre);
			//loop invariant \forall integer i; (\at(n, Pre) - n) <= i < \at(n, Pre) ==> ((char*)dst)[i] == \at(((char*)dst)[i], Pre);
			loop assigns p, q, n, ((char*)dst)[0..(\at(n, Pre) - n -1)];
			loop variant n;
		@*/
		while (n) {
			*q++ = *p++;
			n--;
		}
	} else {
		p += n;
		q += n;

		/*@
			//loop invariant \base_addr(p) == \base_addr(src);
			//loop invariant \base_addr(q) == \base_addr(dst);
			loop invariant 0 <= n <= \at(n, Pre);
			loop invariant p == ((char*)src) + n;
			loop invariant q == ((char*)dst) + n;
			loop invariant (char*)src <= p <= (char*)src+\at(n, Pre);
			loop invariant (char*)dst <= q <= (char*)dst+\at(n, Pre);
			//loop invariant \forall integer i; n <= i < \at(n, Pre) ==> ((char*)dst)[i] == \at(((char*)src)[i], Pre);
			//loop invariant \forall integer i; 0 <= i < n ==> ((char*)dst)[i] == \at(((char*)dst)[i], Pre);
			loop assigns p, q, n, ((char*)dst)[n..(\at(n, Pre)-1)];
			loop variant n;
		@*/
		while (n) {
			*--q = *--p;
			n--;
		}
	}

	return dst;
}

