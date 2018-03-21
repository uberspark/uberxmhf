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
u32 strnlen(const char * s, u32 count){
	const char *sc;

	for (sc = s; count-- && *sc != '\0'; ++sc);
	return (u32)(sc - s);
}*/

/*@
  requires maxlen >= 0;
  requires \valid(s+(0..maxlen-1));
  assigns \nothing;
  behavior bigger:
    assumes \forall integer i; 0 <= i < maxlen ==> s[i] != 0;
    ensures \result == maxlen;

  behavior smaller:
    assumes \exists integer i; 0 <= i < maxlen && s[i] == 0;
    ensures \result <= maxlen;
  complete behaviors;
  disjoint behaviors;
*/
size_t strnlen(const char *s, size_t maxlen)
{
  const char *ss = s;

  /* Important: the maxlen test must precede the reference through ss;
     since the byte beyond the maximum may segfault */

  /*@
    loop invariant 0 <= maxlen <= \at(maxlen,Pre);
    loop invariant \forall integer i; 0 <= i < (\at(maxlen, Pre) - maxlen) ==> s[i] != 0;
    loop invariant ss == s+(\at(maxlen, Pre) - maxlen);
    loop invariant s <= ss <= s+\at(maxlen, Pre);
    loop assigns maxlen, ss;
    loop variant maxlen;
  */
  while ((maxlen > 0) && *ss) {
    ss++;
    maxlen--;
  }
  return ss - s;
}

