/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

/*-
 * Copyright (c) 1990, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Chris Torek.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */
/*
 * From: FreeBSD sys/libkern/strcmp.c
 */

#include <uberspark/uobjrtl/crt/include/string.h>


/** 
 *
 * @brief Compare two strings
 * 
 * @param[in] s1 C string to be compared
 * @param[in] s2 C string to be compared
 * 
 * @retval less-than-0 the first character that does not match has a lower value in s1 than in s2
 * @retval 0 the contents of both strings are equal
 * @retval greater-than-0 the first character that does not match has a greater value in s1 than in s2
 *   
 * @details_begin 
 * Compares the C string ``s1`` to the C string ``s2``.
 * This function starts comparing the first character of each string. If they are equal to each other, it continues 
 * with the following pairs until the characters differ or until a terminating NULL character is reached.
 * @details_end
 *
 *  @uobjrtl_namespace{uberspark/uobjrtl/crt}
 *
 * @headers_begin 
 * #include <uberspark/uobjrtl/crt/include/string.h>
 * @headers_end
 * 
 * @comments_begin
 * .. note:: Functional correctness specified
 * @comments_end
 * 
 */
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
int uberspark_uobjrtl_crt__strcmp(const char *s1, const char *s2) {
  const char *c1 = (const char *)s1;
  const char *c2 = (const char *)s2;
  char ch;
  int d = 0;

	/*@
		loop invariant \base_addr(c1) == \base_addr(s1);
		loop invariant \base_addr(c2) == \base_addr(s2);
		loop invariant s1 <= c1 <= s1 + Length(s1);
		loop invariant s2 <= c2 <= s2 + Length(s2);
		loop invariant c1 == s1+(c2-s2);
		loop invariant c2 == s2+(c1-s1);
		loop invariant \forall integer i; 0 <= i < (c1-s1) ==> s1[i] == s2[i];
		loop assigns ch, c1, c2, d;
		loop variant Length(s1) - (c1-s1);
	@*/
	while (1) {
		d = (int)(ch = *c1++) - (int)*c2++;
		if (d || !ch)
			break;
	}
	return d;
}
