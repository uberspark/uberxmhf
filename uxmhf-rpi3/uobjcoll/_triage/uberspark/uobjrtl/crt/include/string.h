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

/*
 * libc string functions for use in a stand-alone environment
 */
#ifndef __UOBJRTL_CRT__STRING_H__
#define __UOBJRTL_CRT__STRING_H__

#include <uberspark/uobjrtl/crt/include/stdint.h>
#include <uberspark/uobjrtl/crt/include/stddef.h>

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
int uberspark_uobjrtl_crt__memcmp(const void *s1, const void *s2, size_t n);


/*@
    requires \separated(((unsigned char*)src)+(0..n-1), ((unsigned char*)dst)+(0..n-1));
    requires n >= 0;
    requires \valid(((unsigned char*)dst)+(0..n-1));
    requires \valid(((unsigned char*)src)+(0..n-1));
    assigns ((unsigned char*)dst)[0..n-1];
    assigns \result \from dst;
    ensures \forall integer i; 0 <= i < n ==> ((unsigned char*)dst)[i] == ((unsigned char*)src)[i];
    ensures \result == dst;
 */
unsigned char *uberspark_uobjrtl_crt__memcpy(unsigned char *dst, const unsigned char *src, size_t n);



/*@
	requires n >= 0;
	requires \valid(((char*)dst)+(0..n-1));
	requires \valid(((char*)src)+(0..n-1));
	// this function does not requires \separate. refer to manpages
	assigns ((char*)dst)[0..n-1];
	//ensures \forall integer i; 0 <= i < n ==> ((char*)dst)[i] == \old(((char*)src)[i]);
	//ensures \result == dst;
@*/
void *uberspark_uobjrtl_crt__memmove(void *dst, const void *src, size_t n);

/*@
	requires n >= 0;
	requires \valid(((unsigned char*)dst)+(0..n-1));
	assigns ((unsigned char*)dst)[0..n-1];
	assigns \result \from dst;
	ensures \forall integer i; 0 <= i < n ==> (dst[i] == (unsigned char)c);
	ensures \result == dst;
@*/
unsigned char *uberspark_uobjrtl_crt__memset(unsigned char* dst, int c, size_t n);


/*@
  requires \exists integer i; Length_of_str_is(s,i);
  requires -128 <= c <= 127;
  assigns \nothing;
@*/
char *uberspark_uobjrtl_crt__strchr(const char *s, int c);


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
int uberspark_uobjrtl_crt__strcmp(const char *s1, const char *s2);

/*@
   requires \exists integer i; Length_of_str_is(s,i);
   assigns \nothing;
   //ensures \exists integer i; Length_of_str_is(s,i) && \result == i;
   ensures \result == Length(s);
 @*/
int uberspark_uobjrtl_crt__strlen(const char *s);

/*@
	requires n >= 0;
	requires \valid(s1+(0..n-1));
	requires \valid(s2+(0..n-1));
	requires \separated(s1+(0..n-1), s2+(0..n-1));
	assigns \nothing;

	//behavior normal_n_eq:
	//	assumes \exists integer i; 0 <= i < n && Length_of_str_is(s1,i) && Length_of_str_is(s2,i)
	//											&& (\forall integer k; 0 <= k < i ==> s1[k] == s2[k]);
  	//	ensures \result == 0;
	//behavior normal_n_not_eq:
	//	assumes \exists integer i; 0 <= i < n && Length_of_str_is(s1,i) && Length_of_str_is(s2,i)
	//											&& (\exists integer k; 0 <= k <= i && s1[k] != s2[k]);
  	//	ensures \result != 0;
	//behavior larger_n_eq:
	//	assumes \forall integer i; 0 <= i < n ==> s1[i] != 0;
	//	assumes \forall integer i; 0 <= i < n ==> s2[i] != 0;
	//	assumes \forall integer i; 0 <= i < n ==> s1[i] == s2[i];
	//	ensures \result == 0;
	//behavior larger_n_not_eq:
	//	assumes \forall integer i; 0 <= i < n ==> s1[i] != 0;
	//	assumes \forall integer i; 0 <= i < n ==> s2[i] != 0;
	//	assumes \exists integer i; 0 <= i < n && s1[i] != s2[i];
	//	ensures \result != 0;
	//behavior s1_s2_smaller:
	//	assumes \exists integer i, j; 0 <= i < n && 0 <= j < n
	//			&& i != j && Length_of_str_is(s1, i) && Length_of_str_is(s2, j);
	//	ensures \result != 0;
	//behavior s1_smaller:
	//	assumes \exists integer i; 0 <= i < n && Length_of_str_is(s1, i);
	//	assumes \forall integer i; 0 <= i < n ==> s2[i] != 0;
	//	ensures \result != 0;
	//behavior s2_smaller:
	//	assumes \forall integer i; 0 <= i < n ==> s1[i] != 0;
	//	assumes \exists integer i; 0 <= i < n && Length_of_str_is(s2, i);
	//	ensures \result != 0;
	//behavior zero:
	//	assumes n == 0;
	//	ensures \result == 0;
  //complete behaviors;
  //disjoint behaviors;
@*/
int uberspark_uobjrtl_crt__strncmp(const char *s1, const char *s2, size_t n);

/*@
	requires n >= 0;
	requires \exists integer i; Length_of_str_is(src, i);
	requires \valid(dst+(0..n-1));
	requires \valid(((char*)src)+(0..n-1));
	requires \separated(src+(0..n-1), dst+(0..n-1));
	assigns dst[0..n-1];
	ensures \result == dst;
@*/
char *uberspark_uobjrtl_crt__strncpy(char *dst, const char *src, size_t n);

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
size_t uberspark_uobjrtl_crt__strnlen(const char *s, size_t maxlen);



#endif /* __ASSEMBLY__ */

#endif /* __UOBJRTL_CRT__STRING_H__ */
