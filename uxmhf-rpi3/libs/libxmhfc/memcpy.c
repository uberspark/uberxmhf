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

#include <stdint.h>
#include <string.h>


/*void *memcpy(void * to, const void * from, u32 n)
{
  size_t i;
  for(i=0; i<n; i++) {
    ((uint8_t*)to)[i] = ((const uint8_t*)from)[i];
  }
  return to;
}*/


/*@
    requires \separated(((unsigned char*)src)+(0..n-1), ((unsigned char*)dst)+(0..n-1));
    requires n >= 0;
    requires \valid(((unsigned char*)dst)+(0..n-1));
    requires \valid(((unsigned char*)src)+(0..n-1));
    assigns ((unsigned char*)dst)[0..n-1];
    ensures \forall integer i; 0 <= i < n ==> ((unsigned char*)dst)[i] == ((unsigned char*)src)[i];
    ensures \result == dst;
 */
unsigned char *memcpy(unsigned char *dst, const unsigned char *src, size_t n)
{
	const unsigned char *p = src;
	unsigned char *q = dst;

	/*@
		loop invariant 0 <= n <= \at(n,Pre);
		loop invariant p == ((unsigned char*)src)+(\at(n, Pre) - n);
		loop invariant q == ((unsigned char*)dst)+(\at(n, Pre) - n);
		loop invariant (unsigned char*)dst <= q <= (unsigned char*)dst+\at(n,Pre);
		loop invariant (unsigned char*)src <= p <= (unsigned char*)src+\at(n,Pre);
		loop invariant \forall integer i; 0 <= i < (\at(n, Pre) - n) ==> ((unsigned char*)dst)[i] == ((unsigned char*)src)[i];
		loop assigns n, q, p, ((unsigned char*)dst)[0..(\at(n,Pre)- n - 1)];
		loop variant n;
	*/
	while (n) {
		*q++ = *p++;
		n--;
	}

	return dst;
}

