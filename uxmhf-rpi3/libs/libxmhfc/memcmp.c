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

#if 0
int
memcmp(const void *s1, const void *s2, size_t n)
{
    if (n != 0) {
        const unsigned char *p1 = s1, *p2 = s2;

        do {
            if (*p1++ != *p2++)
                return (*--p1 - *--p2);
        } while (--n != 0);
    }
    return (0);
}
#endif // 0


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
int memcmp(const void *s1, const void *s2, size_t n)
{
  const char *c1 = s1, *c2 = s2;
  int d = 0;


  /*@
    loop invariant N_RANGE: 0 <= n <= \at(n, Pre);
    //loop invariant C1_RANGE: (unsigned char*)s1 <= c1 < (unsigned char*)s1+n;
    //loop invariant C2_RANGE: (unsigned char*)s2 <= c2 <= (unsigned char*)s2+\at(n, Pre);
    //loop invariant COMPARE: \forall integer i; 0 <= i < (\at(n, Pre) - n) ==> ((unsigned char*)s1)[i] == ((unsigned char*)s2)[i];
    //loop invariant D_ZERO: d == 0;
	loop invariant c1 == ((char*)s1)+(\at(n, Pre) - n);
	loop invariant c2 == ((char*)s2)+(\at(n, Pre) - n);
	loop invariant (char*)s2 <= c2 <= (char*)s2+\at(n,Pre);
	loop invariant (char*)s1 <= c1 <= (char*)s1+\at(n,Pre);
    loop assigns n, d, c1, c2;
    loop variant n;
  @*/
  while (/*n--*/ n) {
    d = (int)*c1++ - (int)*c2++;
    if (d)
      break;

    n--; //inserted code
  }

  return d;
}



