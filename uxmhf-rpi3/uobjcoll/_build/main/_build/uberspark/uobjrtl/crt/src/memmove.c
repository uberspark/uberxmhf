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

#include <uberspark/uobjrtl/crt/include/string.h>


/** 
 * @brief Move block of memory
 * 
 * @param[out] dst Pointer to the destination array where the content is to be copied, type-casted to a pointer of type void*
 * @param[in] src Pointer to the source of data to be copied, type-casted to a pointer of type const void*
 * @param[in] n Number of bytes to copy
 * 
 * @retval dst is returned
 *  
 * @details_begin 
 * Copies the values of ``n`` bytes from the location pointed by source (``src``) to the memory block pointed 
 * by destination (``dst``). Copying takes place as if an intermediate buffer were used, 
 * allowing the destination and source to overlap. The underlying type of the objects pointed by both 
 * the source and destination pointers are irrelevant for this function; The result is a binary copy of the data.
 * @details_end
 *
 *  @uobjrtl_namespace{uberspark/uobjrtl/crt}
 * 
 * @headers_begin 
 * #include <uberspark/uobjrtl/crt/include/string.h>
 * @headers_end
 * 
 * @comments_begin
 * The size of the blocks pointed to by both the ``dst`` and ``src`` parameters, shall be at least ``n`` bytes.
 * The function does not check for any terminating null character in ``src`` - it always copies exactly ``n`` bytes.
 * 
 * .. note:: Functional correctness specified
 * @comments_end
 * 
 * 
 */
/*@
	requires n >= 0;
	requires \valid(((char*)dst)+(0..n-1));
	requires \valid(((char*)src)+(0..n-1));
	// this function does not requires \separate. refer to manpages
	assigns ((char*)dst)[0..n-1];
	//ensures \forall integer i; 0 <= i < n ==> ((char*)dst)[i] == \old(((char*)src)[i]);
	//ensures \result == dst;
@*/
void *uberspark_uobjrtl_crt__memmove(void *dst, const void *src, size_t n)
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

