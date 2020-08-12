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
 * @brief Copy block of memory
 * 
 * @param[out] dst Pointer to the destination memory block where the content is to be copied, type-casted to a pointer of type void*
 * @param[in] src Pointer to the source of data to be copied, type-casted to a pointer of type const void*
 * @param[in] n Number of bytes to copy
 * 
 * @retval dst is returned
 *  
 * @details_begin 
 * Copies the values of ``n`` bytes from the location pointed to by ``src`` directly to the memory block pointed to 
 * by ``dst``. The underlying type of the objects pointed to by both the source and destination pointers are irrelevant for 
 * this function; The result is a binary copy of the data.
 * @details_end
 *
 *  @uobjrtl_namespace{uberspark/uobjrtl/crt}
 * 
 * @headers_begin 
 * #include <uberspark/uobjrtl/crt/include/string.h>
 * @headers_end
 * 
 * @comments_begin
 * The size of the blocks pointed to by both the ``dst`` and ``src`` parameters, shall be at least ``n`` bytes, and should not 
 * overlap. The function does not check for any terminating null character in ``src`` - it always copies exactly ``n`` bytes.
 * 
 * .. note:: Functional correctness specified
 * @comments_end
 * 
 * 
 */
/*@
    requires \separated(((unsigned char*)src)+(0..n-1), ((unsigned char*)dst)+(0..n-1));
    requires n >= 0;
    requires \valid(((unsigned char*)dst)+(0..n-1));
    requires \valid(((unsigned char*)src)+(0..n-1));
    assigns ((unsigned char*)dst)[0..n-1];
    ensures \forall integer i; 0 <= i < n ==> ((unsigned char*)dst)[i] == ((unsigned char*)src)[i];
    ensures \result == dst;
 */
unsigned char *uberspark_uobjrtl_crt__memcpy(unsigned char *dst, const unsigned char *src, size_t n)
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

