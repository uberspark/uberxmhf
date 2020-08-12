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
 *
 * @brief Fill block of memory
 * 
 * @param[out] dst Pointer to the block of memory to fill
 * @param[in] c Value to be set. The value is passed as an int, but the function fills the block of memory using the 
 * 				unsigned char conversion of this value
 * @param[in] n Number of bytes to be set to the value c
 * 
 * @retval dst is returned
 *  
 * @details_begin 
 * Sets the first ``n`` bytes of the block of memory pointed by ``dat`` to the specified value ``c`` (interpreted as an 
 * unsigned char).
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
	requires n >= 0;
	requires \valid(((unsigned char*)dst)+(0..n-1));
	assigns ((unsigned char*)dst)[0..n-1];
	ensures \forall integer i; 0 <= i < n ==> (dst[i] == (unsigned char)c);
	ensures \result == dst;
@*/
unsigned char *uberspark_uobjrtl_crt__memset(unsigned char* dst, int c, size_t n)
{
	size_t i;

	/*@
		loop invariant 0 <= i <= n;
		loop invariant \forall integer x; 0 <= x < i ==> (dst[x] == (unsigned char)c);
		loop assigns i;
		loop assigns dst[0..(n-1)];
		loop variant n-i;
	@*/
	for(i=0; i < n; i++){
		dst[i]=(unsigned char)c;
	}

	return dst;
}
