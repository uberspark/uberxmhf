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

//error.h - error handling 
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __ERROR_H_
#define __ERROR_H_


#ifndef __ASSEMBLY__

#define HALT()	__asm__ __volatile__ ("hlt\r\n");
#define ASSERT(_p) { if ( !(_p) ) { printf("\nAssertion '%s' failed, line %d, file %s\n", #_p , __LINE__, __FILE__); HALT(); } }
#define WARNING(_p) { if ( !(_p) ) { printf("\nWarning Assertion '%s' failed, line %d, file %s\n", #_p , __LINE__, __FILE__);} }

/* awesome trick from http://www.jaggersoft.com/pubs/CVu11_3.html */
#define COMPILE_TIME_ASSERT(pred)               \
  switch(0){case 0:case pred:;}

/* Overflow functions from tboot-20101005/tboot/include/misc.h */

/*
 *  These three "plus overflow" functions take a "x" value
 *    and add the "y" value to it and if the two values are
 *    greater than the size of the variable type, they will
 *    overflow the type and end up with a smaller value and
 *    return TRUE - that they did overflow.  i.e.
 *    x + y <= variable type maximum.
 */
static inline bool plus_overflow_u64(uint64_t x, uint64_t y)
{
    return ((((uint64_t)(~0)) - x) < y);
}

static inline bool plus_overflow_u32(uint32_t x, uint32_t y)
{
    return ((((uint32_t)(~0)) - x) < y);
}

/*
 * This checks to see if two numbers multiplied together are larger
 *   than the type that they are.  Returns TRUE if OVERFLOWING.
 *   If the first parameter "x" is greater than zero and
 *   if that is true, that the largest possible value 0xFFFFFFFF / "x"
 *   is less than the second parameter "y".  If "y" is zero then
 *   it will also fail because no unsigned number is less than zero.
 */
static inline bool multiply_overflow_u32(uint32_t x, uint32_t y)
{
    return (x > 0) ? ((((uint32_t)(~0))/x) < y) : false;
}

#endif /*__ASSEMBLY__*/

#endif /* _ERROR_H */
