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
 * @brief Determine the length of a fixed-size string
 * 
 * @param[in] s C string
 * @param[in] maxlen Maximum length of string allowed
 * 
 * @retval length of string in bytes if that is less than maxlen
 * @retval maxlen if there is no NULL character among the first maxlen characters pointed to by s
 *  
 * @details_begin
 * This function returns the number of bytes in the string pointed to by ``s``, excluding the terminating 
 * NULL byte ('\0'), but at most ``maxlen``.  In doing this, it looks only at the first ``maxlen``
 * characters in the string pointed to by ``s`` and never beyond ``s+maxlen``. 
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
size_t uberspark_uobjrtl_crt__strnlen(const char *s, size_t maxlen)
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

