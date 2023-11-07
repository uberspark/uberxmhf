/*-
* Copyright (c) 1990 The Regents of the University of California.
* All rights reserved.
*
* This code is derived from software contributed to Berkeley by
* William Jolitz and Don Ahn.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions
* are met:
* 1. Redistributions of source code must retain the above copyright
*    notice, this list of conditions and the following disclaimer.
* 2. Redistributions in binary form must reproduce the above copyright
*    notice, this list of conditions and the following disclaimer in the
*    documentation and/or other materials provided with the distribution.
* 3. All advertising materials mentioning features or use of this software
*    must display the following acknowledgement:
*      This product includes software developed by the University of
*      California, Berkeley and its contributors.
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
*
*      from: @(#)clock.c       7.2 (Berkeley) 5/12/91
*/

/**
 * Modified for XMHF.
 */

// div64.h - 64-bit division macros

#ifndef __DIV64_H__
#define __DIV64_H__

#ifndef __ASSEMBLY__


// do_div()
// modifies the 64-bit dividend _in_place_
// returns the 32-bit remainder

// TODO: not implemented for amd64

#ifdef __AMD64__
#define do_div(n,base) ({ \
        switch(0) { case 0: case 0: not_implemented_for_amd64 }; \
})
#elif defined(__I386__)
#define do_div(n,base) ({ \
        unsigned long __upper, __low, __high, __mod, __base; \
        __base = (base); \
        __asm("":"=a" (__low), "=d" (__high):"A" (n)); \
        __upper = __high; \
        if (__high) { \
                __upper = __high % (__base); \
                __high = __high / (__base); \
        } \
        __asm("divl %2":"=a" (__low), "=d" (__mod):"rm" (__base), "0" (__low), "1" (__upper)); \
        __asm("":"=A" (n):"a" (__low),"d" (__high)); \
        __mod; \
})
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */

#endif /* __ASSEMBLY__ */
#endif /* __DIV64_H__ */
