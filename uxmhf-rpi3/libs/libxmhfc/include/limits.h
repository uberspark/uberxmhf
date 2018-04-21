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
 * Copyright (c) 1988, 1993
 *      The Regents of the University of California.  All rights reserved.
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
 *
 * $FreeBSD: stable/8/sys/sys/limits.h 219757 2011-03-18 22:35:48Z jilles $
 */

/**
 * Modified for XMHF.
 */

#ifndef __LIMITS_H__
#define __LIMITS_H__

/*
 * According to ANSI (section 2.2.4.2), the values below must be usable by
 * #if preprocessing directives.  Additionally, the expression must have the
 * same type as would an expression that is an object of the corresponding
 * type converted according to the integral promotions.  The subtraction for
 * INT_MIN, etc., is so the value is not unsigned; e.g., 0x80000000 is an
 * unsigned int for 32-bit two's complement ANSI compilers (section 3.1.3.2).
 * These numbers are for the default configuration of gcc.  They work for
 * some other compilers as well, but this should not be depended on.
 */

#define __CHAR_BIT      8               /* number of bits in a char */

#define __SCHAR_MAX     0x7f            /* max value for a signed char */
#define __SCHAR_MIN     (-0x7f - 1)     /* min value for a signed char */

#define __UCHAR_MAX     0xff            /* max value for an unsigned char */

#define __USHRT_MAX     0xffff          /* max value for an unsigned short */
#define __SHRT_MAX      0x7fff          /* max value for a short */
#define __SHRT_MIN      (-0x7fff - 1)   /* min value for a short */

#define __UINT_MAX      0xffffffffU     /* max value for an unsigned int */
#define __INT_MAX       0x7fffffff      /* max value for an int */
#define __INT_MIN       (-0x7fffffff - 1)       /* min value for an int */

#define __ULONG_MAX     0xffffffffUL    /* max value for an unsigned long */
#define __LONG_MAX      0x7fffffffL     /* max value for a long */
#define __LONG_MIN      (-0x7fffffffL - 1)      /* min value for a long */

                        /* max value for an unsigned long long */
#define __ULLONG_MAX    0xffffffffffffffffULL
#define __LLONG_MAX     0x7fffffffffffffffLL    /* max value for a long long */
#define __LLONG_MIN     (-0x7fffffffffffffffLL - 1)  /* min for a long long */

#define __SSIZE_MAX     __INT_MAX       /* max value for a ssize_t */

#define __SIZE_T_MAX    __UINT_MAX      /* max value for a size_t */

#define __OFF_MAX       __LLONG_MAX     /* max value for an off_t */
#define __OFF_MIN       __LLONG_MIN     /* min value for an off_t */

/* Quads and long longs are the same size.  Ensure they stay in sync. */
#define __UQUAD_MAX     __ULLONG_MAX    /* max value for a uquad_t */
#define __QUAD_MAX      __LLONG_MAX     /* max value for a quad_t */
#define __QUAD_MIN      __LLONG_MIN     /* min value for a quad_t */

#define __LONG_BIT      32
#define __WORD_BIT      32




#define CHAR_BIT        __CHAR_BIT      /* number of bits in a char */

#define SCHAR_MAX       __SCHAR_MAX     /* max value for a signed char */
#define SCHAR_MIN       __SCHAR_MIN     /* min value for a signed char */

#define UCHAR_MAX       __UCHAR_MAX     /* max value for an unsigned char */

#ifdef __CHAR_UNSIGNED__
#define CHAR_MAX        UCHAR_MAX       /* max value for a char */
#define CHAR_MIN        0               /* min value for a char */
#else
#define CHAR_MAX        SCHAR_MAX
#define CHAR_MIN        SCHAR_MIN
#endif

#define USHRT_MAX       __USHRT_MAX     /* max value for an unsigned short */
#define SHRT_MAX        __SHRT_MAX      /* max value for a short */
#define SHRT_MIN        __SHRT_MIN      /* min value for a short */

#define UINT_MAX        __UINT_MAX      /* max value for an unsigned int */
#define INT_MAX         __INT_MAX       /* max value for an int */
#define INT_MIN         __INT_MIN       /* min value for an int */

#define ULONG_MAX       __ULONG_MAX     /* max for an unsigned long */
#define LONG_MAX        __LONG_MAX      /* max for a long */
#define LONG_MIN        __LONG_MIN      /* min for a long */

#define ULLONG_MAX      __ULLONG_MAX    /* max for an unsigned long long */
#define LLONG_MAX       __LLONG_MAX     /* max for a long long */
#define LLONG_MIN       __LLONG_MIN     /* min for a long long */

#define SSIZE_MAX       __SSIZE_MAX     /* max value for an ssize_t */
#define SIZE_T_MAX      __SIZE_T_MAX    /* max value for a size_t */
#define OFF_MAX         __OFF_MAX       /* max value for an off_t */
#define OFF_MIN         __OFF_MIN       /* min value for an off_t */

#define LONG_BIT        __LONG_BIT
#define WORD_BIT        __WORD_BIT


#endif /* __LIMITS_H__ */
