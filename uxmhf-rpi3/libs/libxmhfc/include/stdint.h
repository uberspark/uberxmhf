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

/**
 * Modified for XMHF.
 */

#ifndef _SYS_STDINT_H_
#define _SYS_STDINT_H_

/*
 * Basic types upon which most other types are built.
 */
typedef signed char           __int8_t;
typedef unsigned char           __uint8_t;
typedef short                   __int16_t;
typedef unsigned short          __uint16_t;
typedef int                     __int32_t;
typedef unsigned int            __uint32_t;

/* LONGLONG */
typedef long long               __int64_t;
/* LONGLONG */
typedef unsigned long long      __uint64_t;

/*
 * Standard type definitions.
 */
typedef unsigned long   __clock_t;              /* clock()... */
typedef unsigned int    __cpumask_t;
typedef __int32_t       __critical_t;
typedef long double     __double_t;
typedef long double     __float_t;
typedef __int32_t       __intfptr_t;
typedef __int64_t       __intmax_t;
typedef __int32_t       __intptr_t;
typedef __int32_t       __int_fast8_t;
typedef __int32_t       __int_fast16_t;
typedef __int32_t       __int_fast32_t;
typedef __int64_t       __int_fast64_t;
typedef __int8_t        __int_least8_t;
typedef __int16_t       __int_least16_t;
typedef __int32_t       __int_least32_t;
typedef __int64_t       __int_least64_t;
typedef __int32_t       __ptrdiff_t;            /* ptr1 - ptr2 */
typedef __int32_t       __register_t;
typedef __int32_t       __segsz_t;              /* segment size (in pages) */
typedef __uint32_t      __size_t;               /* sizeof() */
typedef __int32_t       __ssize_t;              /* byte count or error */
typedef __int32_t       __time_t;               /* time()... */
typedef __uint32_t      __uintfptr_t;
typedef __uint64_t      __uintmax_t;
typedef __uint32_t      __uintptr_t;
typedef __uint32_t      __uint_fast8_t;
typedef __uint32_t      __uint_fast16_t;
typedef __uint32_t      __uint_fast32_t;
typedef __uint64_t      __uint_fast64_t;
typedef __uint8_t       __uint_least8_t;
typedef __uint16_t      __uint_least16_t;
typedef __uint32_t      __uint_least32_t;
typedef __uint64_t      __uint_least64_t;
typedef __uint32_t      __u_register_t;

typedef __uint32_t off_t;


#if !defined(__cplusplus) || defined(__STDC_CONSTANT_MACROS)

#define INT8_C(c)               (c)
#define INT16_C(c)              (c)
#define INT32_C(c)              (c)
#define INT64_C(c)              (c ## LL)

#define UINT8_C(c)              (c)
#define UINT16_C(c)             (c)
#define UINT32_C(c)             (c ## U)
#define UINT64_C(c)             (c ## ULL)

#define INTMAX_C(c)             (c ## LL)
#define UINTMAX_C(c)            (c ## ULL)

#endif /* !defined(__cplusplus) || defined(__STDC_CONSTANT_MACROS) */

#if !defined(__cplusplus) || defined(__STDC_LIMIT_MACROS)

/*
 * ISO/IEC 9899:1999
 * 7.18.2.1 Limits of exact-width integer types
 */
/* Minimum values of exact-width signed integer types. */
#define INT8_MIN        (-0x7f-1)
#define INT16_MIN       (-0x7fff-1)
#define INT32_MIN       (-0x7fffffff-1)
#define INT64_MIN       (-0x7fffffffffffffffLL-1)

/* Maximum values of exact-width signed integer types. */
#define INT8_MAX        0x7f
#define INT16_MAX       0x7fff
#define INT32_MAX       0x7fffffff
#define INT64_MAX       0x7fffffffffffffffLL

/* Maximum values of exact-width unsigned integer types. */
#define UINT8_MAX       0xff
#define UINT16_MAX      0xffff
#define UINT32_MAX      0xffffffffU
#define UINT64_MAX      0xffffffffffffffffULL

/*
 * ISO/IEC 9899:1999
 * 7.18.2.2  Limits of minimum-width integer types
 */
/* Minimum values of minimum-width signed integer types. */
#define INT_LEAST8_MIN  INT8_MIN
#define INT_LEAST16_MIN INT16_MIN
#define INT_LEAST32_MIN INT32_MIN
#define INT_LEAST64_MIN INT64_MIN

/* Maximum values of minimum-width signed integer types. */
#define INT_LEAST8_MAX  INT8_MAX
#define INT_LEAST16_MAX INT16_MAX
#define INT_LEAST32_MAX INT32_MAX
#define INT_LEAST64_MAX INT64_MAX

/* Maximum values of minimum-width unsigned integer types. */
#define UINT_LEAST8_MAX  UINT8_MAX
#define UINT_LEAST16_MAX UINT16_MAX
#define UINT_LEAST32_MAX UINT32_MAX
#define UINT_LEAST64_MAX UINT64_MAX

/*
 * ISO/IEC 9899:1999
 * 7.18.2.3  Limits of fastest minimum-width integer types
 */
/* Minimum values of fastest minimum-width signed integer types. */
#define INT_FAST8_MIN   INT32_MIN
#define INT_FAST16_MIN  INT32_MIN
#define INT_FAST32_MIN  INT32_MIN
#define INT_FAST64_MIN  INT64_MIN

/* Maximum values of fastest minimum-width signed integer types. */
#define INT_FAST8_MAX   INT32_MAX
#define INT_FAST16_MAX  INT32_MAX
#define INT_FAST32_MAX  INT32_MAX
#define INT_FAST64_MAX  INT64_MAX

/* Maximum values of fastest minimum-width unsigned integer types. */
#define UINT_FAST8_MAX  UINT32_MAX
#define UINT_FAST16_MAX UINT32_MAX
#define UINT_FAST32_MAX UINT32_MAX
#define UINT_FAST64_MAX UINT64_MAX

/*
 * ISO/IEC 9899:1999
 * 7.18.2.4  Limits of integer types capable of holding object pointers
 */
#define INTPTR_MIN      INT32_MIN
#define INTPTR_MAX      INT32_MAX
#define UINTPTR_MAX     UINT32_MAX

/*
 * ISO/IEC 9899:1999
 * 7.18.2.5  Limits of greatest-width integer types
 */
#define INTMAX_MIN      INT64_MIN
#define INTMAX_MAX      INT64_MAX
#define UINTMAX_MAX     UINT64_MAX

/*
 * ISO/IEC 9899:1999
 * 7.18.3  Limits of other integer types
 */
/* Limits of ptrdiff_t. */
#define PTRDIFF_MIN     INT32_MIN
#define PTRDIFF_MAX     INT32_MAX

/* Limit of size_t. */
#define SIZE_MAX        UINT32_MAX

#ifndef WCHAR_MIN /* Limits of wchar_t. */
#define WCHAR_MIN       INT32_MIN
#define WCHAR_MAX       INT32_MAX
#endif

/* Limits of wint_t. */
#define WINT_MIN        INT32_MIN
#define WINT_MAX        INT32_MAX

#endif /* !defined(__cplusplus) || defined(__STDC_LIMIT_MACROS) */


typedef unsigned char   u_char;
typedef unsigned short  u_short;
typedef unsigned int    u_int;
typedef unsigned long   u_long;
typedef unsigned short  ushort;         /* Sys V compatibility */
typedef unsigned int    uint;           /* Sys V compatibility */


#ifndef _INT8_T_DECLARED
typedef __int8_t                int8_t;
#define _INT8_T_DECLARED
#endif

#ifndef _INT16_T_DECLARED
typedef __int16_t               int16_t;
#define _INT16_T_DECLARED
#endif

#ifndef _INT32_T_DECLARED
typedef __int32_t               int32_t;
#define _INT32_T_DECLARED
#endif

#ifndef _INT64_T_DECLARED
typedef __int64_t               int64_t;
#define _INT64_T_DECLARED
#endif

#ifndef _UINT8_T_DECLARED
typedef __uint8_t               uint8_t;
#define _UINT8_T_DECLARED
#endif

#ifndef _UINT16_T_DECLARED
typedef __uint16_t              uint16_t;
#define _UINT16_T_DECLARED
#endif

#ifndef _UINT32_T_DECLARED
typedef __uint32_t              uint32_t;
#define _UINT32_T_DECLARED
#endif

#ifndef _UINT64_T_DECLARED
typedef __uint64_t              uint64_t;
#define _UINT64_T_DECLARED
#endif

#ifndef _INTPTR_T_DECLARED
typedef __intptr_t      intptr_t;
typedef __uintptr_t     uintptr_t;
#define _INTPTR_T_DECLARED
#endif

#ifndef _SIZE_T_DECLARED
typedef __size_t        size_t;
#define _SIZE_T_DECLARED
#endif

#ifndef _SSIZE_T_DECLARED
typedef __ssize_t        ssize_t;
#define _SSIZE_T_DECLARED
#endif


typedef __int_least8_t          int_least8_t;
typedef __int_least16_t         int_least16_t;
typedef __int_least32_t         int_least32_t;
typedef __int_least64_t         int_least64_t;

typedef __uint_least8_t         uint_least8_t;
typedef __uint_least16_t        uint_least16_t;
typedef __uint_least32_t        uint_least32_t;
typedef __uint_least64_t        uint_least64_t;

typedef __int_fast8_t           int_fast8_t;
typedef __int_fast16_t          int_fast16_t;
typedef __int_fast32_t          int_fast32_t;
typedef __int_fast64_t          int_fast64_t;

typedef __uint_fast8_t          uint_fast8_t;
typedef __uint_fast16_t         uint_fast16_t;
typedef __uint_fast32_t         uint_fast32_t;
typedef __uint_fast64_t         uint_fast64_t;

typedef __intmax_t              intmax_t;
typedef __uintmax_t             uintmax_t;

#ifndef _INTPTR_T_DECLARED
typedef __intptr_t              intptr_t;
typedef __uintptr_t             uintptr_t;
#define _INTPTR_T_DECLARED
#endif

typedef uint8_t         u8;
typedef uint16_t        u16;
typedef uint32_t        u32;
typedef uint64_t        u64;

typedef int64_t         s64;
typedef int32_t         s32;
typedef int16_t         s16;
typedef int8_t          s8;

typedef __uint8_t       u_int8_t;       /* unsigned integrals (deprecated) */
typedef __uint16_t      u_int16_t;
typedef __uint32_t      u_int32_t;
typedef __uint64_t      u_int64_t;

typedef __uint64_t      u_quad_t;       /* quads (deprecated) */
typedef __int64_t       quad_t;
typedef quad_t *        qaddr_t;

typedef char *          caddr_t;        /* core address */
typedef const char *  c_caddr_t;      /* core address, pointer to const */
typedef volatile char *v_caddr_t;     /* core address, pointer to volatile */





#endif /* !_SYS_STDINT_H_ */
