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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

/*-
 * Copyright (c) 1982, 1986, 1991, 1993, 1994
 *      The Regents of the University of California.  All rights reserved.
 * (c) UNIX System Laboratories, Inc.
 * All or some portions of this file are derived from material licensed
 * to the University of California by American Telephone and Telegraph
 * Co. or Unix System Laboratories, Inc. and are reproduced herein with
 * the permission of UNIX System Laboratories, Inc.
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
 *      @(#)types.h     8.6 (Berkeley) 2/19/95
 * $FreeBSD: stable/8/sys/sys/types.h 199583 2009-11-20 15:27:52Z jhb $
 */

/**
 * Modified for EMHF.
 */

#ifndef _SYS_TYPES_H_
#define _SYS_TYPES_H_

/* Machine type dependent parameters. */
#include <sys/i386_endian.h>
#include <sys/i386_types.h>

typedef unsigned char   u_char;
typedef unsigned short  u_short;
typedef unsigned int    u_int;
typedef unsigned long   u_long;
typedef unsigned short  ushort;         /* Sys V compatibility */
typedef unsigned int    uint;           /* Sys V compatibility */

/*
 * XXX POSIX sized integrals that should appear only in <sys/stdint.h>.
 */
#ifndef _INT8_T_DECLARED
typedef __int8_t        int8_t;
#define _INT8_T_DECLARED
#endif

#ifndef _INT16_T_DECLARED
typedef __int16_t       int16_t;
#define _INT16_T_DECLARED
#endif

#ifndef _INT32_T_DECLARED
typedef __int32_t       int32_t;
#define _INT32_T_DECLARED
#endif

#ifndef _INT64_T_DECLARED
typedef __int64_t       int64_t;
#define _INT64_T_DECLARED
#endif

#ifndef _UINT8_T_DECLARED
typedef __uint8_t       uint8_t;
#define _UINT8_T_DECLARED
#endif

#ifndef _UINT16_T_DECLARED
typedef __uint16_t      uint16_t;
#define _UINT16_T_DECLARED
#endif

#ifndef _UINT32_T_DECLARED
typedef __uint32_t      uint32_t;
#define _UINT32_T_DECLARED
#endif

#ifndef _UINT64_T_DECLARED
typedef __uint64_t      uint64_t;
#define _UINT64_T_DECLARED
#endif

#ifndef _INTPTR_T_DECLARED
typedef __intptr_t      intptr_t;
typedef __uintptr_t     uintptr_t;
#define _INTPTR_T_DECLARED
#endif

typedef __uint8_t       u_int8_t;       /* unsigned integrals (deprecated) */
typedef __uint16_t      u_int16_t;
typedef __uint32_t      u_int32_t;
typedef __uint64_t      u_int64_t;

typedef __uint64_t      u_quad_t;       /* quads (deprecated) */
typedef __int64_t       quad_t;
typedef quad_t *        qaddr_t;

typedef char *          caddr_t;        /* core address */
typedef __const char *  c_caddr_t;      /* core address, pointer to const */
typedef __volatile char *v_caddr_t;     /* core address, pointer to volatile */

#endif /* !_SYS_TYPES_H_ */
