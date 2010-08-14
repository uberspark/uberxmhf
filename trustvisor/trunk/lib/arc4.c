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

/*
 *  An implementation of the ARCFOUR algorithm
 *
 *  Copyright (C) 2003-2006  Christophe Devine
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License, version 2.1 as published by the Free Software Foundation.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 *  MA  02110-1301  USA
 */
/*
 *  The ARC4 algorithm was publicly disclosed on 94/09.
 *
 *  http://groups.google.com/group/sci.crypt/msg/10a300c9d21afca0
 */


#include "arc4.h"

/*
 * ARC4 key schedule
 */
void arc4_setup( arc4_context *ctx, unsigned char *key, int keylen )
{
    int i, j, k, *m, a;

    ctx->x = 0;
    ctx->y = 0;
    m = ctx->m;

    for( i = 0; i < 256; i++ )
        m[i] = i;

    j = k = 0;

    for( i = 0; i < 256; i++ )
    {
        a = m[i];
        j = (unsigned char)( j + a + key[k] );
        m[i] = m[j]; m[j] = a;
        if( ++k >= keylen ) k = 0;
    }
}

/*
 * ARC4 cipher function
 */
void arc4_crypt( arc4_context *ctx, unsigned char *buf, int buflen )
{
    int i, x, y, *m, a, b;

    x = ctx->x;
    y = ctx->y;
    m = ctx->m;

    for( i = 0; i < buflen; i++ )
    {
        x = (unsigned char)( x + 1 ); a = m[x];
        y = (unsigned char)( y + a );
        m[x] = b = m[y];
        m[y] = a;
        buf[i] ^= m[(unsigned char)( a + b )];
    }

    ctx->x = x;
    ctx->y = y;
}

/* #ifdef SELF_TEST */

/* #include <string.h> */
/* #include <stdio.h> */

/* /\* */
/*  * ARC4 tests vectors as posted by Eric Rescorla */
/*  *\/ */
/* static const unsigned char arc4_test_key[3][8] = */
/* { */
/*     { 0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF }, */
/*     { 0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF }, */
/*     { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 } */
/* }; */

/* static const unsigned char arc4_test_pt[3][8] = */
/* { */
/*     { 0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF }, */
/*     { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 }, */
/*     { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 } */
/* }; */

/* static const unsigned char arc4_test_ct[3][8] = */
/* { */
/*     { 0x75, 0xB7, 0x87, 0x80, 0x99, 0xE0, 0xC5, 0x96 }, */
/*     { 0x74, 0x94, 0xC2, 0xE7, 0x10, 0x4B, 0x08, 0x79 }, */
/*     { 0xDE, 0x18, 0x89, 0x41, 0xA3, 0x37, 0x5D, 0x3A } */
/* }; */

/* /\* */
/*  * Checkup routine */
/*  *\/ */
/* int arc4_self_test( void ) */
/* { */
/*     int i; */
/*     unsigned char buf[8]; */
/*     arc4_context ctx; */

/*     for( i = 0; i < 3; i++ ) */
/*     { */
/*         printf( "  ARC4 test #%d: ", i + 1 ); */

/*         memcpy( buf, arc4_test_pt[i], 8 ); */

/*         arc4_setup( &ctx, (unsigned char *) arc4_test_key[i], 8 ); */
/*         arc4_crypt( &ctx, buf, 8 ); */

/*         if( memcmp( buf, arc4_test_ct[i], 8 ) != 0 ) */
/*         { */
/*             printf( "failed\n" ); */
/*             return( 1 ); */
/*         } */

/*         printf( "passed\n" ); */
/*     } */

/*     printf( "\n" ); */
/*     return( 0 ); */
/* } */
/* #else */
/* int arc4_self_test( void ) */
/* { */
/*     return( 0 ); */
/* } */
/* #endif */
