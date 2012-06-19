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

/* super class file for PK algos */

/* default ... include all MPI */
/* #define LTM_ALL */

/* RSA only (does not support DH/DSA/ECC) */
#define SC_RSA_1

#define LTM_NO_FILE
#define BN_MP_NEG_C
#define BN_MP_GET_INT_C
#define BN_MP_READ_RADIX_C
#define BN_MP_TORADIX_C
#define BN_MP_WRITE_RADIX_C
#define BN_MP_MONTGOMERY_REDUCE_C
#define BN_MP_TO_UNSIGNED_BIN_N_C

/* For reference.... On an Athlon64 optimizing for speed...

   LTM's mpi.o with all functions [striped] is 142KiB in size.

*/

/* Works for RSA only, mpi.o is 68KiB */
#ifdef SC_RSA_1
   #define BN_MP_SHRINK_C
   #define BN_MP_LCM_C
   #define BN_MP_PRIME_RANDOM_EX_C
   #define BN_MP_INVMOD_C
   #define BN_MP_GCD_C
   #define BN_MP_MOD_C
   #define BN_MP_MULMOD_C
   #define BN_MP_ADDMOD_C
   #define BN_MP_EXPTMOD_C
   #define BN_MP_SET_INT_C
   #define BN_MP_INIT_MULTI_C
   #define BN_MP_CLEAR_MULTI_C
   #define BN_MP_UNSIGNED_BIN_SIZE_C
   #define BN_MP_TO_UNSIGNED_BIN_C
   #define BN_MP_MOD_D_C
   #define BN_MP_PRIME_RABIN_MILLER_TRIALS_C
   #define BN_REVERSE_C
   #define BN_PRIME_TAB_C

   /* other modifiers */
   #define BN_MP_DIV_SMALL                    /* Slower division, not critical */

   /* here we are on the last pass so we turn things off.  The functions classes are still there
    * but we remove them specifically from the build.  This also invokes tweaks in functions
    * like removing support for even moduli, etc...
    */
#ifdef LTM_LAST
   #undef  BN_MP_TOOM_MUL_C
   #undef  BN_MP_TOOM_SQR_C
   #undef  BN_MP_KARATSUBA_MUL_C
   #undef  BN_MP_KARATSUBA_SQR_C
   #undef  BN_MP_REDUCE_C
   #undef  BN_MP_REDUCE_SETUP_C
   #undef  BN_MP_DR_IS_MODULUS_C
   #undef  BN_MP_DR_SETUP_C
   #undef  BN_MP_DR_REDUCE_C
   #undef  BN_MP_REDUCE_IS_2K_C
   #undef  BN_MP_REDUCE_2K_SETUP_C
   #undef  BN_MP_REDUCE_2K_C
   #undef  BN_S_MP_EXPTMOD_C
   #undef  BN_MP_DIV_3_C
   #undef  BN_S_MP_MUL_HIGH_DIGS_C
   #undef  BN_FAST_S_MP_MUL_HIGH_DIGS_C
   #undef  BN_FAST_MP_INVMOD_C

   /* To safely undefine these you have to make sure your RSA key won't exceed the Comba threshold
    * which is roughly 255 digits [7140 bits for 32-bit machines, 15300 bits for 64-bit machines] 
    * which means roughly speaking you can handle upto 2536-bit RSA keys with these defined without
    * trouble.  
    */
   #undef  BN_S_MP_MUL_DIGS_C
   #undef  BN_S_MP_SQR_C
   /* #undef  BN_MP_MONTGOMERY_REDUCE_C */
#endif

#endif

/* $Source$ */
/* $Revision: 0.36 $ */
/* $Date: 2005-08-01 16:37:28 +0000 $ */
