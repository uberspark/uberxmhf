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

/**
 * perf.h
 *
 * This file contains constants, structs, and enums used to facilitate
 * performance data exchange between the untrusted OS and the SLB.
 *
 * Copyright (C) 2006-2008 Jonathan M. McCune
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License v2.0 as published by
 * the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 */

#ifndef __PERF_H__
#define __PERF_H__

struct st_timer_vars {
    unsigned long startlow;
    unsigned long starthigh;
    unsigned long endlow;
    unsigned long endhigh;
};


struct slb_perf_vals {
    struct st_timer_vars seal;
    struct st_timer_vars unseal;
    struct st_timer_vars tpm_seal;
    struct st_timer_vars tpm_unseal;
    struct st_timer_vars tpm_getrand;
    struct st_timer_vars tpm_getrand_min;
    struct st_timer_vars tpm_getrand_max;
    struct st_timer_vars rsa_keygen;
    struct st_timer_vars rsa_encrypt;
    struct st_timer_vars rsa_decrypt;
    struct st_timer_vars primep;
    struct st_timer_vars primeq;
    struct st_timer_vars skinit;
    struct st_timer_vars hashself;
    struct st_timer_vars pcrextend;
    unsigned long long sum_getrand;
    int num_getrand_calls;
    int num_random_byte_calls;
    unsigned long long sum_rsag_malloc;
    unsigned char pcr17[20]; /* for verifying seal is working correctly */
    struct st_timer_vars ctr_create;
    struct st_timer_vars ctr_release;
    struct st_timer_vars ctr_incr;
    struct st_timer_vars ctr_read;
    unsigned int countID;
};


#endif /* __PERF_H__ */
