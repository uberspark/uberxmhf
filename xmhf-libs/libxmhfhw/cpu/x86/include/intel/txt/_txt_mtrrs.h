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

/*
 * mtrrs.c: Intel(r) TXT MTRR-related definitions
 *
 * Copyright (c) 2003-2010, Intel Corporation
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above
 *     copyright notice, this list of conditions and the following
 *     disclaimer in the documentation and/or other materials provided
 *     with the distribution.
 *   * Neither the name of the Intel Corporation nor the names of its
 *     contributors may be used to endorse or promote products derived
 *     from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

/*
 * Modified for XMHF by jonmccune@cmu.edu, 2011.01.04
 */

#ifndef __TXT_MTRRS_H__
#define __TXT_MTRRS_H__

/* XXX TODO eliminate this dependency.  txt_heap.h is also dependent
 * on the current file.  tboot code has the ugly structure.  we should
 * do better. */
#include "_txt_acmod.h"

enum fix_mtrr_t {
    MTRR_FIX64K_00000 = 0x250,
    MTRR_FIX16K_80000 = 0x258,
    MTRR_FIX16K_A0000 = 0x259,
    MTRR_FIX4K_C0000  = 0x268,
    MTRR_FIX4K_C8000  = 0x269,
    MTRR_FIX4K_D0000  = 0x26A,
    MTRR_FIX4K_D8000  = 0x26B,
    MTRR_FIX4K_E0000  = 0x26C,
    MTRR_FIX4K_E8000  = 0x26D,
    MTRR_FIX4K_F0000  = 0x26E,
    MTRR_FIX4K_F8000  = 0x26F
};

typedef union {
    uint64_t raw;
    uint8_t  type[8];
} mtrr_fix_types_t;

enum var_mtrr_t {
    MTRR_PHYS_BASE0_MSR = 0x200,
    MTRR_PHYS_MASK0_MSR = 0x201,
    MTRR_PHYS_BASE1_MSR = 0x202,
    MTRR_PHYS_MASK1_MSR = 0x203,
    MTRR_PHYS_BASE2_MSR = 0x204,
    MTRR_PHYS_MASK2_MSR = 0x205,
    MTRR_PHYS_BASE3_MSR = 0x206,
    MTRR_PHYS_MASK3_MSR = 0x207,
    MTRR_PHYS_BASE4_MSR = 0x208,
    MTRR_PHYS_MASK4_MSR = 0x209,
    MTRR_PHYS_BASE5_MSR = 0x20A,
    MTRR_PHYS_MASK5_MSR = 0x20B,
    MTRR_PHYS_BASE6_MSR = 0x20C,
    MTRR_PHYS_MASK6_MSR = 0x20D,
    MTRR_PHYS_BASE7_MSR = 0x20E,
    MTRR_PHYS_MASK7_MSR = 0x20F
};

typedef union {
    uint64_t	raw;
    struct {
        uint64_t vcnt        : 8;    /* num variable MTRR pairs */
        uint64_t fix         : 1;    /* fixed range MTRRs are supported */
        uint64_t reserved1   : 1;
        uint64_t wc          : 1;    /* write-combining mem type supported */
        uint64_t reserved2   : 53;
    };
} mtrr_cap_t;

typedef union {
    uint64_t	raw;
    struct {
        uint64_t type        : 8;
        uint64_t reserved1   : 2;
        uint64_t fe          : 1;    /* fixed MTRR enable */
        uint64_t e           : 1;    /* (all) MTRR enable */
        uint64_t reserved2   : 52;
    };
} mtrr_def_type_t;

typedef union {
    uint64_t	raw;
    struct {
        uint64_t type      : 8;
        uint64_t reserved1 : 4;
        /* TBD: the end of base really depends on MAXPHYADDR, but since */
        /* the MTRRs are set for SINIT and it must be <4GB, can use 24b */
        uint64_t base      : 24;
        uint64_t reserved2 : 28;
    };
} mtrr_physbase_t;

typedef union {
    uint64_t	raw;
    struct {
        uint64_t reserved1 : 11;
        uint64_t v         : 1;      /* valid */
        /* TBD: the end of mask really depends on MAXPHYADDR, but since */
        /* the MTRRs are set for SINIT and it must be <4GB, can use 24b */
        uint64_t mask      : 24;
        uint64_t reserved2 : 28;
    };
} mtrr_physmask_t;

/* current procs only have 8, so this should hold us for a while */
#define MAX_VARIABLE_MTRRS      16

typedef struct {
    mtrr_def_type_t	    mtrr_def_type;
    int	                num_var_mtrrs;
    mtrr_physbase_t     mtrr_physbases[MAX_VARIABLE_MTRRS];
    mtrr_physmask_t     mtrr_physmasks[MAX_VARIABLE_MTRRS];
} mtrr_state_t;

extern bool set_mtrrs_for_acmod(acm_hdr_t *hdr);
extern void print_mtrrs(const mtrr_state_t *saved_state);
extern void save_mtrrs(mtrr_state_t *saved_state);
extern void set_all_mtrrs(bool enable);
extern bool set_mem_type(void *base, uint32_t size, uint32_t mem_type);
extern void restore_mtrrs(mtrr_state_t *saved_state);
extern bool validate_mtrrs(const mtrr_state_t *saved_state);

#endif /*__TXT_MTRRS_H__ */


/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
