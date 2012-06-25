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
 * smx.h: Intel(r) TXT SMX architecture-related definitions
 *
 * Copyright (c) 2003-2008, Intel Corporation
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


#ifndef __TXT_SMX_H__
#define __TXT_SMX_H__

/*
 * GETSEC[] instructions
 */

/* GETSEC instruction opcode */
#define IA32_GETSEC_OPCODE		".byte 0x0f,0x37"

/* GETSEC leaf function codes */
#define IA32_GETSEC_CAPABILITIES	0
#define IA32_GETSEC_SENTER		4
#define IA32_GETSEC_SEXIT		5
#define IA32_GETSEC_PARAMETERS		6
#define IA32_GETSEC_SMCTRL		7
#define IA32_GETSEC_WAKEUP		8

/*
 * GETSEC[] leaf functions
 */

typedef union {
    uint32_t _raw;
    struct {
        uint32_t chipset_present  : 1;
        uint32_t undefined1	  : 1;
        uint32_t enteraccs	  : 1;
        uint32_t exitac	          : 1;
        uint32_t senter	          : 1;
        uint32_t sexit	          : 1;
        uint32_t parameters	  : 1;
        uint32_t smctrl	          : 1;
        uint32_t wakeup	          : 1;
        uint32_t undefined9	  : 22;
        uint32_t extended_leafs   : 1;
    };
} capabilities_t;

static inline uint32_t __getsec_capabilities(uint32_t index)
{
    uint32_t cap;
    __asm__ __volatile__ (IA32_GETSEC_OPCODE "\n"
              : "=a"(cap)
              : "a"(IA32_GETSEC_CAPABILITIES), "b"(index));
    return cap;
}

/* helper fn. for getsec_capabilities */
/* this is arbitrary and can be increased when needed */
#define MAX_SUPPORTED_ACM_VERSIONS      16

typedef struct {
    struct {
        uint32_t mask;
        uint32_t version;
    } acm_versions[MAX_SUPPORTED_ACM_VERSIONS];
    int n_versions;
    uint32_t acm_max_size;
    uint32_t acm_mem_types;
    uint32_t senter_controls;
    bool proc_based_scrtm;
    bool preserve_mce;
} getsec_parameters_t;

///extern bool get_parameters(getsec_parameters_t *params);


static inline void __getsec_senter(uint32_t sinit_base, uint32_t sinit_size)
{
    __asm__ __volatile__ (IA32_GETSEC_OPCODE "\n"
			  :
			  : "a"(IA32_GETSEC_SENTER),
			    "b"(sinit_base),
			    "c"(sinit_size),
			    "d"(0x0));
}

static inline void __getsec_sexit(void)
{
    __asm__ __volatile__ (IA32_GETSEC_OPCODE "\n"
                          : : "a"(IA32_GETSEC_SEXIT));
}

static inline void __getsec_wakeup(void)
{
    __asm__ __volatile__ (IA32_GETSEC_OPCODE "\n"
                          : : "a"(IA32_GETSEC_WAKEUP));
}

static inline void __getsec_smctrl(void)
{
    __asm__ __volatile__ (IA32_GETSEC_OPCODE "\n"
                          : : "a"(IA32_GETSEC_SMCTRL), "b"(0x0));
}

static inline void __getsec_parameters(uint32_t index, int* param_type,
                                       uint32_t* peax, uint32_t* pebx,
                                       uint32_t* pecx)
{
    uint32_t eax=0, ebx=0, ecx=0;
    __asm__ __volatile__ (IA32_GETSEC_OPCODE "\n"
                          : "=a"(eax), "=b"(ebx), "=c"(ecx)
                          : "a"(IA32_GETSEC_PARAMETERS), "b"(index));

    if ( param_type != NULL )   *param_type = eax & 0x1f;
    if ( peax != NULL )         *peax = eax;
    if ( pebx != NULL )         *pebx = ebx;
    if ( pecx != NULL )         *pecx = ecx;
}

static inline bool txt_is_launched(void)
{
    txt_sts_t sts;

    sts._raw = read_pub_config_reg(TXTCR_STS);

    return sts.senter_done_sts;
}

bool txt_prepare_cpu(void);
tb_error_t txt_launch_environment(void *sinit_ptr, size_t sinit_size,
                                  void *phys_mle_start, size_t mle_size);
#endif /* __TXT_SMX_H__ */

/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
