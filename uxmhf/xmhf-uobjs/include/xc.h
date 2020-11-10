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

//xmhf.h - main XMHF core header file
// this orchestrates the inclusion of other core component specific
// headers
//author: amit vasudevan (amitvasudevan@acm.org)
//author: matt mccormack (matthew.mccormack@live.com)
//
#ifndef __XC_H_
#define __XC_H_


#ifndef __ASSEMBLY__
#include <xmhfcrypto.h>

#endif // __ASSEMBLY__

#define XC_HYPAPPCB_CHAIN                       (1)
#define XC_HYPAPPCB_NOCHAIN                     (2)

#define XC_HYPAPPCB_INITIALIZE                  (0)
#define XC_HYPAPPCB_HYPERCALL                   (1)
#define XC_HYPAPPCB_MEMORYFAULT                 (2)
#define XC_HYPAPPCB_SHUTDOWN                    (3)
#define XC_HYPAPPCB_TRAP_IO                     (4)
#define XC_HYPAPPCB_TRAP_INSTRUCTION            (5)
#define XC_HYPAPPCB_TRAP_EXCEPTION              (6)

#define XC_HYPAPPCB_MAXMASK			(6)

#define XC_HYPAPPCB_TRAP_INSTRUCTION_CPUID      (0x60)
#define XC_HYPAPPCB_TRAP_INSTRUCTION_WRMSR      (0x61)
#define XC_HYPAPPCB_TRAP_INSTRUCTION_RDMSR      (0x62)

#ifndef __ASSEMBLY__


typedef struct {
    uint32_t cbtype;
    uint32_t cbqual;
    uint32_t guest_slab_index;
    uint32_t cbresult;
}__attribute__((packed)) xc_hypappcb_params_t;

typedef struct {
    uint32_t xmhfhic_slab_index;
    uint32_t cbmask;
} __attribute__((packed)) xc_hypapp_info_t;


#define XC_HYPAPPCB_MASK(x) (1 << x)

static xc_hypapp_info_t _xcihub_hypapp_info_table[] = {
    {
        XMHFGEEC_SLAB_XH_UHCALLTEST,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_INITIALIZE) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },
    
    {
        XMHFGEEC_SLAB_XH_HYPERDEP,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_INITIALIZE) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_MEMORYFAULT) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },

    //{
    //   XMHFGEEC_SLAB_XH_APRVEXEC,
    //    (XC_HYPAPPCB_MASK(XC_HYPAPPCB_INITIALIZE) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_MEMORYFAULT) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    //},

    {
        XMHFGEEC_SLAB_XH_SSTEPTRACE,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_INITIALIZE) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_TRAP_EXCEPTION) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },

    {
        XMHFGEEC_SLAB_XH_SYSCALLLOG,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_INITIALIZE) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_MEMORYFAULT) )
    }

};

#define HYPAPP_INFO_TABLE_NUMENTRIES (sizeof(_xcihub_hypapp_info_table)/sizeof(_xcihub_hypapp_info_table[0]))


#endif //__ASSEMBLY__


#endif /* __XC_H_ */
