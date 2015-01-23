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
//
#ifndef __XMHF_CORE_H_
#define __XMHF_CORE_H_

#define XC_HYPAPPCB_CHAIN                       (1)
#define XC_HYPAPPCB_NOCHAIN                     (2)

#define XC_HYPAPPCB_INITIALIZE                  (1)
#define XC_HYPAPPCB_HYPERCALL                   (2)
#define XC_HYPAPPCB_MEMORYFAULT                 (3)
#define XC_HYPAPPCB_SHUTDOWN                    (4)
#define XC_HYPAPPCB_TRAP_IO                     (5)
#define XC_HYPAPPCB_TRAP_INSTRUCTION            (6)
#define XC_HYPAPPCB_TRAP_EXCEPTION              (7)


#define XC_HYPAPPCB_TRAP_INSTRUCTION_CPUID      (0x60)
#define XC_HYPAPPCB_TRAP_INSTRUCTION_WRMSR      (0x61)
#define XC_HYPAPPCB_TRAP_INSTRUCTION_RDMSR      (0x62)


typedef struct {
    u64 cbtype;
    u64 cbqual;
    u64 guest_slab_index;
}__attribute__((packed)) xc_hypappcb_inputparams_t;


typedef struct {
    u64 cbresult;
}__attribute__((packed)) xc_hypappcb_outputparams_t;


typedef struct {
    u64 xmhfhic_slab_index;
    u64 cbmask;
} __attribute__((packed)) xc_hypapp_info_t;


#define XC_HYPAPPCB_MASK(x) (1 << x)



static xc_hypapp_info_t _xcihub_hypapp_info_table[] = {
/*    {
        XMHF_HYP_SLAB_XHHYPERDEP,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_MEMORYFAULT) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },

    {
        XMHF_HYP_SLAB_XHAPPROVEXEC,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_MEMORYFAULT) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },

    {
        XMHF_HYP_SLAB_XHSSTEPTRACE,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_TRAP_EXCEPTION) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },
*/
    {
        XMHF_HYP_SLAB_XHSYSCALLLOG,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_MEMORYFAULT) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_TRAP_INSTRUCTION) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },

};

#define HYPAPP_INFO_TABLE_NUMENTRIES (sizeof(_xcihub_hypapp_info_table)/sizeof(_xcihub_hypapp_info_table[0]))


static inline u64 xc_hcbinvoke(u64 cbtype, u64 cbqual, u64 guest_slab_index){
    u64 status = XC_HYPAPPCB_CHAIN;
    u64 i;
    xc_hypappcb_inputparams_t hcb_iparams;
    xc_hypappcb_outputparams_t hcb_oparams;

    hcb_iparams.cbtype = cbtype;
    hcb_iparams.cbqual = cbqual;
    hcb_iparams.guest_slab_index = guest_slab_index;

    for(i=0; i < HYPAPP_INFO_TABLE_NUMENTRIES; i++){
        if(_xcihub_hypapp_info_table[i].cbmask & XC_HYPAPPCB_MASK(cbtype)){
            XMHF_SLAB_CALL(hypapp, _xcihub_hypapp_info_table[i].xmhfhic_slab_index, &hcb_iparams, sizeof(hcb_iparams), &hcb_oparams, sizeof(hcb_oparams));
            if(hcb_oparams.cbresult == XC_HYPAPPCB_NOCHAIN){
                status = XC_HYPAPPCB_NOCHAIN;
                break;
            }
        }
    }

    return status;
}

#endif /* __XMHF_CORE_H_ */
