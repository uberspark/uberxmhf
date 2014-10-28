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

//#include <_xctypes.h>			//core specific data types
//#include <_xchypapp.h>			//hypapp callback declarations


#define XC_HYPAPPCB_HANDLED                   (1)
#define XC_HYPAPPCB_UNHANDLED                 (0)

#define XC_HYPAPPCB_INITIALIZE                  (1)
#define XC_HYPAPPCB_HYPERCALL                   (2)
#define XC_HYPAPPCB_MEMORYFAULT                 (3)
#define XC_HYPAPPCB_TRAP_IO                     (4)
#define XC_HYPAPPCB_TRAP_INSTRUCTION            (5)
#define XC_HYPAPPCB_TRAP_EXCEPTION              (6)

typedef struct {
    u64 cbtype;
}__attribute__((packed)) xc_hypappcb_inputparams_t


typedef struct {
    u64 cbresult;
}__attribute__((packed)) xc_hypappcb_outputparams_t


typedef struct {
    u64 xmhfhic_slab_index;
    u64 cbmask;
} __attribute__((packed)) xc_hypapp_info_t;



#endif /* __XMHF_CORE_H_ */
