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
 *
 *  slab memory pagetable uAPI
 *
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */

#ifndef __UAPI_SLABMEMPGTBL_H__
#define __UAPI_SLABMEMPGTBL_H__

#define XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL     0
#define XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR 1
#define XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR 2
#define XMHFGEEC_UAPI_SLABMEMPGTBL_FLUSHTLB			3
#define UAPI_UGMPGTBL_GETMPGTBLBASE					4




#ifndef __ASSEMBLY__

extern __attribute__((section(".rwdatahdr"))) __attribute__((aligned(4096))) uint64_t _slabmempgtbl_lvl4t[XMHFGEEC_TOTAL_UGSLABS][PAE_MAXPTRS_PER_PML4T];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t _slabmempgtbl_lvl3t[XMHFGEEC_TOTAL_UGSLABS][PAE_MAXPTRS_PER_PDPT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t _slabmempgtbl_lvl2t[XMHFGEEC_TOTAL_UGSLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096)))  uint64_t _slabmempgtbl_lvl1t[XMHFGEEC_TOTAL_UGSLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT][PAE_PTRS_PER_PT];



typedef struct {
    uint32_t dst_slabid;
}__attribute__((packed)) xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t;

typedef struct {
    uint32_t dst_slabid;
    uint64_t gpa;
    uint64_t entry;
}__attribute__((packed)) xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t;

typedef struct {
    uint32_t dst_slabid;
    uint64_t gpa;
    uint64_t result_entry;
}__attribute__((packed)) xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t;

typedef struct {
    uint32_t dst_slabid;
}__attribute__((packed)) xmhfgeec_uapi_slabmempgtbl_flushtlb_params_t;


typedef struct {
    uint32_t dst_slabid;
    uint32_t mpgtblbase;
}__attribute__((packed)) uapi_ugmpgtbl_getmpgtblbase_params_t;



/*@
  requires \valid(p);
@*/
void _ugmpgtbl_getmpgtblbase(uapi_ugmpgtbl_getmpgtblbase_params_t *p);


/*@
  requires \valid(flushtlbp);
@*/
void _slabmempgtbl_flushtlb(xmhfgeec_uapi_slabmempgtbl_flushtlb_params_t *flushtlbp);


/*@
  requires \valid(setentryforpaddrp);
@*/
void _slabmempgtbl_setentryforpaddr(xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp);



/*@
	requires \valid(getentryforpaddrp);
@*/
void _slabmempgtbl_getentryforpaddr(xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *getentryforpaddrp);



/*@
	requires \valid(initmempgtblp);
@*/
void _slabmempgtbl_initmempgtbl(xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *initmempgtblp);






#endif	//__ASSEMBLY__

#endif //__UAPI_SLABMEMPGTBL_H__
