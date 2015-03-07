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

// XMHF slab decls./defns.
// author: amit vasudevan (amitvasudevan@acm.org)
// XXX: need to split arch. dependent portions

#ifndef __XMHFHICSLAB_H__
#define __XMHFHICSLAB_H__

#include <xmhf-hwm.h>
#include <xmhfhw.h>

#define XMHF_HIC_UAPI                       (0x666)

#define XMHF_HIC_UAPI_CPUSTATE                  (0)

#define XMHF_HIC_UAPI_CPUSTATE_VMREAD           (1)
#define XMHF_HIC_UAPI_CPUSTATE_VMWRITE          (2)
#define XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD    (3)
#define XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE   (4)
#define XMHF_HIC_UAPI_CPUSTATE_WRMSR            (5)
#define XMHF_HIC_UAPI_CPUSTATE_RDMSR            (6)


#define XMHF_HIC_UAPI_PHYSMEM                   (16)

#define XMHF_HIC_UAPI_PHYSMEM_PEEK              (17)
#define XMHF_HIC_UAPI_PHYSMEM_POKE              (18)

#define XMHF_HIC_UAPI_MEMPGTBL                  (24)

#define XMHF_HIC_UAPI_MEMPGTBL_GETENTRY         (25)
#define XMHF_HIC_UAPI_MEMPGTBL_SETENTRY         (26)


#define GUEST_SLAB_HEADER_MAGIC     (0x76543210)

#define XMHF_HIC_SLABCALL                   (0xA0)
#define XMHF_HIC_SLABRET                    (0xA1)

#define XMHF_HIC_SLABCALLEXCEPTION          (0xA2)
#define XMHF_HIC_SLABRETEXCEPTION           (0xA3)

#define XMHF_HIC_SLABCALLINTERCEPT          (0xA4)
#define XMHF_HIC_SLABRETINTERCEPT           (0xA5)


#ifndef __ASSEMBLY__

typedef void slab_input_params_t;
typedef void slab_output_params_t;


typedef struct {
    u32 slab_ctype;
    u32 src_slabid;
    u32 dst_slabid;
    u32 cpuid;
    u32 in_out_params[16];
} __attribute__((packed)) slab_params_t;




//////
// uapi related types

typedef struct {
    u32 guest_slab_index;
    void *addr_from;
    void *addr_to;
    u32 numbytes;
}__attribute__((packed)) xmhf_hic_uapi_physmem_desc_t;

typedef struct {
    u32 guest_slab_index;
    u64 gpa;
    u64 entry;
}__attribute__((packed)) xmhf_hic_uapi_mempgtbl_desc_t;

//guest slab header data type
typedef struct {
    u32 magic;
    __attribute__((aligned(4096))) u64 lvl2mempgtbl_pml4t[PAE_MAXPTRS_PER_PDPT];
    __attribute__((aligned(4096))) u64 lvl2mempgtbl_pdpt[PAE_MAXPTRS_PER_PDPT];
    __attribute__((aligned(4096))) u64 lvl2mempgtbl_pdts[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
    __attribute__(( aligned(16) )) u64 gdt[16];
} __attribute__((packed)) guest_slab_header_t;



//////
// HIC UAPI and trampoline invocation macros



//HIC UAPI
void __slab_calluapinew(slab_params_t *sp);


#define XMHF_HIC_SLAB_UAPI_CPUSTATE(cpustatefn, iparams, oparams) \
    __slab_calluapi(XMHF_HIC_UAPI, XMHF_HIC_UAPI_CPUSTATE, cpustatefn, 0, iparams, oparams)


#define XMHF_HIC_SLAB_UAPI_PHYSMEM(physmemfn, iparams, oparams) \
    __slab_calluapi(XMHF_HIC_UAPI, XMHF_HIC_UAPI_PHYSMEM, physmemfn, 0, iparams, oparams)


#define XMHF_HIC_SLAB_UAPI_MEMPGTBL(mempgtblfn, iparams, oparams) \
    __slab_calluapi(XMHF_HIC_UAPI, XMHF_HIC_UAPI_MEMPGTBL, mempgtblfn, 0, iparams, oparams)


#define XMHF_SLAB_UAPI(sp) __slab_calluapinew(sp)


//HIC trampoline
__attribute__((naked)) u32 __slab_calltrampolinenew_h2g(void);
void __slab_calltrampolinenew(slab_params_t *sp);


#define XMHF_SLAB_CALL(dst_slabname, dst_slabid, iparams, iparams_size, oparams, oparams_size) \
    __slab_calltrampoline(0, iparams, iparams_size, oparams, oparams_size, dst_slabid)


#define XMHF_SLAB_CALLNEW(sp) \
    __slab_calltrampolinenew(sp)




//////
// slab entry stub definitions
extern void slab_main(slab_params_t *sp);
typedef void (*FPSLABMAIN)(slab_params_t *sp);


#endif //__ASSEMBLY__


#endif //__XMHFHICSLAB_H__


