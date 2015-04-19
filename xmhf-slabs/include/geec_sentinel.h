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

// XMHF/GEEC sentinel header file
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __GEEC_SENTINEL_H_
#define __GEEC_SENTINEL_H_

#define XMHF_HIC_SLABCALL                   (0xA0)
#define XMHF_HIC_SLABRET                    (0xA1)

#define XMHF_HIC_SLABCALLEXCEPTION          (0xA2)
#define XMHF_HIC_SLABRETEXCEPTION           (0xA3)

#define XMHF_HIC_SLABCALLINTERCEPT          (0xA4)
#define XMHF_HIC_SLABRETINTERCEPT           (0xA5)


#ifndef __ASSEMBLY__

typedef struct {
    u64 src_slabid;
    u64 dst_slabid;
    u64 hic_calltype;
    u64 return_address;
    void *oparams;
    void *newoparams;
    u64 oparams_size;
    u64 iparams_size;
} __xmhfhic_safestack_element_t;

typedef void (*FPSLABMAIN)(slab_params_t *sp);


extern __attribute__((section(".data"))) __xmhfhic_safestack_element_t __xmhfhic_safestack[MAX_PLATFORM_CPUS][512];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) x_slab_info_t _xmhfhic_common_slab_info_table[XMHF_HIC_MAX_SLABS];
extern __attribute__((section(".data"))) u64 __xmhfhic_safestack_indices[MAX_PLATFORM_CPUS];



void __xmhfhic_rtm_uapihandler(slab_params_t *sp);
void __xmhfhic_rtm_trampolinehandler(slab_params_t *sp);

bool __xmhfhic_callcaps(u64 src_slabid, u64 dst_slabid);
//void __xmhfhic_safepush(u64 cpuid, u64 src_slabid, u64 dst_slabid, u64 hic_calltype, u64 return_address,
//                        slab_output_params_t *oparams, slab_output_params_t *newoparams, u64 oparams_size, u64 iparams_size);
//void __xmhfhic_safepop(u64 cpuid, u64 *src_slabid, u64 *dst_slabid, u64 *hic_calltype, u64 *return_address,
//                       slab_output_params_t **oparams, slab_output_params_t **newoparams, u64 *oparams_size, u64 *iparams_size);
void __xmhfhic_rtm_intercept(x86regs_t *r);
//void __xmhfhic_rtm_exception_stub(x86vmx_exception_frame_t *exframe);
//void __xmhfhic_rtm_trampoline(u64 hic_calltype, slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 dst_slabid, u64 src_slabid, u64 cpuid, u64 return_address, u64 return_rsp);



CASM_FUNCDECL(void __xmhfhic_rtm_intercept_stub(void *noparam));
CASM_FUNCDECL(void __xmhfhic_rtm_trampoline_stub(void *noparam));
CASM_FUNCDECL(void __xmhfhic_trampoline_slabxfer_h2h(u64 iparams,u64 iparams_size,u64 entrystub,u64 slabtos,u64 oparams,u64 oparams_size,u64 src_slabid,u64 cpuid));
CASM_FUNCDECL(void __xmhfhic_trampoline_slabxfer_h2g(void *noparam));
CASM_FUNCDECL(void __xmhfhic_trampoline_slabxfer_callexception(u64 iparams,u64 iparams_size,u64 entrystub,u64 slabtos,u64 src_slabid,u64 cpuid));
CASM_FUNCDECL(void __xmhfhic_trampoline_slabxfer_callintercept(u64 entrystub,u64 slabtos,u64 src_slabid,u64 cpuid));
CASM_FUNCDECL(void __xmhfhic_trampoline_slabxfer_retintercept(u64 addrgprs));
CASM_FUNCDECL(void __xmhfhic_trampoline_slabxfer_retexception(u64 addr_exframe));

void _geec_sentinel_exception_stub(x86vmx_exception_frame_t *exframe);


CASM_FUNCDECL(void _geec_sentinel_xfer_vft_prog_to_vft_prog(u32 entry_point, void *caller_stack_frame));
CASM_FUNCDECL(void _geec_sentinel_xfer_exception_to_vft_prog(u32 entry_point, void *caller_stack_frame));
CASM_FUNCDECL(void _geec_sentinel_xfer_ret_from_exception(x86vmx_exception_frame_t *exframe));
CASM_FUNCDECL(u32 _geec_sentinel_xfer_vft_prog_to_uvt_uvu_prog_guest(void *noparam));


#endif // __ASSEMBLY__


#endif /* __GEEC_SENTINEL_H_ */
