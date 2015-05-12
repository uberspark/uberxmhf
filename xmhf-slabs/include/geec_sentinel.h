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


#define GEEC_SENTINEL_MEMOFFSETS_SYSENTERHANDLER_IDX        0
#define GEEC_SENTINEL_MEMOFFSETS_INTERCEPTHANDLER_IDX       1
#define GEEC_SENTINEL_MEMOFFSETS_EXCEPTIONHANDLERS_IDX      2



#ifndef __ASSEMBLY__

typedef struct {
    u32 src_slabid;
    u32 dst_slabid;
    u32 hic_calltype;
    void *caller_stack_frame;
    slab_params_t *sp;
}__attribute__((packed)) __xmhfhic_safestack_element_t;


extern __attribute__((section(".data"))) __xmhfhic_safestack_element_t __xmhfhic_safestack[MAX_PLATFORM_CPUS][512];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) xmhfgeec_slab_info_t _xmhfhic_common_slab_info_table[XMHFGEEC_TOTAL_SLABS];
extern __attribute__((section(".data"))) u64 __xmhfhic_safestack_indices[MAX_PLATFORM_CPUS];



CASM_FUNCDECL(void _geec_sentinel_intercept_casmstub(void *noparam));
CASM_FUNCDECL(void _geec_sentinel_sysenter_casmstub(void *noparam));


void _geec_sentinel_intercept_stub(x86regs_t *r);
void _geec_sentinel_exception_stub(x86vmx_exception_frame_t *exframe);
void _geec_sentinel_sysenter_stub(slab_params_t *sp, void *caller_stack_frame);


CASM_FUNCDECL(void _geec_sentinel_xfer_vft_prog_to_vft_prog(u32 entry_point, void *caller_stack_frame));
CASM_FUNCDECL(void _geec_sentinel_xfer_exception_to_vft_prog(u32 entry_point, void *caller_stack_frame));
CASM_FUNCDECL(void _geec_sentinel_xfer_ret_from_exception(x86vmx_exception_frame_t *exframe));
CASM_FUNCDECL(u32 _geec_sentinel_xfer_vft_prog_to_uvt_uvu_prog_guest(void *noparam));
CASM_FUNCDECL(void _geec_sentinel_xfer_intercept_to_vft_prog(u32 entry_point, void *caller_stack_frame));
CASM_FUNCDECL(void _geec_sentinel_xfer_ret_from_intercept(x86regs_t *r));
CASM_FUNCDECL(void _geec_sentinel_xfer_vft_prog_to_uvt_uvu_prog(u32 entry_point, void *callee_stack_frame));
CASM_FUNCDECL(void _geec_sentinel_xfer_ret_vft_prog_to_uvt_uvu_prog(void *caller_stack_frame));
CASM_FUNCDECL(void _geec_sentinel_xfer_call_uvt_uvu_prog_to_vft_prog(u32 entry_point, void *callee_stack_frame));
CASM_FUNCDECL(void _geec_sentinel_xfer_ret_uvt_uvu_prog_to_vft_prog(void *caller_stack_frame));


#endif // __ASSEMBLY__


#endif /* __GEEC_SENTINEL_H_ */
