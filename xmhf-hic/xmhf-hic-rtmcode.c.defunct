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
 * slab trampoline that is mapped into every slab memory view
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
//#include <xmhf-core.h>
#include <xmhf-debug.h>


bool __xmhfhic_callcaps(u64 src_slabid, u64 dst_slabid){
    if(_xmhfhic_common_slab_info_table[src_slabid].slab_callcaps & HIC_SLAB_CALLCAP(dst_slabid))
        return true;
    else
        return false;
}


void __xmhfhic_safepush(u64 cpuid, u64 src_slabid, u64 dst_slabid, u64 hic_calltype, u64 return_address,
                        slab_output_params_t *oparams, slab_output_params_t *newoparams, u64 oparams_size, u64 iparams_size){
    u64 safestack_index =  __xmhfhic_safestack_indices[(u32)cpuid];
    __xmhfhic_safestack[(u32)cpuid][safestack_index].src_slabid = src_slabid;
    __xmhfhic_safestack[(u32)cpuid][safestack_index].dst_slabid = dst_slabid;
    __xmhfhic_safestack[(u32)cpuid][safestack_index].hic_calltype = hic_calltype;
    __xmhfhic_safestack[(u32)cpuid][safestack_index].return_address = return_address;
    __xmhfhic_safestack[(u32)cpuid][safestack_index].oparams = oparams;
    __xmhfhic_safestack[(u32)cpuid][safestack_index].newoparams = newoparams;
    __xmhfhic_safestack[(u32)cpuid][safestack_index].oparams_size = oparams_size;
    __xmhfhic_safestack[(u32)cpuid][safestack_index].iparams_size = iparams_size;

    safestack_index++;
    __xmhfhic_safestack_indices[(u32)cpuid] = safestack_index;
}

void __xmhfhic_safepop(u64 cpuid, u64 *src_slabid, u64 *dst_slabid, u64 *hic_calltype, u64 *return_address,
                       slab_output_params_t **oparams, slab_output_params_t **newoparams, u64 *oparams_size, u64 *iparams_size){
    u64 safestack_index =  __xmhfhic_safestack_indices[(u32)cpuid]-1;
    *src_slabid = __xmhfhic_safestack[(u32)cpuid][safestack_index].src_slabid;
    *dst_slabid = __xmhfhic_safestack[(u32)cpuid][safestack_index].dst_slabid;
    *hic_calltype = __xmhfhic_safestack[(u32)cpuid][safestack_index].hic_calltype;
    *return_address = __xmhfhic_safestack[(u32)cpuid][safestack_index].return_address;
    *oparams = __xmhfhic_safestack[(u32)cpuid][safestack_index].oparams;
    *newoparams = __xmhfhic_safestack[(u32)cpuid][safestack_index].newoparams;
    *oparams_size = __xmhfhic_safestack[(u32)cpuid][safestack_index].oparams_size;
    *iparams_size = __xmhfhic_safestack[(u32)cpuid][safestack_index].iparams_size;

    __xmhfhic_safestack_indices[(u32)cpuid] = safestack_index;
}

