
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

// XMHF core init verification module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhf-debug.h>
#include <xmhf-core.h>

#include <xcinit.h>

static XMHF_BOOTINFO xcbootinfo_store = {
	.magic= RUNTIME_PARAMETER_BLOCK_MAGIC,
};

// XMHF boot information block
XMHF_BOOTINFO *xcbootinfo= &xcbootinfo_store;

u8 sourceslab_rwdatabuffer[128];
u8 destinationslab_rwdatabuffer[128];

u64 guestslab_mempgtbl_buffer[1048576];


x_slab_info_t _x_xmhfhic_common_slab_info_table[XMHF_HIC_MAX_SLABS] = {
    //source slab
    {
        {
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            true,
            true,
            0,
            {0}
        },
        true,
        0,
        0,
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE),
        {0},
        {
            {0, 0, 0},
            {(u64)&sourceslab_rwdatabuffer, ((u64)&sourceslab_rwdatabuffer + (u64)sizeof(sourceslab_rwdatabuffer)), 0},
            {0, 0, 0},
            {0, 0, 0},
            {0, 0, 0},
        },
        0,
    },


    //destination slab
    {
        {
            0,
            0,
            0,
            (u64 *)&guestslab_mempgtbl_buffer,
            0,
            0,
            0,
            0,
            0,
            HIC_SLAB_X86VMXX86PC_GUEST,
            true,
            true,
            0,
            {0}
        },
        true,
        0,
        0,
        0,
        {0},
        {
            {0, 0, 0},
            {(u64)&destinationslab_rwdatabuffer, ((u64)&destinationslab_rwdatabuffer + (u64)sizeof(destinationslab_rwdatabuffer)), 0},
            {0, 0, 0},
            {0, 0, 0},
            {0, 0, 0},
        },
        0,
    }

};


void main(void){
    xcbootinfo->cpuinfo_numentries=1;

    xcinit_interface(NULL, 0, NULL, 0, 0, 0x8000000000000000ULL);
}
