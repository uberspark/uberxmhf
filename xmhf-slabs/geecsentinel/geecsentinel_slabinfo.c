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


#include <xmhf.h>
#include <xmhf-hic.h>

/*
 * slab info data structure
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */



extern u8 _xmhfhic_sharedro_start[];
extern u8 _xmhfhic_sharedro_end[];
extern u8 _xmhfhic_code_start[];
extern u8 _xmhfhic_code_end[];
extern u8 _xmhfhic_rwdata_start[];
extern u8 _xmhfhic_rwdata_end[];
extern u8 _xmhfhic_rodata_start[];
extern u8 _xmhfhic_rodata_end[];
extern u8 _xmhfhic_stack_start[];
extern u8 _xmhfhic_stack_end[];

extern u8 _slab_geecsentinel_code_start[];
extern u8 _slab_geecsentinel_code_end[];
extern u8 _slab_geecsentinel_rwdata_start[];
extern u8 _slab_geecsentinel_rwdata_end[];
extern u8 _slab_geecsentinel_rodata_start[];
extern u8 _slab_geecsentinel_rodata_end[];
extern u8 _slab_geecsentinel_stack_start[];
extern u8 _slab_geecsentinel_stack_end[];
extern u8 _slab_geecsentinel_dmadata_start[];
extern u8 _slab_geecsentinel_dmadata_end[];
extern u8 _slab_geecsentinel_entrypoint[];

extern u8 _slab_geec_primesmp_code_start[];
extern u8 _slab_geec_primesmp_code_end[];
extern u8 _slab_geec_primesmp_rwdata_start[];
extern u8 _slab_geec_primesmp_rwdata_end[];
extern u8 _slab_geec_primesmp_rodata_start[];
extern u8 _slab_geec_primesmp_rodata_end[];
extern u8 _slab_geec_primesmp_stack_start[];
extern u8 _slab_geec_primesmp_stack_end[];
extern u8 _slab_geec_primesmp_dmadata_start[];
extern u8 _slab_geec_primesmp_dmadata_end[];
extern u8 _slab_geec_primesmp_entrypoint[];

extern u8 _slab_uapi_gcpustate_code_start[];
extern u8 _slab_uapi_gcpustate_code_end[];
extern u8 _slab_uapi_gcpustate_rwdata_start[];
extern u8 _slab_uapi_gcpustate_rwdata_end[];
extern u8 _slab_uapi_gcpustate_rodata_start[];
extern u8 _slab_uapi_gcpustate_rodata_end[];
extern u8 _slab_uapi_gcpustate_stack_start[];
extern u8 _slab_uapi_gcpustate_stack_end[];
extern u8 _slab_uapi_gcpustate_dmadata_start[];
extern u8 _slab_uapi_gcpustate_dmadata_end[];
extern u8 _slab_uapi_gcpustate_entrypoint[];

extern u8 _slab_uapi_hcpustate_code_start[];
extern u8 _slab_uapi_hcpustate_code_end[];
extern u8 _slab_uapi_hcpustate_rwdata_start[];
extern u8 _slab_uapi_hcpustate_rwdata_end[];
extern u8 _slab_uapi_hcpustate_rodata_start[];
extern u8 _slab_uapi_hcpustate_rodata_end[];
extern u8 _slab_uapi_hcpustate_stack_start[];
extern u8 _slab_uapi_hcpustate_stack_end[];
extern u8 _slab_uapi_hcpustate_dmadata_start[];
extern u8 _slab_uapi_hcpustate_dmadata_end[];
extern u8 _slab_uapi_hcpustate_entrypoint[];


extern u8 _slab_uapi_slabmemacc_code_start[];
extern u8 _slab_uapi_slabmemacc_code_end[];
extern u8 _slab_uapi_slabmemacc_rwdata_start[];
extern u8 _slab_uapi_slabmemacc_rwdata_end[];
extern u8 _slab_uapi_slabmemacc_rodata_start[];
extern u8 _slab_uapi_slabmemacc_rodata_end[];
extern u8 _slab_uapi_slabmemacc_stack_start[];
extern u8 _slab_uapi_slabmemacc_stack_end[];
extern u8 _slab_uapi_slabmemacc_dmadata_start[];
extern u8 _slab_uapi_slabmemacc_dmadata_end[];
extern u8 _slab_uapi_slabmemacc_entrypoint[];

extern u8 _slab_uapi_slabmempgtbl_code_start[];
extern u8 _slab_uapi_slabmempgtbl_code_end[];
extern u8 _slab_uapi_slabmempgtbl_rwdata_start[];
extern u8 _slab_uapi_slabmempgtbl_rwdata_end[];
extern u8 _slab_uapi_slabmempgtbl_rodata_start[];
extern u8 _slab_uapi_slabmempgtbl_rodata_end[];
extern u8 _slab_uapi_slabmempgtbl_stack_start[];
extern u8 _slab_uapi_slabmempgtbl_stack_end[];
extern u8 _slab_uapi_slabmempgtbl_dmadata_start[];
extern u8 _slab_uapi_slabmempgtbl_dmadata_end[];
extern u8 _slab_uapi_slabmempgtbl_entrypoint[];



extern u8 _slab_xcinit_code_start[];
extern u8 _slab_xcinit_code_end[];
extern u8 _slab_xcinit_rwdata_start[];
extern u8 _slab_xcinit_rwdata_end[];
extern u8 _slab_xcinit_rodata_start[];
extern u8 _slab_xcinit_rodata_end[];
extern u8 _slab_xcinit_stack_start[];
extern u8 _slab_xcinit_stack_end[];
extern u8 _slab_xcinit_dmadata_start[];
extern u8 _slab_xcinit_dmadata_end[];
extern u8 _slab_xcinit_entrypoint[];

extern u8 _slab_xcihub_code_start[];
extern u8 _slab_xcihub_code_end[];
extern u8 _slab_xcihub_rwdata_start[];
extern u8 _slab_xcihub_rwdata_end[];
extern u8 _slab_xcihub_rodata_start[];
extern u8 _slab_xcihub_rodata_end[];
extern u8 _slab_xcihub_stack_start[];
extern u8 _slab_xcihub_stack_end[];
extern u8 _slab_xcihub_dmadata_start[];
extern u8 _slab_xcihub_dmadata_end[];
extern u8 _slab_xcihub_entrypoint[];

extern u8 _slab_xcexhub_code_start[];
extern u8 _slab_xcexhub_code_end[];
extern u8 _slab_xcexhub_rwdata_start[];
extern u8 _slab_xcexhub_rwdata_end[];
extern u8 _slab_xcexhub_rodata_start[];
extern u8 _slab_xcexhub_rodata_end[];
extern u8 _slab_xcexhub_stack_start[];
extern u8 _slab_xcexhub_stack_end[];
extern u8 _slab_xcexhub_dmadata_start[];
extern u8 _slab_xcexhub_dmadata_end[];
extern u8 _slab_xcexhub_entrypoint[];

extern u8 _slab_xctestslab1_code_start[];
extern u8 _slab_xctestslab1_code_end[];
extern u8 _slab_xctestslab1_rwdata_start[];
extern u8 _slab_xctestslab1_rwdata_end[];
extern u8 _slab_xctestslab1_rodata_start[];
extern u8 _slab_xctestslab1_rodata_end[];
extern u8 _slab_xctestslab1_stack_start[];
extern u8 _slab_xctestslab1_stack_end[];
extern u8 _slab_xctestslab1_dmadata_start[];
extern u8 _slab_xctestslab1_dmadata_end[];
extern u8 _slab_xctestslab1_entrypoint[];

extern u8 _slab_xhhyperdep_code_start[];
extern u8 _slab_xhhyperdep_code_end[];
extern u8 _slab_xhhyperdep_rwdata_start[];
extern u8 _slab_xhhyperdep_rwdata_end[];
extern u8 _slab_xhhyperdep_rodata_start[];
extern u8 _slab_xhhyperdep_rodata_end[];
extern u8 _slab_xhhyperdep_stack_start[];
extern u8 _slab_xhhyperdep_stack_end[];
extern u8 _slab_xhhyperdep_dmadata_start[];
extern u8 _slab_xhhyperdep_dmadata_end[];
extern u8 _slab_xhhyperdep_entrypoint[];

extern u8 _slab_xhapprovexec_code_start[];
extern u8 _slab_xhapprovexec_code_end[];
extern u8 _slab_xhapprovexec_rwdata_start[];
extern u8 _slab_xhapprovexec_rwdata_end[];
extern u8 _slab_xhapprovexec_rodata_start[];
extern u8 _slab_xhapprovexec_rodata_end[];
extern u8 _slab_xhapprovexec_stack_start[];
extern u8 _slab_xhapprovexec_stack_end[];
extern u8 _slab_xhapprovexec_dmadata_start[];
extern u8 _slab_xhapprovexec_dmadata_end[];
extern u8 _slab_xhapprovexec_entrypoint[];

extern u8 _slab_xhsyscalllog_code_start[];
extern u8 _slab_xhsyscalllog_code_end[];
extern u8 _slab_xhsyscalllog_rwdata_start[];
extern u8 _slab_xhsyscalllog_rwdata_end[];
extern u8 _slab_xhsyscalllog_rodata_start[];
extern u8 _slab_xhsyscalllog_rodata_end[];
extern u8 _slab_xhsyscalllog_stack_start[];
extern u8 _slab_xhsyscalllog_stack_end[];
extern u8 _slab_xhsyscalllog_dmadata_start[];
extern u8 _slab_xhsyscalllog_dmadata_end[];
extern u8 _slab_xhsyscalllog_entrypoint[];


extern u8 _slab_xhssteptrace_code_start[];
extern u8 _slab_xhssteptrace_code_end[];
extern u8 _slab_xhssteptrace_rwdata_start[];
extern u8 _slab_xhssteptrace_rwdata_end[];
extern u8 _slab_xhssteptrace_rodata_start[];
extern u8 _slab_xhssteptrace_rodata_end[];
extern u8 _slab_xhssteptrace_stack_start[];
extern u8 _slab_xhssteptrace_stack_end[];
extern u8 _slab_xhssteptrace_dmadata_start[];
extern u8 _slab_xhssteptrace_dmadata_end[];
extern u8 _slab_xhssteptrace_entrypoint[];

extern u8 _slab_xcguestslab_code_start[];
extern u8 _slab_xcguestslab_code_end[];
extern u8 _slab_xcguestslab_rwdata_start[];
extern u8 _slab_xcguestslab_rwdata_end[];
extern u8 _slab_xcguestslab_rodata_start[];
extern u8 _slab_xcguestslab_rodata_end[];
extern u8 _slab_xcguestslab_stack_start[];
extern u8 _slab_xcguestslab_stack_end[];
extern u8 _slab_xcguestslab_dmadata_start[];
extern u8 _slab_xcguestslab_dmadata_end[];
extern u8 _slab_xcguestslab_entrypoint[];



__attribute__(( section(".data") )) __attribute__((aligned(4096))) x_slab_info_t _xmhfhic_common_slab_info_table[] = {

    //XMHF_HYP_SLAB_GEECPRIME
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_xmhfhic_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_xmhfhic_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_xmhfhic_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_xmhfhic_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_xmhfhic_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_xmhfhic_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_xmhfhic_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_xmhfhic_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,        HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XCINIT),
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        {
            {.addr_start = _xmhfhic_sharedro_start, .addr_end = _xmhfhic_sharedro_end, .protection = 0},
            {.addr_start = _xmhfhic_code_start, .addr_end = _xmhfhic_code_end, .protection = 0},
            {.addr_start = _xmhfhic_rwdata_start, .addr_end = _xmhfhic_rwdata_end, .protection = 0},
            {.addr_start = _xmhfhic_rodata_start, .addr_end = _xmhfhic_rodata_end, .protection = 0},
            {.addr_start = _xmhfhic_stack_start, .addr_end = _xmhfhic_stack_end, .protection = 0},
        },
        (u32)_xmhfhic_code_start
    },


    //XMHF_HYP_SLAB_GEECSENTINEL
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_slab_geecsentinel_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_geecsentinel_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_geecsentinel_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_geecsentinel_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_geecsentinel_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_geecsentinel_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_geecsentinel_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_geecsentinel_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XCTESTSLAB1) | HIC_SLAB_CALLCAP(XMHF_GUEST_SLAB_XCGUESTSLAB),
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        {
            {.addr_start = _slab_geecsentinel_code_start, .addr_end = _slab_geecsentinel_code_end, .protection = 0},
            {.addr_start = _slab_geecsentinel_rwdata_start, .addr_end = _slab_geecsentinel_rwdata_end, .protection = 0},
            {.addr_start = _slab_geecsentinel_rodata_start, .addr_end = _slab_geecsentinel_rodata_end, .protection = 0},
            {.addr_start = _slab_geecsentinel_stack_start, .addr_end = _slab_geecsentinel_stack_end, .protection = 0},
            {.addr_start = _slab_geecsentinel_dmadata_start, .addr_end = _slab_geecsentinel_dmadata_end, .protection = 0},
        },
        (u32)_slab_geecsentinel_entrypoint
    },


    //XMHF_HYP_SLAB_GEEC_PRIMESMP
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_slab_geec_primesmp_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_geec_primesmp_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_geec_primesmp_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_geec_primesmp_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_geec_primesmp_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_geec_primesmp_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_geec_primesmp_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_geec_primesmp_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XCTESTSLAB1) | HIC_SLAB_CALLCAP(XMHF_GUEST_SLAB_XCGUESTSLAB),
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        {
            {.addr_start = _slab_geec_primesmp_code_start, .addr_end = _slab_geec_primesmp_code_end, .protection = 0},
            {.addr_start = _slab_geec_primesmp_rwdata_start, .addr_end = _slab_geec_primesmp_rwdata_end, .protection = 0},
            {.addr_start = _slab_geec_primesmp_rodata_start, .addr_end = _slab_geec_primesmp_rodata_end, .protection = 0},
            {.addr_start = _slab_geec_primesmp_stack_start, .addr_end = _slab_geec_primesmp_stack_end, .protection = 0},
            {.addr_start = _slab_geec_primesmp_dmadata_start, .addr_end = _slab_geec_primesmp_dmadata_end, .protection = 0},
        },
        (u32)_slab_geec_primesmp_entrypoint
    },



    //XMHF_HYP_SLAB_UAPI_GCPUSTATE
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_slab_uapi_gcpustate_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_gcpustate_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_gcpustate_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_gcpustate_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_gcpustate_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_gcpustate_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_gcpustate_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_gcpustate_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XCTESTSLAB1) | HIC_SLAB_CALLCAP(XMHF_GUEST_SLAB_XCGUESTSLAB),
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        {
            {.addr_start = _slab_uapi_gcpustate_code_start, .addr_end = _slab_uapi_gcpustate_code_end, .protection = 0},
            {.addr_start = _slab_uapi_gcpustate_rwdata_start, .addr_end = _slab_uapi_gcpustate_rwdata_end, .protection = 0},
            {.addr_start = _slab_uapi_gcpustate_rodata_start, .addr_end = _slab_uapi_gcpustate_rodata_end, .protection = 0},
            {.addr_start = _slab_uapi_gcpustate_stack_start, .addr_end = _slab_uapi_gcpustate_stack_end, .protection = 0},
            {.addr_start = _slab_uapi_gcpustate_dmadata_start, .addr_end = _slab_uapi_gcpustate_dmadata_end, .protection = 0},
        },
        (u32)_slab_uapi_gcpustate_entrypoint
    },


    //XMHF_HYP_SLAB_UAPI_HCPUSTATE
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_slab_uapi_hcpustate_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_hcpustate_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_hcpustate_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_hcpustate_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_hcpustate_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_hcpustate_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_hcpustate_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_hcpustate_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XCTESTSLAB1) | HIC_SLAB_CALLCAP(XMHF_GUEST_SLAB_XCGUESTSLAB),
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        {
            {.addr_start = _slab_uapi_hcpustate_code_start, .addr_end = _slab_uapi_hcpustate_code_end, .protection = 0},
            {.addr_start = _slab_uapi_hcpustate_rwdata_start, .addr_end = _slab_uapi_hcpustate_rwdata_end, .protection = 0},
            {.addr_start = _slab_uapi_hcpustate_rodata_start, .addr_end = _slab_uapi_hcpustate_rodata_end, .protection = 0},
            {.addr_start = _slab_uapi_hcpustate_stack_start, .addr_end = _slab_uapi_hcpustate_stack_end, .protection = 0},
            {.addr_start = _slab_uapi_hcpustate_dmadata_start, .addr_end = _slab_uapi_hcpustate_dmadata_end, .protection = 0},
        },
        (u32)_slab_uapi_hcpustate_entrypoint
    },


    //XMHF_HYP_SLAB_UAPI_SLABMEMACC
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_slab_uapi_slabmemacc_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_slabmemacc_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_slabmemacc_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_slabmemacc_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_slabmemacc_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_slabmemacc_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_slabmemacc_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_slabmemacc_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XCTESTSLAB1) | HIC_SLAB_CALLCAP(XMHF_GUEST_SLAB_XCGUESTSLAB),
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        {
            {.addr_start = _slab_uapi_slabmemacc_code_start, .addr_end = _slab_uapi_slabmemacc_code_end, .protection = 0},
            {.addr_start = _slab_uapi_slabmemacc_rwdata_start, .addr_end = _slab_uapi_slabmemacc_rwdata_end, .protection = 0},
            {.addr_start = _slab_uapi_slabmemacc_rodata_start, .addr_end = _slab_uapi_slabmemacc_rodata_end, .protection = 0},
            {.addr_start = _slab_uapi_slabmemacc_stack_start, .addr_end = _slab_uapi_slabmemacc_stack_end, .protection = 0},
            {.addr_start = _slab_uapi_slabmemacc_dmadata_start, .addr_end = _slab_uapi_slabmemacc_dmadata_end, .protection = 0},
        },
        (u32)_slab_uapi_slabmemacc_entrypoint
    },

    //XMHF_HYP_SLAB_UAPI_SLABMEMPGTBL
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_slab_uapi_slabmempgtbl_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_slabmempgtbl_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_slabmempgtbl_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_slabmempgtbl_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_slabmempgtbl_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_slabmempgtbl_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_slabmempgtbl_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_uapi_slabmempgtbl_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XCTESTSLAB1) | HIC_SLAB_CALLCAP(XMHF_GUEST_SLAB_XCGUESTSLAB),
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        {
            {.addr_start = _slab_uapi_slabmempgtbl_code_start, .addr_end = _slab_uapi_slabmempgtbl_code_end, .protection = 0},
            {.addr_start = _slab_uapi_slabmempgtbl_rwdata_start, .addr_end = _slab_uapi_slabmempgtbl_rwdata_end, .protection = 0},
            {.addr_start = _slab_uapi_slabmempgtbl_rodata_start, .addr_end = _slab_uapi_slabmempgtbl_rodata_end, .protection = 0},
            {.addr_start = _slab_uapi_slabmempgtbl_stack_start, .addr_end = _slab_uapi_slabmempgtbl_stack_end, .protection = 0},
            {.addr_start = _slab_uapi_slabmempgtbl_dmadata_start, .addr_end = _slab_uapi_slabmempgtbl_dmadata_end, .protection = 0},
        },
        (u32)_slab_uapi_slabmempgtbl_entrypoint
    },

    //XMHF_HYP_SLAB_XCINIT
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_slab_xcinit_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcinit_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcinit_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcinit_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcinit_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcinit_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcinit_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcinit_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XCTESTSLAB1) | HIC_SLAB_CALLCAP(XMHF_GUEST_SLAB_XCGUESTSLAB),
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        {
            {.addr_start = _slab_xcinit_code_start, .addr_end = _slab_xcinit_code_end, .protection = 0},
            {.addr_start = _slab_xcinit_rwdata_start, .addr_end = _slab_xcinit_rwdata_end, .protection = 0},
            {.addr_start = _slab_xcinit_rodata_start, .addr_end = _slab_xcinit_rodata_end, .protection = 0},
            {.addr_start = _slab_xcinit_stack_start, .addr_end = _slab_xcinit_stack_end, .protection = 0},
            {.addr_start = _slab_xcinit_dmadata_start, .addr_end = _slab_xcinit_dmadata_end, .protection = 0},
        },
        (u32)_slab_xcinit_entrypoint
    },


    //XMHF_HYP_SLAB_XCIHUB
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_slab_xcihub_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcihub_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcihub_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcihub_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcihub_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcihub_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcihub_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcihub_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XHHYPERDEP) | HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XHAPPROVEXEC) | HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XHSSTEPTRACE) | HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XHSYSCALLLOG),
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        {
            {.addr_start = _slab_xcihub_code_start, .addr_end = _slab_xcihub_code_end, .protection = 0},
            {.addr_start = _slab_xcihub_rwdata_start, .addr_end = _slab_xcihub_rwdata_end, .protection = 0},
            {.addr_start = _slab_xcihub_rodata_start, .addr_end = _slab_xcihub_rodata_end, .protection = 0},
            {.addr_start = _slab_xcihub_stack_start, .addr_end = _slab_xcihub_stack_end, .protection = 0},
            {.addr_start = _slab_xcihub_dmadata_start, .addr_end = _slab_xcihub_dmadata_end, .protection = 0},
        },
        (u32)_slab_xcihub_entrypoint
    },


    //XMHF_HYP_SLAB_XCEXHUB
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_slab_xcexhub_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcexhub_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcexhub_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcexhub_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcexhub_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcexhub_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcexhub_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcexhub_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        0,
        0,
        {false, 0, {0}},
        {
            {.addr_start = _slab_xcexhub_code_start, .addr_end = _slab_xcexhub_code_end, .protection = 0},
            {.addr_start = _slab_xcexhub_rwdata_start, .addr_end = _slab_xcexhub_rwdata_end, .protection = 0},
            {.addr_start = _slab_xcexhub_rodata_start, .addr_end = _slab_xcexhub_rodata_end, .protection = 0},
            {.addr_start = _slab_xcexhub_stack_start, .addr_end = _slab_xcexhub_stack_end, .protection = 0},
            {.addr_start = _slab_xcexhub_dmadata_start, .addr_end = _slab_xcexhub_dmadata_end, .protection = 0},
        },
        (u32)_slab_xcexhub_entrypoint
    },


    //XMHF_HYP_SLAB_XCTESTSLAB1
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_slab_xctestslab1_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xctestslab1_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xctestslab1_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xctestslab1_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xctestslab1_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xctestslab1_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xctestslab1_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xctestslab1_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        0,
        0,
        {false, 0, {0}},
        {
            {.addr_start = _slab_xctestslab1_code_start, .addr_end = _slab_xctestslab1_code_end, .protection = 0},
            {.addr_start = _slab_xctestslab1_rwdata_start, .addr_end = _slab_xctestslab1_rwdata_end, .protection = 0},
            {.addr_start = _slab_xctestslab1_rodata_start, .addr_end = _slab_xctestslab1_rodata_end, .protection = 0},
            {.addr_start = _slab_xctestslab1_stack_start, .addr_end = _slab_xctestslab1_stack_end, .protection = 0},
            {.addr_start = _slab_xctestslab1_dmadata_start, .addr_end = _slab_xctestslab1_dmadata_end, .protection = 0},
        },
        (u32)_slab_xctestslab1_entrypoint
    },


    //XMHF_HYP_SLAB_XHHYPERDEP
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_slab_xhhyperdep_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhhyperdep_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhhyperdep_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhhyperdep_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhhyperdep_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhhyperdep_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhhyperdep_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhhyperdep_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        0,
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        {
            {.addr_start = _slab_xhhyperdep_code_start, .addr_end = _slab_xhhyperdep_code_end, .protection = 0},
            {.addr_start = _slab_xhhyperdep_rwdata_start, .addr_end = _slab_xhhyperdep_rwdata_end, .protection = 0},
            {.addr_start = _slab_xhhyperdep_rodata_start, .addr_end = _slab_xhhyperdep_rodata_end, .protection = 0},
            {.addr_start = _slab_xhhyperdep_stack_start, .addr_end = _slab_xhhyperdep_stack_end, .protection = 0},
            {.addr_start = _slab_xhhyperdep_dmadata_start, .addr_end = _slab_xhhyperdep_dmadata_end, .protection = 0},
        },
        (u32)_slab_xhhyperdep_entrypoint
    },


    //XMHF_HYP_SLAB_XHAPPROVEXEC
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_slab_xhapprovexec_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhapprovexec_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhapprovexec_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhapprovexec_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhapprovexec_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhapprovexec_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhapprovexec_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhapprovexec_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        0,
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        {
            {.addr_start = _slab_xhapprovexec_code_start, .addr_end = _slab_xhapprovexec_code_end, .protection = 0},
            {.addr_start = _slab_xhapprovexec_rwdata_start, .addr_end = _slab_xhapprovexec_rwdata_end, .protection = 0},
            {.addr_start = _slab_xhapprovexec_rodata_start, .addr_end = _slab_xhapprovexec_rodata_end, .protection = 0},
            {.addr_start = _slab_xhapprovexec_stack_start, .addr_end = _slab_xhapprovexec_stack_end, .protection = 0},
            {.addr_start = _slab_xhapprovexec_dmadata_start, .addr_end = _slab_xhapprovexec_dmadata_end, .protection = 0},
        },
        (u32)_slab_xhapprovexec_entrypoint
    },

    //XMHF_HYP_SLAB_XHSYSCALLLOG
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_slab_xhsyscalllog_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhsyscalllog_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhsyscalllog_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhsyscalllog_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhsyscalllog_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhsyscalllog_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhsyscalllog_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhsyscalllog_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        0,
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        {
            {.addr_start = _slab_xhsyscalllog_code_start, .addr_end = _slab_xhsyscalllog_code_end, .protection = 0},
            {.addr_start = _slab_xhsyscalllog_rwdata_start, .addr_end = _slab_xhsyscalllog_rwdata_end, .protection = 0},
            {.addr_start = _slab_xhsyscalllog_rodata_start, .addr_end = _slab_xhsyscalllog_rodata_end, .protection = 0},
            {.addr_start = _slab_xhsyscalllog_stack_start, .addr_end = _slab_xhsyscalllog_stack_end, .protection = 0},
            {.addr_start = _slab_xhsyscalllog_dmadata_start, .addr_end = _slab_xhsyscalllog_dmadata_end, .protection = 0},
        },
        (u32)_slab_xhsyscalllog_entrypoint
    },

    //XMHF_HYP_SLAB_XHSSTEPTRACE
    {
        {
            HIC_SLAB_X86VMXX86PC_HYPERVISOR,
            false,
            false,
            0,
            {
                ((u32)&_slab_xhssteptrace_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhssteptrace_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhssteptrace_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhssteptrace_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhssteptrace_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhssteptrace_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhssteptrace_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xhssteptrace_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        0,
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        {
            {.addr_start = _slab_xhssteptrace_code_start, .addr_end = _slab_xhssteptrace_code_end, .protection = 0},
            {.addr_start = _slab_xhssteptrace_rwdata_start, .addr_end = _slab_xhssteptrace_rwdata_end, .protection = 0},
            {.addr_start = _slab_xhssteptrace_rodata_start, .addr_end = _slab_xhssteptrace_rodata_end, .protection = 0},
            {.addr_start = _slab_xhssteptrace_stack_start, .addr_end = _slab_xhssteptrace_stack_end, .protection = 0},
            {.addr_start = _slab_xhssteptrace_dmadata_start, .addr_end = _slab_xhssteptrace_dmadata_end, .protection = 0},
        },
        (u32)_slab_xhssteptrace_entrypoint
    },

    //XMHF_GUEST_SLAB_XCGUESTSLAB
    {
        {
            HIC_SLAB_X86VMXX86PC_GUEST,
            false,
            false,
            0,
            {
                ((u32)&_slab_xcguestslab_stack_start[1*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcguestslab_stack_start[2*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcguestslab_stack_start[3*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcguestslab_stack_start[4*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcguestslab_stack_start[5*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcguestslab_stack_start[6*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcguestslab_stack_start[7*XMHF_SLAB_STACKSIZE]),
                ((u32)&_slab_xcguestslab_stack_start[8*XMHF_SLAB_STACKSIZE]),
            }
        },
        true,
        0,
        0,
        0,
        {true, 0xFFFFFFFFUL, {0}},
        {
            {.addr_start = _slab_xcguestslab_code_start, .addr_end = _slab_xcguestslab_code_end, .protection = 0},
            {.addr_start = _slab_xcguestslab_rwdata_start, .addr_end = _slab_xcguestslab_rwdata_end, .protection = 0},
            {.addr_start = _slab_xcguestslab_rodata_start, .addr_end = _slab_xcguestslab_rodata_end, .protection = 0},
            {.addr_start = _slab_xcguestslab_stack_start, .addr_end = _slab_xcguestslab_stack_end, .protection = 0},
            {.addr_start = _slab_xcguestslab_dmadata_start, .addr_end = _slab_xcguestslab_dmadata_end, .protection = 0},
        },
        (u32)_slab_xcguestslab_entrypoint
    },

};



