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
 * data used by HIC
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

//////
// setup stage

static XMHF_BOOTINFO xcbootinfo_store __attribute__(( section(".sharedro_xcbootinfo") )) = {
	.magic= RUNTIME_PARAMETER_BLOCK_MAGIC,
};

// XMHF boot information block
__attribute__(( section(".sharedro_xcbootinfoptr") )) XMHF_BOOTINFO *xcbootinfo= &xcbootinfo_store;

/*
// slab capabilities (privilegemask, call capabilities, type ...)
__attribute__((section(".data"))) slab_caps_t _xmhfhic_init_setupdata_slab_caps[XMHF_HIC_MAX_SLABS] = {

    //XMHF_HYP_SLAB_GEECPRIME
    {
        0,
        HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XCINIT),
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        HIC_SLAB_X86VMXX86PC_HYPERVISOR
    },

    //XMHF_HYP_SLAB_XCINIT
    {
        0,
        HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XCTESTSLAB1) | HIC_SLAB_CALLCAP(XMHF_GUEST_SLAB_XCGUESTSLAB),
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        HIC_SLAB_X86VMXX86PC_HYPERVISOR
    },
#if !defined (__XMHF_VERIFICATION__)

    //XMHF_HYP_SLAB_XCIHUB
    {
        0,
        HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XHHYPERDEP) | HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XHAPPROVEXEC) | HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XHSSTEPTRACE) | HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XHSYSCALLLOG),
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        HIC_SLAB_X86VMXX86PC_HYPERVISOR
    },

    //XMHF_HYP_SLAB_XCEXHUB
    {
        0,
        0,
        0,
        {false, 0, {0}},
        HIC_SLAB_X86VMXX86PC_HYPERVISOR
    },

    //XMHF_HYP_SLAB_XCTESTSLAB1
    {
        0,
        0,
        0,
        {false, 0, {0}},
        HIC_SLAB_X86VMXX86PC_HYPERVISOR
    },

    //XMHF_HYP_SLAB_XHHYPERDEP
    {
        0,
        0,
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        HIC_SLAB_X86VMXX86PC_HYPERVISOR
    },

    //XMHF_HYP_SLAB_XHAPPROVEXEC
    {
        0,
        0,
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        HIC_SLAB_X86VMXX86PC_HYPERVISOR
    },

    //XMHF_HYP_SLAB_XHSYSCALLLOG
    {
        0,
        0,
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        HIC_SLAB_X86VMXX86PC_HYPERVISOR
    },

    //XMHF_HYP_SLAB_XHSSTEPTRACE
    {
        0,
        0,
        HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_CPUSTATE) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_PHYSMEM) | HIC_SLAB_UAPICAP(XMHF_HIC_UAPI_MEMPGTBL),
        {false, 0, {0}},
        HIC_SLAB_X86VMXX86PC_HYPERVISOR
    },

    //XMHF_GUEST_SLAB_XCGUESTSLAB
    {
        0,
        0,
        0,
        {true, 0xFFFFFFFFUL, {0}},
        HIC_SLAB_X86VMXX86PC_GUEST
    },
#endif
};
*/

//#if !defined (__XMHF_VERIFICATION__)

//the following is autogenerated based on the linker script
//#include "__xmhfhic_initdata_slabtable"


//#else

//slab_physmem_extent_t _xmhfhic_init_setupdata_slab_physmem_extents[XMHF_HIC_MAX_SLABS][HIC_SLAB_PHYSMEM_MAXEXTENTS];
//
//#endif //__XMHF_VERIFICATION__













//////
// runtime stage
__attribute__((section(".hic_mleheader"))) x86vmx_mle_header_t mleheader = { 0 };

__attribute__((section(".data"))) u64 __xmhfhic_safestack_indices[MAX_PLATFORM_CPUS] = { 0 };

__attribute__((section(".data"))) __xmhfhic_safestack_element_t __xmhfhic_safestack[MAX_PLATFORM_CPUS][512];


















//////
// common



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



__attribute__(( section(".sharedro") )) __attribute__((aligned(4096))) x_slab_info_t _xmhfhic_common_slab_info_table[] = {

    //XMHF_HYP_SLAB_GEECPRIME
    {
        {HIC_SLAB_X86VMXX86PC_HYPERVISOR, false, false, 0, {0}},
        true,
        0,
        HIC_SLAB_CALLCAP(XMHF_HYP_SLAB_XCINIT),
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


    //XMHF_HYP_SLAB_XCINIT
    {
        {HIC_SLAB_X86VMXX86PC_HYPERVISOR, false, false, 0, {0}},
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
        {HIC_SLAB_X86VMXX86PC_HYPERVISOR, false, false, 0, {0}},
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
        {HIC_SLAB_X86VMXX86PC_HYPERVISOR, false, false, 0, {0}},
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
        {HIC_SLAB_X86VMXX86PC_HYPERVISOR, false, false, 0, {0}},
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
        {HIC_SLAB_X86VMXX86PC_HYPERVISOR, false, false, 0, {0}},
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
        {HIC_SLAB_X86VMXX86PC_HYPERVISOR, false, false, 0, {0}},
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
        {HIC_SLAB_X86VMXX86PC_HYPERVISOR, false, false, 0, {0}},
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
        {HIC_SLAB_X86VMXX86PC_HYPERVISOR, false, false, 0, {0}},
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



//////
// backing data buffers for slab memory and device page tables
#if !defined (__XMHF_VERIFICATION__)

__attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_slpgtbl_t _dbuf_devpgtbl[XMHF_HIC_MAX_SLABS];
__attribute__((section(".data"))) __attribute__(( aligned(2097152) )) u64 _dbuf_mempgtbl_pml4t[XMHF_HIC_MAX_SLABS][PAE_MAXPTRS_PER_PML4T];
__attribute__((section(".data"))) __attribute__((aligned(4096)))	u64 _dbuf_mempgtbl_pdpt[XMHF_HIC_MAX_SLABS][PAE_MAXPTRS_PER_PDPT];
__attribute__((section(".data"))) __attribute__((aligned(4096)))	u64 _dbuf_mempgtbl_pdt[XMHF_HIC_MAX_SLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
__attribute__((section(".data"))) __attribute__((aligned(4096)))  u64 _dbuf_mempgtbl_pt[XMHF_HIC_MAX_SLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT][PAE_PTRS_PER_PT];

#endif //__XMHF_VERIFICATION__


// GDT
__attribute__((section(".data"))) __attribute__(( aligned(16) )) u64 __xmhfhic_x86vmx_gdt_start[]  = {
	0x0000000000000000ULL,	//NULL descriptor
	0x00cf9a000000ffffULL,	//CPL-0 32-bit code descriptor (CS64)
	0x00cf92000000ffffULL,	//CPL-0 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x00cffa000000ffffULL,	//TODO: CPL-3 32-bit code descriptor (CS64)
	0x00cff2000000ffffULL,	//TODO: CPL-3 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x00cffa000000ffffULL,	//TODO: CPL-3 32-bit code descriptor (CS64)
	0x00cff2000000ffffULL,	//TODO: CPL-3 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x0000000000000000ULL,  //TSS descriptors (64-bits each)
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,

	0x0000000000000000ULL,
};

/* x86_64
// GDT descriptor
__attribute__(( aligned(16) )) arch_x86_gdtdesc_t __xmhfhic_x86vmx_gdt  = {
	.size=sizeof(__xmhfhic_x86vmx_gdt_start)-1,
	.base=(u64)&__xmhfhic_x86vmx_gdt_start,
};
*/

// GDT descriptor
__attribute__((section(".data"))) __attribute__(( aligned(16) )) arch_x86_gdtdesc_t __xmhfhic_x86vmx_gdt  = {
	.size=sizeof(__xmhfhic_x86vmx_gdt_start)-1,
	.base=(u32)&__xmhfhic_x86vmx_gdt_start,
};

// TSS
__attribute__((section(".data"))) __attribute__(( aligned(4096) )) u8 __xmhfhic_x86vmx_tss[MAX_PLATFORM_CPUS][PAGE_SIZE_4K] = { 0 };


// TSS stacks
__attribute__((section(".data"))) __attribute__(( aligned(4096) )) u8 __xmhfhic_x86vmx_tss_stack[MAX_PLATFORM_CPUS][PAGE_SIZE_4K];



// IDT
__attribute__((section(".data"))) __attribute__(( aligned(16) )) idtentry_t __xmhfhic_x86vmx_idt_start[EMHF_XCPHANDLER_MAXEXCEPTIONS] ;

/* x86_64
// IDT descriptor
__attribute__(( aligned(16) )) arch_x86_idtdesc_t __xmhfhic_x86vmx_idt = {
	.size=sizeof(__xmhfhic_x86vmx_idt_start)-1,
	.base=(u64)&__xmhfhic_x86vmx_idt_start,
};
*/

// IDT descriptor
__attribute__((section(".data"))) __attribute__(( aligned(16) )) arch_x86_idtdesc_t __xmhfhic_x86vmx_idt = {
	.size=sizeof(__xmhfhic_x86vmx_idt_start)-1,
	.base=(u32)&__xmhfhic_x86vmx_idt_start,
};



//////
// trampoline CPU stacks

__attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) u8 __xmhfhic_rtm_trampoline_stack[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];


//////
// runtime exception CPU stacks

__attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) u8 _rtmxcp_cpustacks[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];

//////
// runtime exception bootstrap save area
__attribute__((section(".data"))) __attribute__(( aligned(4096) )) u64 _rtmxcp_bssavearea[512] = { 1ULL };


//__attribute__(( aligned(8) )) u64 __xmhfhic_x86vmx_cpuidtable[MAX_X86_APIC_ID];
__attribute__((section(".data"))) __attribute__(( aligned(4) )) u32 __xmhfhic_x86vmx_cpuidtable[MAX_X86_APIC_ID];

__attribute__((section(".data"))) __attribute__(( aligned(4096) )) xc_cpuarchdata_x86vmx_t __xmhfhic_x86vmx_archdata[MAX_PLATFORM_CPUS];



//////
// CASM module supporting data structures

// initialization phase CPU stacks
__attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) u8 _init_cpustacks[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];


// following two data structures used for SMP bootup
__attribute__(( aligned(16) )) u64 _xcsmp_ap_init_gdt_start[]  = {
	0x0000000000000000ULL,	//NULL descriptor
	0x00af9b000000ffffULL,	//CPL-0 64-bit code descriptor (CS64)
	0x00af93000000ffffULL,	//CPL-0 64-bit data descriptor (DS/SS/ES/FS/GS)
};

__attribute__(( aligned(16) )) arch_x86_gdtdesc_t _xcsmp_ap_init_gdt  = {
	.size=sizeof(_xcsmp_ap_init_gdt_start)-1,
	.base=&_xcsmp_ap_init_gdt_start,
};


extern void __xmhf_exception_handler_0(void);
extern void __xmhf_exception_handler_1(void);
extern void __xmhf_exception_handler_2(void);
extern void __xmhf_exception_handler_3(void);
extern void __xmhf_exception_handler_4(void);
extern void __xmhf_exception_handler_5(void);
extern void __xmhf_exception_handler_6(void);
extern void __xmhf_exception_handler_7(void);
extern void __xmhf_exception_handler_8(void);
extern void __xmhf_exception_handler_9(void);
extern void __xmhf_exception_handler_10(void);
extern void __xmhf_exception_handler_11(void);
extern void __xmhf_exception_handler_12(void);
extern void __xmhf_exception_handler_13(void);
extern void __xmhf_exception_handler_14(void);
extern void __xmhf_exception_handler_15(void);
extern void __xmhf_exception_handler_16(void);
extern void __xmhf_exception_handler_17(void);
extern void __xmhf_exception_handler_18(void);
extern void __xmhf_exception_handler_19(void);
extern void __xmhf_exception_handler_20(void);
extern void __xmhf_exception_handler_21(void);
extern void __xmhf_exception_handler_22(void);
extern void __xmhf_exception_handler_23(void);
extern void __xmhf_exception_handler_24(void);
extern void __xmhf_exception_handler_25(void);
extern void __xmhf_exception_handler_26(void);
extern void __xmhf_exception_handler_27(void);
extern void __xmhf_exception_handler_28(void);
extern void __xmhf_exception_handler_29(void);
extern void __xmhf_exception_handler_30(void);
extern void __xmhf_exception_handler_31(void);

#define XMHF_EXCEPTION_HANDLER_ADDROF(vector) &__xmhf_exception_handler_##vector

u32  __xmhfhic_exceptionstubs[] = { XMHF_EXCEPTION_HANDLER_ADDROF(0),
							XMHF_EXCEPTION_HANDLER_ADDROF(1),
							XMHF_EXCEPTION_HANDLER_ADDROF(2),
							XMHF_EXCEPTION_HANDLER_ADDROF(3),
							XMHF_EXCEPTION_HANDLER_ADDROF(4),
							XMHF_EXCEPTION_HANDLER_ADDROF(5),
							XMHF_EXCEPTION_HANDLER_ADDROF(6),
							XMHF_EXCEPTION_HANDLER_ADDROF(7),
							XMHF_EXCEPTION_HANDLER_ADDROF(8),
							XMHF_EXCEPTION_HANDLER_ADDROF(9),
							XMHF_EXCEPTION_HANDLER_ADDROF(10),
							XMHF_EXCEPTION_HANDLER_ADDROF(11),
							XMHF_EXCEPTION_HANDLER_ADDROF(12),
							XMHF_EXCEPTION_HANDLER_ADDROF(13),
							XMHF_EXCEPTION_HANDLER_ADDROF(14),
							XMHF_EXCEPTION_HANDLER_ADDROF(15),
							XMHF_EXCEPTION_HANDLER_ADDROF(16),
							XMHF_EXCEPTION_HANDLER_ADDROF(17),
							XMHF_EXCEPTION_HANDLER_ADDROF(18),
							XMHF_EXCEPTION_HANDLER_ADDROF(19),
							XMHF_EXCEPTION_HANDLER_ADDROF(20),
							XMHF_EXCEPTION_HANDLER_ADDROF(21),
							XMHF_EXCEPTION_HANDLER_ADDROF(22),
							XMHF_EXCEPTION_HANDLER_ADDROF(23),
							XMHF_EXCEPTION_HANDLER_ADDROF(24),
							XMHF_EXCEPTION_HANDLER_ADDROF(25),
							XMHF_EXCEPTION_HANDLER_ADDROF(26),
							XMHF_EXCEPTION_HANDLER_ADDROF(27),
							XMHF_EXCEPTION_HANDLER_ADDROF(28),
							XMHF_EXCEPTION_HANDLER_ADDROF(29),
							XMHF_EXCEPTION_HANDLER_ADDROF(30),
							XMHF_EXCEPTION_HANDLER_ADDROF(31),
};











