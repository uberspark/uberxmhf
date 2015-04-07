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






// initialization BSP stack
__attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) u8 _init_bsp_cpustack[MAX_PLATFORM_CPUSTACK_SIZE];















//////
// backing data buffers for slab memory and device page tables
#if !defined (__XMHF_VERIFICATION__)

__attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_slpgtbl_t _dbuf_devpgtbl[XMHF_HIC_MAX_SLABS];
__attribute__((section(".data"))) __attribute__(( aligned(2097152) )) u64 _dbuf_mempgtbl_pml4t[XMHF_HIC_MAX_SLABS][PAE_MAXPTRS_PER_PML4T];
__attribute__((section(".data"))) __attribute__((aligned(4096)))	u64 _dbuf_mempgtbl_pdpt[XMHF_HIC_MAX_SLABS][PAE_MAXPTRS_PER_PDPT];
__attribute__((section(".data"))) __attribute__((aligned(4096)))	u64 _dbuf_mempgtbl_pdt[XMHF_HIC_MAX_SLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
__attribute__((section(".data"))) __attribute__((aligned(4096)))  u64 _dbuf_mempgtbl_pt[XMHF_HIC_MAX_SLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT][PAE_PTRS_PER_PT];

#endif //__XMHF_VERIFICATION__







//////
// runtime exception CPU stacks

//__attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) u8 _rtmxcp_cpustacks[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];

//////
// runtime exception bootstrap save area
//__attribute__((section(".data"))) __attribute__(( aligned(4096) )) u64 _rtmxcp_bssavearea[512] = { 1ULL };


//__attribute__(( aligned(8) )) u64 __xmhfhic_x86vmx_cpuidtable[MAX_X86_APIC_ID];
__attribute__((section(".data"))) __attribute__(( aligned(4) )) u32 __xmhfhic_x86vmx_cpuidtable[MAX_X86_APIC_ID];

__attribute__((section(".data"))) __attribute__(( aligned(4096) )) xc_cpuarchdata_x86vmx_t __xmhfhic_x86vmx_archdata[MAX_PLATFORM_CPUS];
















