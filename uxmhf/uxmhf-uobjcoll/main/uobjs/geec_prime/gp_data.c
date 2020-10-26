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


#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec_prime.h>

/*
 * data used by HIC
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


__attribute__(( section(".rwdatahdr") )) __attribute__(( aligned(4096) )) gp_rwdatahdr_t gp_rwdatahdr = {
		.xcbootinfo_store.magic = RUNTIME_PARAMETER_BLOCK_MAGIC,
};

//static XMHF_BOOTINFO xcbootinfo_store __attribute__(( section(".rwdatahdr") )) = {
//	.magic= RUNTIME_PARAMETER_BLOCK_MAGIC,
//};

// XMHF boot information block
__attribute__(( section(".data") )) XMHF_BOOTINFO *xcbootinfo= &gp_rwdatahdr.xcbootinfo_store;

__attribute__((section(".slab_codehdr"))) x86vmx_mle_header_t mleheader = { 0 };


// initialization BSP stack
__attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) uint8_t _init_bsp_cpustack[MAX_PLATFORM_CPUSTACK_SIZE];



//////
// (SMP) CPU state setup data
//////
/*
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

uint32_t  __xmhfhic_exceptionstubs[] = { XMHF_EXCEPTION_HANDLER_ADDROF(0),
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
*/
// CASM module supporting data structures



// following two data structures used for SMP bootup
__attribute__(( aligned(16) )) uint64_t _xcsmp_ap_init_gdt_start[]  = {
	0x0000000000000000ULL,	//NULL descriptor
	0x00af9b000000ffffULL,	//CPL-0 64-bit code descriptor (CS64)
	0x00af93000000ffffULL,	//CPL-0 64-bit data descriptor (DS/SS/ES/FS/GS)
};

__attribute__(( aligned(16) )) arch_x86_gdtdesc_t _xcsmp_ap_init_gdt  = {
	.size=sizeof(_xcsmp_ap_init_gdt_start)-1,
	.base=(uint32_t)&_xcsmp_ap_init_gdt_start,
};



//static bool CASM_FUNCCALL(__xmhfhic_ap_entry,void) __attribute__((naked));
void __xmhfhic_smp_cpu_x86_smpinitialize_commonstart(void);


// GDT
__attribute__((section(".data"))) __attribute__(( aligned(16) )) uint64_t __xmhfhic_x86vmx_gdt_start[XMHFGEEC_MAX_GDT_CODEDATA_DESCRIPTORS + MAX_PLATFORM_CPUS]  = {
	0x0000000000000000ULL,	//NULL descriptor
	0x00cf9a000000ffffULL,	//CPL-0 32-bit code descriptor (CS64)
	0x00cf92000000ffffULL,	//CPL-0 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x00cffa000000ffffULL,	//TODO: CPL-3 32-bit code descriptor (CS64)
	0x00cff2000000ffffULL,	//TODO: CPL-3 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x00cffa000000ffffULL,	//TODO: CPL-3 32-bit code descriptor (CS64)
	0x00cff2000000ffffULL,	//TODO: CPL-3 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x0000000000000000ULL,  //TSS descriptors (64-bits each)
};
// GDT descriptor
__attribute__((section(".data"))) __attribute__(( aligned(16) )) arch_x86_gdtdesc_t __xmhfhic_x86vmx_gdt  = {
	.size=sizeof(__xmhfhic_x86vmx_gdt_start)-1,
	.base=(uint32_t)&__xmhfhic_x86vmx_gdt_start,
};


//////
// per-CPU data structures
//////


// initialization phase CPU stacks
__attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) uint8_t _init_cpustacks[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];
// TSS
//__attribute__((section(".data"))) __attribute__(( aligned(4096) )) uint8_t __xmhfhic_x86vmx_tss[MAX_PLATFORM_CPUS][4*PAGE_SIZE_4K] = { 0 };
__attribute__((section(".data"))) __attribute__(( aligned(4096) )) geec_prime_tss_t __xmhfhic_x86vmx_tss[MAX_PLATFORM_CPUS] = { 0 };
// TSS stacks
__attribute__((section(".stack"))) __attribute__(( aligned(4096) )) uint8_t __xmhfhic_x86vmx_tss_stack[MAX_PLATFORM_CPUS][PAGE_SIZE_4K];

//// sysenter CPU stacks
//__attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) uint8_t _geec_primesmp_sysenter_stack[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];

// archdata
__attribute__((section(".data"))) __attribute__(( aligned(4096) )) xc_cpuarchdata_x86vmx_t __xmhfhic_x86vmx_archdata[MAX_PLATFORM_CPUS];
//cpuidtable
//__attribute__((section(".data"))) __attribute__(( aligned(4) )) uint32_t __xmhfhic_x86vmx_cpuidtable[MAX_X86_APIC_ID];


//////
// verified hypervisor slab memory page-tables
__attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t gp_vhslabmempgtbl_lvl3t[PAE_MAXPTRS_PER_PDPT];
//__attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t gp_vhslabmempgtbl_lvl2t[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
__attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t gp_vhslabmempgtbl_lvl2t[PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT];
//__attribute__((section(".data"))) __attribute__((aligned(4096)))  uint64_t gp_vhslabmempgtbl_lvl1t[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT][PAE_PTRS_PER_PT];
__attribute__((section(".data"))) __attribute__((aligned(4096)))  uint64_t gp_vhslabmempgtbl_lvl1t[PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT];

#if 1
//////
// unverified hypervisor slab memory page-tables

__attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t gp_uhslabmempgtbl_lvl3t[XMHFGEEC_TOTAL_UHSLABS][PAE_MAXPTRS_PER_PDPT];
__attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t gp_uhslabmempgtbl_lvl2t[XMHFGEEC_TOTAL_UHSLABS][PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT];
__attribute__((section(".data"))) __attribute__((aligned(4096)))  uint64_t gp_uhslabmempgtbl_lvl1t[XMHFGEEC_TOTAL_UHSLABS][PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT];
#endif


//////
// bootstrap unity mapped page-tables
__attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t _xcprimeon_init_pdt[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
__attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t _xcprimeon_init_pdpt[PAE_MAXPTRS_PER_PDPT];


__attribute__((section(".data"))) slab_devicemap_t _sda_slab_devicemap[XMHFGEEC_TOTAL_SLABS];

__attribute__((section(".data"))) sysdev_memioregions_t sysdev_memioregions[MAX_PLATFORM_DEVICES];
__attribute__((section(".data"))) uint32_t numentries_sysdev_memioregions=0;


__attribute__((section(".data"))) struct _memorytype _vmx_ept_memorytypes[MAX_MEMORYTYPE_ENTRIES]; //EPT memory types array

__attribute__((section(".data"))) mtrr_state_t _mtrrs;
__attribute__((section(".data"))) mtrr_state_t sinit2mle_mtrrs;

__attribute__((section(".data"))) uint32_t gp_state4_smplock = 1;


//DMA Remapping Hardware Unit Definitions
__attribute__((section(".data"))) VTD_DRHD vtd_drhd[VTD_MAX_DRHD];
__attribute__((section(".data"))) uint32_t vtd_num_drhd=0;	//total number of DMAR h/w units
__attribute__((section(".data"))) bool vtd_drhd_scanned=false;	//set to true once DRHD units have been scanned in the system

__attribute__((section(".data"))) vtd_drhd_handle_t vtd_drhd_maxhandle=0;
__attribute__((section(".data"))) uint32_t vtd_dmar_table_physical_address=0;
__attribute__((section(".data"))) uint32_t vtd_ret_address=0;


//DMA page tables
__attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_ret_entry_t _slabdevpgtbl_vtd_ret[VTD_RET_MAXPTRS];
__attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_cet_entry_t _slabdevpgtbl_vtd_cet[VTD_RET_MAXPTRS][VTD_CET_MAXPTRS];

__attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pml4te_t _slabdevpgtbl_pml4t[XMHFGEEC_TOTAL_SLABS][PAE_MAXPTRS_PER_PML4T];
__attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pdpte_t _slabdevpgtbl_pdpt[XMHFGEEC_TOTAL_SLABS][PAE_MAXPTRS_PER_PDPT];
__attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pdte_t _slabdevpgtbl_pdt[XMHFGEEC_TOTAL_SLABS][PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT];
__attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pte_t _slabdevpgtbl_pt[XMHFGEEC_TOTAL_SLABS][MAX_SLAB_DMADATA_PDT_ENTRIES][PAE_PTRS_PER_PT];

//rich-guest DMA page-tables
__attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pte_t _slabdevpgtbl_pt_rg[VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT * VTD_PTRS_PER_PT];



__attribute__((section(".data"))) _slabdevpgtbl_infotable_t _slabdevpgtbl_infotable[XMHFGEEC_TOTAL_SLABS];
__attribute__((section(".data"))) uint32_t vtd_pagewalk_level;


//SMP
__attribute__((section(".data"))) x86smp_apbootstrapdata_t apdata;
