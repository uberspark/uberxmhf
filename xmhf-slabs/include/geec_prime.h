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

// XMHF/GEEC prime header file
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __GEEC_PRIME_H_
#define __GEEC_PRIME_H_

//---platform
//VMX MSR indices
#define INDEX_IA32_VMX_BASIC_MSR            0x0
#define INDEX_IA32_VMX_PINBASED_CTLS_MSR    0x1
#define INDEX_IA32_VMX_PROCBASED_CTLS_MSR   0x2
#define INDEX_IA32_VMX_EXIT_CTLS_MSR        0x3
#define INDEX_IA32_VMX_ENTRY_CTLS_MSR       0x4
#define INDEX_IA32_VMX_MISC_MSR       	    0x5
#define INDEX_IA32_VMX_CR0_FIXED0_MSR       0x6
#define INDEX_IA32_VMX_CR0_FIXED1_MSR       0x7
#define INDEX_IA32_VMX_CR4_FIXED0_MSR       0x8
#define INDEX_IA32_VMX_CR4_FIXED1_MSR       0x9
#define INDEX_IA32_VMX_VMCS_ENUM_MSR        0xA
#define INDEX_IA32_VMX_PROCBASED_CTLS2_MSR  0xB




#ifndef __ASSEMBLY__

//MTRR memory type structure
struct _memorytype {
  u64 startaddr;
  u64 endaddr;
  u32 type;
  u32 invalid;
  u32 reserved[6];
} __attribute__((packed));


typedef struct {
    u8 pgtbl[3 * PAGE_SIZE_4K];
    u8 mlehdr[0x80];
} __attribute__((packed)) x86vmx_mle_header_t;

#define MAX_SLAB_MEMIOREGIONS_MEMEXTENTS (PCI_CONF_MAX_BARS * MAX_PLATFORM_DEVICES)
#define MAX_SLAB_MEMIOREGIONS_IOEXTENTS (PCI_CONF_MAX_BARS * MAX_PLATFORM_DEVICES)

#define _MEMIOREGIONS_EXTENTS_TYPE_MEM  0
#define _MEMIOREGIONS_EXTENTS_TYPE_IO   1
#define _MEMIOREGIONS_EXTENTS_TYPE_NONE 3

typedef struct {
    u32 extent_type;
    u32 addr_start;
    u32 addr_end;
} __attribute__((packed)) _memioregions_extents_t;

typedef struct {
    u32 num_memextents;
    u32 num_ioextents;
    _memioregions_extents_t memextents[MAX_SLAB_MEMIOREGIONS_MEMEXTENTS];
    _memioregions_extents_t ioextents[MAX_SLAB_MEMIOREGIONS_IOEXTENTS];
} __attribute__((packed)) slab_memioregions_t;


#define SYSDEV_MEMIOREGIONS_DTYPE_GENERAL   0
#define SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE    1
#define SYSDEV_MEMIOREGIONS_DTYPE_LAPIC     2
#define SYSDEV_MEMIOREGIONS_DTYPE_TPM       3
#define SYSDEV_MEMIOREGIONS_DTYPE_TXT       4
#define SYSDEV_MEMIOREGIONS_DTYPE_IOMMU     5
#define SYSDEV_MEMIOREGIONS_DTYPE_SERIAL0   6

#define SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN   0xFF

typedef struct {
    u32 b;
    u32 d;
    u32 f;
    u16 vendor_id;
    u16 device_id;
    u32 dtype;
    _memioregions_extents_t memioextents[PCI_CONF_MAX_BARS];
} __attribute__((packed)) sysdev_memioregions_t;


typedef struct {
    u32 device_count;
    u32 sysdev_mmioregions_indices[MAX_PLATFORM_DEVICES];
} __attribute__((packed)) slab_devicemap_t;


typedef struct {
    u8 tss_mainblock[PAGE_SIZE_4K];
    u8 tss_iobitmap[3*PAGE_SIZE_4K];
} __attribute__((packed)) geec_prime_tss_t;





typedef struct {
    u32 ap_cr3;             //0
    u32 ap_cr4;             //4
    u32 ap_entrypoint;      //8
    u32 _filler0;           //12
    u32 ap_gdtdesc_limit;   //16
    u32 ap_gdtdesc_base;    //20
    u32 ap_cs_selector;     //24
    u32 ap_eip;             //28
    u32 cpuidtable;         //32
    u32 _filler1;
    u32 _filler2;
    u32 _filler3;
    u64 ap_gdt[X86SMP_APBOOTSTRAP_MAXGDTENTRIES];
}__attribute__((packed)) x86smp_apbootstrapdata_t;

typedef struct {
  u8 vmx_vmxon_region[PAGE_SIZE_4K];
  u8 vmx_vmcs_region[PAGE_SIZE_4K];
  u8 vmx_msr_area_host_region[2*PAGE_SIZE_4K];
  u8 vmx_msr_area_guest_region[2*PAGE_SIZE_4K];
  u8 vmx_iobitmap_region[2][PAGE_SIZE_4K];		//I/O Bitmap area
  u8 vmx_msrbitmaps_region[PAGE_SIZE_4K];		//MSR bitmap area
  u64 vmx_msrs[IA32_VMX_MSRCOUNT];
  u64 vmx_msr_efer;
  u64 vmx_msr_efcr;
  x86regs_t vmx_gprs;
  u8 _filler0[3952]; //page-align the whole structure
} __attribute__((packed)) xc_cpuarchdata_x86vmx_t;


typedef struct {
	XMHF_BOOTINFO xcbootinfo_store;
	u64 gp_vhslabmempgtbl_lvl4t[PAE_MAXPTRS_PER_PML4T];
	u64 gp_uhslabmempgtbl_lvl4t[XMHFGEEC_TOTAL_UHSLABS][PAE_MAXPTRS_PER_PML4T];
	u8 gp_uhslab_iobitmap[XMHFGEEC_TOTAL_UHSLABS][3*PAGE_SIZE_4K];
	u8 gp_ugslab_iobitmap[XMHFGEEC_TOTAL_UGSLABS][3*PAGE_SIZE_4K];
} gp_rwdatahdr_t;


typedef struct {
    bool devpgtbl_initialized;
}__attribute__((packed)) _slabdevpgtbl_infotable_t;



extern __attribute__(( section(".data") )) XMHF_BOOTINFO *xcbootinfo;

extern __attribute__(( section(".rwdatahdr") )) gp_rwdatahdr_t gp_rwdatahdr;

extern __attribute__((section(".data"))) __attribute__(( aligned(16) )) idtentry_t __xmhfhic_x86vmx_idt_start[EMHF_XCPHANDLER_MAXEXCEPTIONS]; //ro
extern __attribute__((section(".data"))) __attribute__(( aligned(16) )) u64 __xmhfhic_x86vmx_gdt_start[];     //ro
extern __attribute__((section(".data"))) __attribute__(( aligned(16) )) arch_x86_gdtdesc_t __xmhfhic_x86vmx_gdt;  //ro
extern __attribute__((section(".data"))) u32  __xmhfhic_exceptionstubs[]; //ro
extern __attribute__((section(".data"))) __attribute__(( aligned(16) )) arch_x86_idtdesc_t __xmhfhic_x86vmx_idt; //ro


extern __attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) u8 _init_cpustacks[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];
//extern __attribute__((section(".data"))) __attribute__(( aligned(4096) )) u8 __xmhfhic_x86vmx_tss[MAX_PLATFORM_CPUS][PAGE_SIZE_4K]; //ro
extern __attribute__((section(".data"))) __attribute__(( aligned(4096) )) geec_prime_tss_t __xmhfhic_x86vmx_tss[MAX_PLATFORM_CPUS];
extern __attribute__((section(".stack"))) __attribute__(( aligned(4096) )) u8 __xmhfhic_x86vmx_tss_stack[MAX_PLATFORM_CPUS][PAGE_SIZE_4K];
extern __attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) u8 _geec_primesmp_sysenter_stack[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];
extern __attribute__((section(".data"))) __attribute__(( aligned(4096) )) xc_cpuarchdata_x86vmx_t __xmhfhic_x86vmx_archdata[MAX_PLATFORM_CPUS];
extern __attribute__((section(".data"))) __attribute__(( aligned(8) )) u32 __xmhfhic_x86vmx_cpuidtable[MAX_X86_APIC_ID]; //ro

// initialization BSP stack
extern __attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) u8 _init_bsp_cpustack[MAX_PLATFORM_CPUSTACK_SIZE];


//////
// verified hypervisor slab memory page-tables
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) u64 gp_vhslabmempgtbl_lvl3t[PAE_MAXPTRS_PER_PDPT];
//extern __attribute__((section(".data"))) __attribute__((aligned(4096))) u64 gp_vhslabmempgtbl_lvl2t[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) u64 gp_vhslabmempgtbl_lvl2t[PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT];
//extern __attribute__((section(".data"))) __attribute__((aligned(4096)))  u64 gp_vhslabmempgtbl_lvl1t[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT][PAE_PTRS_PER_PT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096)))  u64 gp_vhslabmempgtbl_lvl1t[PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT];

//////
// unverified hypervisor slab memory page-tables
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) u64 gp_uhslabmempgtbl_lvl3t[XMHFGEEC_TOTAL_UHSLABS][PAE_MAXPTRS_PER_PDPT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) u64 gp_uhslabmempgtbl_lvl2t[XMHFGEEC_TOTAL_UHSLABS][PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096)))  u64 gp_uhslabmempgtbl_lvl1t[XMHFGEEC_TOTAL_UHSLABS][PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT];

//////
// bootstrap unity mapped page-tables
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) u64 _xcprimeon_init_pdt[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) u64 _xcprimeon_init_pdpt[PAE_MAXPTRS_PER_PDPT];


extern __attribute__((section(".data"))) slab_devicemap_t _sda_slab_devicemap[XMHFGEEC_TOTAL_SLABS];

extern __attribute__((section(".data"))) sysdev_memioregions_t sysdev_memioregions[MAX_PLATFORM_DEVICES];
extern __attribute__((section(".data"))) u32 numentries_sysdev_memioregions;


extern __attribute__((section(".data"))) struct _memorytype _vmx_ept_memorytypes[MAX_MEMORYTYPE_ENTRIES]; //EPT memory types array

extern __attribute__((section(".data"))) mtrr_state_t _mtrrs;
extern __attribute__((section(".data"))) mtrr_state_t sinit2mle_mtrrs;

extern __attribute__((section(".data"))) u32 gp_state4_smplock;


//DMA Remapping Hardware Unit Definitions
extern __attribute__((section(".data"))) VTD_DRHD vtd_drhd[VTD_MAX_DRHD];
extern __attribute__((section(".data"))) u32 vtd_num_drhd;	//total number of DMAR h/w units
extern __attribute__((section(".data"))) bool vtd_drhd_scanned;	//set to true once DRHD units have been scanned in the system

extern __attribute__((section(".data"))) vtd_drhd_handle_t vtd_drhd_maxhandle;
extern __attribute__((section(".data"))) u32 vtd_dmar_table_physical_address;
extern __attribute__((section(".data"))) u32 vtd_ret_address;


//DMA page tables
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_ret_entry_t _slabdevpgtbl_vtd_ret[VTD_RET_MAXPTRS];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_cet_entry_t _slabdevpgtbl_vtd_cet[VTD_RET_MAXPTRS][VTD_CET_MAXPTRS];

extern __attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pml4te_t _slabdevpgtbl_pml4t[XMHFGEEC_TOTAL_SLABS][PAE_MAXPTRS_PER_PML4T];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pdpte_t _slabdevpgtbl_pdpt[XMHFGEEC_TOTAL_SLABS][PAE_MAXPTRS_PER_PDPT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pdte_t _slabdevpgtbl_pdt[XMHFGEEC_TOTAL_SLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pte_t _slabdevpgtbl_pt[XMHFGEEC_TOTAL_SLABS][MAX_SLAB_DMADATA_PDT_ENTRIES][PAE_PTRS_PER_PT];
extern __attribute__((section(".data"))) _slabdevpgtbl_infotable_t _slabdevpgtbl_infotable[XMHFGEEC_TOTAL_SLABS];
extern __attribute__((section(".data"))) u32 vtd_pagewalk_level;


//SMP
extern __attribute__((section(".data"))) x86smp_apbootstrapdata_t apdata;





//////////////////////////////////////////////////////////////////////////////
// setup slab memory page tables (smt)

#define _SLAB_SPATYPE_MASK_SAMESLAB             (0x100)

#define	_SLAB_SPATYPE_SLAB_CODE					(0x0)
#define	_SLAB_SPATYPE_SLAB_DATA	    			(0x1)
#define _SLAB_SPATYPE_SLAB_STACK				(0x2)
#define _SLAB_SPATYPE_SLAB_DMADATA				(0x3)
#define _SLAB_SPATYPE_SLAB_DEVICEMMIO           (0x4)
#define _SLAB_SPATYPE_GEEC_PRIME_IOTBL          (0x5)

#define _SLAB_SPATYPE_OTHER	    				(0x6)





void gp_s1_bspstack(void);

u64 _gp_s1_bspstack_getflagsforspa(u32 paddr);

void gp_s1_bspstkactivate(void);
void gp_s1_hub(void);
void gp_s1_chkreq(void);
void gp_s1_postdrt(void);
void gp_s1_scaniommu(void);
void gp_s1_iommuinittbl(void);

/*@
	requires 0 <= retindex < VTD_RET_MAXPTRS;
@*/
void gp_s1_iommuinittbl_clearcet(u32 retindex);

void gp_s1_iommuinit(void);


void gp_s2_entry(void);
void gp_s2_setupslabdevmap(void);



/*@
	requires 0 <= uhslabiobitmap_idx < XMHFGEEC_TOTAL_UHSLABS;
	requires 0 <= port < 65536;
	requires 0 <= port_size <= 4;
@*/
void gp_s2_setupiotbluh_allowaccesstoport(u32 uhslabiobitmap_idx, u16 port, u16 port_size);


/*@
	requires (slabid >= XMHFGEEC_UHSLAB_BASE_IDX && slabid <= XMHFGEEC_UHSLAB_MAX_IDX);
	requires _sda_slab_devicemap[slabid].device_count < MAX_PLATFORM_DEVICES;
	requires  \forall integer x; 0 <= x < MAX_PLATFORM_DEVICES ==> (_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x] < MAX_PLATFORM_DEVICES);
@*/
void gp_s2_setupiotbluh(u32 slabid);


/*@
	requires 0 <= ugslabiobitmap_idx < XMHFGEEC_TOTAL_UGSLABS;
	requires 0 <= port < 65536;
	requires 0 <= port_size <= 4;
@*/
void gp_s2_setupiotblug_allowaccesstoport(u32 ugslabiobitmap_idx, u16 port, u16 port_size);

/*@
	requires (slabid >= XMHFGEEC_UGSLAB_BASE_IDX && slabid <= XMHFGEEC_UGSLAB_MAX_IDX);
	requires _sda_slab_devicemap[slabid].device_count < MAX_PLATFORM_DEVICES;
	requires  \forall integer x; 0 <= x < MAX_PLATFORM_DEVICES ==> (_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x] < MAX_PLATFORM_DEVICES);
@*/
void gp_s2_setupiotblug(u32 slabid);



void gp_s2_setupiotbl(void);



void gp_s2_gathersysmemtypes(void);

/*@
	assigns \nothing;
	ensures 0 <= \result <= 7;
@*/
u32 gp_s2_setupmpgtblug_getmtype(u64 pagebaseaddr);

/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
@*/
u64 gp_s2_setupmpgtblug_getflags(u32 slabid, u32 spa, u32 spatype);



/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS ;
@*/
bool gp_s2_setupmpgtbl_getspatypeuobj_isiotbl(u32 slabid, u32 spa);

/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS ;
	requires \forall u32 x; 0 <= x < MAX_PLATFORM_CPUS ==> (_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x] < MAX_PLATFORM_DEVICES);
	requires 0 <= _sda_slab_devicemap[slabid].device_count < MAX_PLATFORM_DEVICES;
@*/
bool gp_s2_setupmpgtbl_getspatypeuobj_ismmio(u32 slabid, u32 spa);

/*@
	requires 0 <= slab_index < XMHFGEEC_TOTAL_SLABS ;
@*/
u32 gp_s2_setupmpgtbl_getspatypeuobj(u32 slab_index, u32 spa);
//u32 gp_slab_getspatype_for_slab(u32 slab_index, u32 spa);

/*@
	requires 0 <= slab_index < XMHFGEEC_TOTAL_SLABS ;
@*/
u32 gp_s2_setupmpgtbl_getspatype(u32 slab_index, u32 spa);

void gp_s2_setupmpgtblug(u32 slabid);

bool gp_s2_setupmpgtbluh_setentry(u32 slabid, u32 uhslabmempgtbl_idx, u32 spatype, u32 ptindex, u64 flags);

u64 gp_s2_setupmpgtbluh_getflags(u32 slabid, u32 spa, u32 spatype);

void gp_s2_setupmpgtbluh(u32 slabid);

/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
@*/
u64 gp_s2_setupmpgtblv_getflags(u32 slabid, u32 spa, u32 spatype);

void gp_s2_setupmpgtblv(void);

void gp_s2_setupmpgtblu(void);


/*@
	requires \valid(xcbootinfo);
	requires (xcbootinfo->cpuinfo_numentries < MAX_PLATFORM_CPUS);
@*/
void gp_s2_setupgdt(void);

/*@
	requires (__TRSEL/8) <= gdtindex <= (XMHFGEEC_MAX_GDT_CODEDATA_DESCRIPTORS + MAX_PLATFORM_CPUS);
	requires 0 <= tssidx < MAX_PLATFORM_CPUS;
@*/
void gp_s2_setupgdt_setgdttssentry(u32 gdtindex, u32 tssidx);

void gp_s2_setupidt(void);


/*@
	requires 0 <= tssidx < MAX_PLATFORM_CPUS;
@*/
void gp_s2_setuptss_inittss(u32 tssidx);


void gp_s2_setuptss(void);


void gp_s3_entry(void);
void gp_s3_startcores(void);

CASM_FUNCDECL(void gp_s4_entry(void *noparam));
CASM_FUNCDECL(void gp_s4_apstacks(void *noparam));


//void gp_s4_s6_entry(void);


void gp_s5_entry(void);
void gp_s5_setupcpustate(u32 cpuid, bool isbsp);
void gp_s5_invokestrt(u32 cpuid);



void xmhfhic_arch_setup_slab_info(void);
void xmhfhic_arch_sanity_check_requirements(void);
void xmhfhic_arch_setup_slab_device_allocation(void);
void xmhfhic_arch_setup_slab_mem_page_tables(void);


CASM_FUNCDECL(void xmhfhic_arch_relinquish_control_to_init_slab(u64 cpuid, u64 entrystub, u64 mempgtbl_cr3, u64 slabtos));

//void _geec_prime_main(void);


void xmhfhic_arch_switch_to_smp(void);
void xmhfhic_arch_setup_base_cpu_data_structures(void);
void xmhf_hic_arch_setup_cpu_state(u64 cpuid);
void xmhfhic_smp_entry(u32 cpuid);

CASM_FUNCDECL(void __xmhfhic_x86vmx_reloadCS(u32 cs_sel));
CASM_FUNCDECL(void __xmhfhic_x86vmx_reloadsegregs(u32 ds_sel));


#endif // __ASSEMBLY__


#endif /* __GEEC_PRIME_H_ */
