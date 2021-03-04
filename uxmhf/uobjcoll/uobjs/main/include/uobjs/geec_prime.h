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
  uint64_t startaddr;
  uint64_t endaddr;
  uint32_t type;
  uint32_t invalid;
  uint32_t reserved[6];
} __attribute__((packed));


//typedef struct {
//    uint8_t pgtbl[3 * PAGE_SIZE_4K];
//    uint8_t mlehdr[0x80];
//} __attribute__((packed)) x86vmx_mle_header_t;

#define MAX_SLAB_MEMIOREGIONS_MEMEXTENTS (PCI_CONF_MAX_BARS * MAX_PLATFORM_DEVICES)
#define MAX_SLAB_MEMIOREGIONS_IOEXTENTS (PCI_CONF_MAX_BARS * MAX_PLATFORM_DEVICES)

#define _MEMIOREGIONS_EXTENTS_TYPE_MEM  0
#define _MEMIOREGIONS_EXTENTS_TYPE_IO   1
#define _MEMIOREGIONS_EXTENTS_TYPE_NONE 3

typedef struct {
    uint32_t extent_type;
    uint32_t addr_start;
    uint32_t addr_end;
} __attribute__((packed)) _memioregions_extents_t;

typedef struct {
    uint32_t num_memextents;
    uint32_t num_ioextents;
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
    uint32_t b;
    uint32_t d;
    uint32_t f;
    uint16_t vendor_id;
    uint16_t device_id;
    uint32_t dtype;
    _memioregions_extents_t memioextents[PCI_CONF_MAX_BARS];
} __attribute__((packed)) sysdev_memioregions_t;


typedef struct {
    uint32_t device_count;
    uint32_t sysdev_mmioregions_indices[MAX_PLATFORM_DEVICES];
} __attribute__((packed)) slab_devicemap_t;


typedef struct {
    uint8_t tss_mainblock[PAGE_SIZE_4K];
    uint8_t tss_iobitmap[3*PAGE_SIZE_4K];
} __attribute__((packed)) geec_prime_tss_t;





typedef struct {
    uint32_t ap_cr3;             //0
    uint32_t ap_cr4;             //4
    uint32_t ap_entrypoint;      //8
    uint32_t _filler0;           //12
    uint32_t ap_gdtdesc_limit;   //16
    uint32_t ap_gdtdesc_base;    //20
    uint32_t ap_cs_selector;     //24
    uint32_t ap_eip;             //28
    uint32_t cpuidtable;         //32
    uint32_t _filler1;
    uint32_t _filler2;
    uint32_t _filler3;
    uint64_t ap_gdt[X86SMP_APBOOTSTRAP_MAXGDTENTRIES];
}__attribute__((packed)) x86smp_apbootstrapdata_t;

typedef struct {
  uint8_t vmx_vmxon_region[PAGE_SIZE_4K];
  uint8_t vmx_vmcs_region[PAGE_SIZE_4K];
  uint8_t vmx_msr_area_host_region[2*PAGE_SIZE_4K];
  uint8_t vmx_msr_area_guest_region[2*PAGE_SIZE_4K];
  uint8_t vmx_iobitmap_region[2][PAGE_SIZE_4K];		//I/O Bitmap area
  uint8_t vmx_msrbitmaps_region[PAGE_SIZE_4K];		//MSR bitmap area
  uint64_t vmx_msrs[IA32_VMX_MSRCOUNT];
  uint64_t vmx_msr_efer;
  uint64_t vmx_msr_efcr;
  x86regs_t vmx_gprs;
  uint8_t _filler0[3952]; //page-align the whole structure
} __attribute__((packed)) xc_cpuarchdata_x86vmx_t;


typedef struct {
	XMHF_BOOTINFO xcbootinfo_store;
	uint64_t gp_vhslabmempgtbl_lvl4t[PAE_MAXPTRS_PER_PML4T];
	//uint8_t gp_uhslab_iobitmap[XMHFGEEC_TOTAL_UHSLABS][3*PAGE_SIZE_4K];
	//uint8_t gp_ugslab_iobitmap[XMHFGEEC_TOTAL_UGSLABS][3*PAGE_SIZE_4K];
} __attribute__((packed)) gp_rwdatahdr_t;


typedef struct {
    bool devpgtbl_initialized;
}__attribute__((packed)) _slabdevpgtbl_infotable_t;



extern __attribute__(( section(".data") )) XMHF_BOOTINFO *xcbootinfo;

extern __attribute__(( section(".hdrdata") )) gp_rwdatahdr_t gp_rwdatahdr;

extern __attribute__((section(".data"))) __attribute__(( aligned(16) )) uint64_t __xmhfhic_x86vmx_gdt_start[];     //ro
extern __attribute__((section(".data"))) __attribute__(( aligned(16) )) arch_x86_gdtdesc_t __xmhfhic_x86vmx_gdt;  //ro
extern __attribute__((section(".data"))) uint32_t  __xmhfhic_exceptionstubs[]; //ro


extern __attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) uint8_t _init_cpustacks[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];
//extern __attribute__((section(".data"))) __attribute__(( aligned(4096) )) uint8_t __xmhfhic_x86vmx_tss[MAX_PLATFORM_CPUS][PAGE_SIZE_4K]; //ro
extern __attribute__((section(".data"))) __attribute__(( aligned(4096) )) geec_prime_tss_t __xmhfhic_x86vmx_tss[MAX_PLATFORM_CPUS];
extern __attribute__((section(".stack"))) __attribute__(( aligned(4096) )) uint8_t __xmhfhic_x86vmx_tss_stack[MAX_PLATFORM_CPUS][PAGE_SIZE_4K];
//extern __attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) uint8_t _geec_primesmp_sysenter_stack[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];
extern __attribute__((section(".data"))) __attribute__(( aligned(4096) )) xc_cpuarchdata_x86vmx_t __xmhfhic_x86vmx_archdata[MAX_PLATFORM_CPUS];
extern __attribute__((section(".data"))) __attribute__(( aligned(8) )) uint32_t __xmhfhic_x86vmx_cpuidtable[MAX_X86_APIC_ID]; //ro

// initialization BSP stack
extern __attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) uint8_t _init_bsp_cpustack[MAX_PLATFORM_CPUSTACK_SIZE];


//////
// verified hypervisor slab memory page-tables
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t gp_vhslabmempgtbl_lvl3t[PAE_MAXPTRS_PER_PDPT];
//extern __attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t gp_vhslabmempgtbl_lvl2t[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t gp_vhslabmempgtbl_lvl2t[PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT];
//extern __attribute__((section(".data"))) __attribute__((aligned(4096)))  uint64_t gp_vhslabmempgtbl_lvl1t[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT][PAE_PTRS_PER_PT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096)))  uint64_t gp_vhslabmempgtbl_lvl1t[PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT];

#if 1
//////
// unverified hypervisor slab memory page-tables
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t gp_uhslabmempgtbl_lvl3t[XMHFGEEC_TOTAL_UHSLABS][PAE_MAXPTRS_PER_PDPT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t gp_uhslabmempgtbl_lvl2t[XMHFGEEC_TOTAL_UHSLABS][PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096)))  uint64_t gp_uhslabmempgtbl_lvl1t[XMHFGEEC_TOTAL_UHSLABS][PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT * PAE_PTRS_PER_PT];
#endif

//////
// bootstrap unity mapped page-tables
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t _xcprimeon_init_pdt[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) uint64_t _xcprimeon_init_pdpt[PAE_MAXPTRS_PER_PDPT];


extern __attribute__((section(".data"))) slab_devicemap_t _sda_slab_devicemap[XMHFGEEC_TOTAL_SLABS];

extern __attribute__((section(".data"))) sysdev_memioregions_t sysdev_memioregions[MAX_PLATFORM_DEVICES];
extern __attribute__((section(".data"))) uint32_t numentries_sysdev_memioregions;


extern __attribute__((section(".data"))) struct _memorytype _vmx_ept_memorytypes[MAX_MEMORYTYPE_ENTRIES]; //EPT memory types array

extern __attribute__((section(".data"))) mtrr_state_t _mtrrs;
extern __attribute__((section(".data"))) mtrr_state_t sinit2mle_mtrrs;

extern __attribute__((section(".data"))) uint32_t gp_state4_smplock;


//DMA Remapping Hardware Unit Definitions
extern __attribute__((section(".data"))) VTD_DRHD vtd_drhd[VTD_MAX_DRHD];
extern __attribute__((section(".data"))) uint32_t vtd_num_drhd;	//total number of DMAR h/w units
extern __attribute__((section(".data"))) bool vtd_drhd_scanned;	//set to true once DRHD units have been scanned in the system

extern __attribute__((section(".data"))) vtd_drhd_handle_t vtd_drhd_maxhandle;
extern __attribute__((section(".data"))) uint32_t vtd_dmar_table_physical_address;
extern __attribute__((section(".data"))) uint32_t vtd_ret_address;


//DMA page tables
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_ret_entry_t _slabdevpgtbl_vtd_ret[VTD_RET_MAXPTRS];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_cet_entry_t _slabdevpgtbl_vtd_cet[VTD_RET_MAXPTRS][VTD_CET_MAXPTRS];

extern __attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pml4te_t _slabdevpgtbl_pml4t[XMHFGEEC_TOTAL_SLABS][PAE_MAXPTRS_PER_PML4T];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pdpte_t _slabdevpgtbl_pdpt[XMHFGEEC_TOTAL_SLABS][PAE_MAXPTRS_PER_PDPT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pdte_t _slabdevpgtbl_pdt[XMHFGEEC_TOTAL_SLABS][PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pte_t _slabdevpgtbl_pt[XMHFGEEC_TOTAL_SLABS][MAX_SLAB_DMADATA_PDT_ENTRIES][PAE_PTRS_PER_PT];

//rich-guest DMA page-tables
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pte_t _slabdevpgtbl_pt_rg[VTD_PTRS_PER_PDPT * VTD_PTRS_PER_PDT * VTD_PTRS_PER_PT];


extern __attribute__((section(".data"))) _slabdevpgtbl_infotable_t _slabdevpgtbl_infotable[XMHFGEEC_TOTAL_SLABS];
extern __attribute__((section(".data"))) uint32_t vtd_pagewalk_level;


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



//////
// stage-1
//////
void gp_s1_bspstack(void);
uint64_t _gp_s1_bspstack_getflagsforspa(uint32_t paddr);
void gp_s1_bspstkactivate(void);
void gp_s1_hub(void);
void gp_s1_chkreq(void);
void gp_s1_postdrt(void);
void gp_s1_scaniommu(void);
void gp_s1_iommuinittbl(void);

/*@
	requires 0 <= retindex < VTD_RET_MAXPTRS;
@*/
void gp_s1_iommuinittbl_clearcet(uint32_t retindex);

void gp_s1_iommuinit(void);



//////
// stage-2
//////

/*@
	requires (gp_rwdatahdr.xcbootinfo_store.memmapinfo_numentries < MAX_E820_ENTRIES);
@*/
void gp_s2_entry(void);

void gp_s2_gathersysmemtypes(void);

/*@
	requires (gp_rwdatahdr.xcbootinfo_store.memmapinfo_numentries < MAX_E820_ENTRIES);
@*/
void gp_s2_initsysmemmap(void);


void gp_s2_sda(void);







/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
@*/
bool gp_s2_sdabinddevice(uint32_t slabid, uint32_t pagewalk_lvl,  uint32_t bus, uint32_t dev, uint32_t func);

/*@
	requires 0 <= numentries_sysdev_memioregions < MAX_PLATFORM_DEVICES;
@*/
void gp_s2_sdadoalloc(void);

/*@
	assigns \nothing;
	ensures (\result == 0xFFFFFFFFUL || (0 <= \result < XMHFGEEC_TOTAL_SLABS));
@*/
uint32_t gp_s2_sdadoalloc_getuobjfordev(uint32_t bus, uint32_t dev, uint32_t func);


/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
@*/
void gp_s2_sdasetupdevpgtbl_rg(uint32_t slabid);

/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
@*/
void gp_s2_sdasetupdevpgtbl(uint32_t slabid);

/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
	requires 0 <= pd_index < MAX_SLAB_DMADATA_PDT_ENTRIES;
	requires (startpaddr < (0xFFFFFFFFUL - PAGE_SIZE_2M));
@*/
void gp_s2_sdasetupdevpgtbl_setptentries(uint32_t slabid, uint32_t pd_index, uint32_t startpaddr);


/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
	requires (paddr_end >= paddr_start);
	requires (paddr_end < (0xFFFFFFFFUL - PAGE_SIZE_2M));
	requires (paddr_end - paddr_start) <= MAX_SLAB_DMADATA_SIZE;
@*/
void gp_s2_sdasetupdevpgtbl_splintpdt(uint32_t slabid, uint32_t paddr_start, uint32_t paddr_end);



/*@
	requires 0 <= vtd_drhd_maxhandle <= VTD_MAX_DRHD;
	ensures 0 <= numentries_sysdev_memioregions <= MAX_PLATFORM_DEVICES;
@*/
void gp_s2_sdmenumsysdevices(void);

/*@
	behavior addentry:
		ensures 0 <= numentries_sysdev_memioregions <= MAX_PLATFORM_DEVICES;
@*/
void gp_s2_sdmenumsysdevices_memioextents(uint32_t b, uint32_t d, uint32_t f, uint32_t vendor_id, uint32_t device_id);


/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
	requires 0 <= numentries_sysdev_memioregions <= MAX_PLATFORM_DEVICES;
	requires 0 <= xmhfgeec_slab_info_table[slabid].excl_devices_count <= XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES;
@*/
void gp_s2_sdminitdevmap_addalldevstouobj(uint32_t slabid);

/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;

	behavior addentry:
		ensures _sda_slab_devicemap[slabid].sysdev_mmioregions_indices[\at(_sda_slab_devicemap[slabid].device_count, Pre)] == sysdev_mmioregions_index;
		ensures (_sda_slab_devicemap[slabid].device_count == (\at(_sda_slab_devicemap[slabid].device_count, Pre) + 1));
		ensures (_sda_slab_devicemap[slabid].device_count <= MAX_PLATFORM_DEVICES);
@*/
void gp_s2_sdminitdevmap_adddeventry(uint32_t slabid, uint32_t sysdev_mmioregions_index);


/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
	requires 0 <= numentries_sysdev_memioregions <= MAX_PLATFORM_DEVICES;
	requires 0 <= xmhfgeec_slab_info_table[slabid].excl_devices_count <= XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES;
@*/
void gp_s2_sdminitdevmap_adddevtouobj(uint32_t slabid, uint32_t vendor_id, uint32_t device_id);


/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
	requires 0 <= xmhfgeec_slab_info_table[slabid].excl_devices_count <= XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES;

	assigns \nothing;

	ensures (\result == true) || (\result == false);
@*/
bool gp_s2_sdminitdevmap_isdevinexcl(uint32_t slabid, uint32_t vendor_id, uint32_t device_id);

/*@
	requires \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==>
		(0 <= xmhfgeec_slab_info_table[x].incl_devices_count <= XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES);
	requires \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==>
		(0 <= xmhfgeec_slab_info_table[x].excl_devices_count <= XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES);
	requires 0 <= numentries_sysdev_memioregions <= MAX_PLATFORM_DEVICES;
@*/
void gp_s2_sdminitdevmap(void);




/*@
	requires (slabid >= XMHFGEEC_UHSLAB_BASE_IDX && slabid <= XMHFGEEC_UHSLAB_MAX_IDX);
	requires _sda_slab_devicemap[slabid].device_count < MAX_PLATFORM_DEVICES;
	requires  \forall integer x; 0 <= x < MAX_PLATFORM_DEVICES ==> (_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x] < MAX_PLATFORM_DEVICES);
@*/
void gp_s2_setupiotbluh(uint32_t slabid);


/*@
	requires (slabid >= XMHFGEEC_UGSLAB_BASE_IDX && slabid <= XMHFGEEC_UGSLAB_MAX_IDX);
	requires _sda_slab_devicemap[slabid].device_count < MAX_PLATFORM_DEVICES;
	requires  \forall integer x; 0 <= x < MAX_PLATFORM_DEVICES ==> (_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x] < MAX_PLATFORM_DEVICES);
@*/
void gp_s2_setupiotblug(uint32_t slabid);


void gp_s2_setupiotblug_rg(uint32_t slabid);



void gp_s2_setupiotbl(void);




/*@
	assigns \nothing;
	ensures 0 <= \result <= 7;
@*/
uint32_t gp_s2_setupmpgtblug_getmtype(uint64_t pagebaseaddr);

/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
@*/
uint64_t gp_s2_setupmpgtblug_getflags(uint32_t slabid, uint32_t spa, uint32_t spatype);



/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS ;
@*/
bool gp_s2_setupmpgtbl_getspatypeuobj_isiotbl(uint32_t slabid, uint32_t spa);

/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS ;
	requires \forall uint32_t x; 0 <= x < MAX_PLATFORM_CPUS ==> (_sda_slab_devicemap[slabid].sysdev_mmioregions_indices[x] < MAX_PLATFORM_DEVICES);
	requires 0 <= _sda_slab_devicemap[slabid].device_count < MAX_PLATFORM_DEVICES;
@*/
bool gp_s2_setupmpgtbl_getspatypeuobj_ismmio(uint32_t slabid, uint32_t spa);

/*@
	requires 0 <= slab_index < XMHFGEEC_TOTAL_SLABS ;
@*/
uint32_t gp_s2_setupmpgtbl_getspatypeuobj(uint32_t slab_index, uint32_t spa);
//uint32_t gp_slab_getspatype_for_slab(uint32_t slab_index, uint32_t spa);

/*@
	requires 0 <= slab_index < XMHFGEEC_TOTAL_SLABS ;
@*/
uint32_t gp_s2_setupmpgtbl_getspatype(uint32_t slab_index, uint32_t spa);


/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
@*/
void gp_s2_setupmpgtblug(uint32_t slabid);


/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
@*/
void gp_s2_setupmpgtblug_rg(uint32_t slabid);


/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
	requires 0 <= uhslabmempgtbl_idx < XMHFGEEC_TOTAL_UHSLABS;
	requires 0 <= ptindex < (1024*1024);
	ensures (\result == true) || (\result == false);
@*/
bool gp_s2_setupmpgtbluh_setentry(uint32_t slabid, uint32_t uhslabmempgtbl_idx, uint32_t spatype, uint32_t ptindex, uint64_t flags);

/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
@*/
uint64_t gp_s2_setupmpgtbluh_getflags(uint32_t slabid, uint32_t spa, uint32_t spatype);


/*@
	requires XMHFGEEC_UHSLAB_BASE_IDX <= slabid <= XMHFGEEC_UHSLAB_MAX_IDX;
@*/
void gp_s2_setupmpgtbluh(uint32_t slabid);

/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;
@*/
uint64_t gp_s2_setupmpgtblv_getflags(uint32_t slabid, uint32_t spa, uint32_t spatype);

void gp_s2_setupmpgtblv(void);

void gp_s2_setupmpgtblu(void);


void gp_s2_setupgdt(void);

/*@
	requires (__TRSEL/8) <= gdtindex <= (XMHFGEEC_MAX_GDT_CODEDATA_DESCRIPTORS + MAX_PLATFORM_CPUS);
	requires 0 <= tssidx < MAX_PLATFORM_CPUS;
@*/
void gp_s2_setupgdt_setgdttssentry(uint32_t gdtindex, uint32_t tssidx);

void gp_s2_setupidt(void);


/*@
	requires 0 <= tssidx < MAX_PLATFORM_CPUS;
@*/
void gp_s2_setuptss_inittss(uint32_t tssidx);


void gp_s2_setuptss(void);



void gp_s3_entry(void);
void gp_s3_startcores(void);



CASM_FUNCDECL(void gp_s4_entry(void *noparam));
CASM_FUNCDECL(void gp_s4_apstacks(void *noparam));


void gp_s5_entry(void);
void gp_s5_setupcpustate(uint32_t cpuid, bool isbsp);
void gp_s5_invokestrt(uint32_t cpuid);


#endif // __ASSEMBLY__


#endif /* __GEEC_PRIME_H_ */
