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

// XMHF slab decls./defns.
// author: amit vasudevan (amitvasudevan@acm.org)
// XXX: need to split arch. dependent portions

#ifndef __XMHF_HIC_H__
#define __XMHF_HIC_H__

#include <xmhf-hwm.h>            //XMHF hardware interfaces
#include <xmhfhw.h>
#include <xmhfhicslab.h>

//arch. specific decls.
#define HIC_SLAB_X86VMXX86PC_HYPERVISOR (1)
#define HIC_SLAB_X86VMXX86PC_GUEST      (2)

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

// segment selectors
#define 	__CS_CPL0 	    0x0008 	//CPL-0 code segment selector
#define 	__DS_CPL0 	    0x0010 	//CPL-0 data segment selector
#define		__CS_CPL3	    0x001b	//CPL-3 code segment selector
#define		__DS_CPL3	    0x0023  //CPL-3 data segment selector
#define		__CS_CPL3_SE	0x002b	//CPL-3 code segment selector
#define		__DS_CPL3_SE	0x0033  //CPL-3 data segment selector
#define 	__TRSEL 	    0x0038  //TSS (task) selector

#define	EMHF_XCPHANDLER_MAXEXCEPTIONS	32


#ifndef __ASSEMBLY__

/* x86_64
typedef struct {
    u64 pci_bus;
    u64 pci_device;
    u64 pci_function;
    u64 vendor_id;
    u64 device_id;
}__attribute__((packed)) xc_platformdevice_arch_desc_t;
*/

typedef struct {
    u32 pci_bus;
    u32 pci_device;
    u32 pci_function;
    u32 vendor_id;
    u32 device_id;
}__attribute__((packed)) xc_platformdevice_arch_desc_t;


typedef struct {
    u32 ap_cr3;
    u32 ap_cr4;
    u32 ap_entrypoint;
    u32 _filler0;
    u32 ap_gdtdesc_limit;
    u32 ap_gdtdesc_base;
    u32 ap_cs_selector;
    u32 ap_eip;
    u32 cpuidtable;
    u32 _filler1;
    u32 _filler2;
    u32 _filler3;
    u64 ap_gdt[X86SMP_APBOOTSTRAP_MAXGDTENTRIES];
}__attribute__((packed)) x86smp_apbootstrapdata_t;

//MTRR memory type structure
struct _memorytype {
  u64 startaddr;
  u64 endaddr;
  u32 type;
  u32 invalid;
  u32 reserved[6];
} __attribute__((packed));


typedef struct {
  u8 vmx_vmxon_region[PAGE_SIZE_4K] __attribute__((aligned(4096)));
  u8 vmx_vmcs_region[PAGE_SIZE_4K] __attribute__((aligned(4096)));
  u8 vmx_msr_area_host_region[2*PAGE_SIZE_4K] __attribute__((aligned(4096)));
  u8 vmx_msr_area_guest_region[2*PAGE_SIZE_4K] __attribute__((aligned(4096)));
  u8 vmx_iobitmap_region[2][PAGE_SIZE_4K] __attribute__((aligned(4096)));		//I/O Bitmap area
  u8 vmx_msrbitmaps_region[PAGE_SIZE_4K] __attribute__((aligned(4096)));		//MSR bitmap area
  u64 vmx_msrs[IA32_VMX_MSRCOUNT];
  u64 vmx_msr_efer;
  u64 vmx_msr_efcr;
  //x86regs64_t vmx_gprs;
  x86regs_t vmx_gprs;
} __attribute__((packed)) xc_cpuarchdata_x86vmx_t;

#endif //__ASSEMBLY__













#ifndef __ASSEMBLY__


typedef void * slab_entrystub_t;

/* x86_64
typedef u64 slab_privilegemask_t;
typedef u64 slab_callcaps_t;
typedef u64 slab_uapicaps_t;
*/

typedef u32 slab_privilegemask_t;
typedef u32 slab_callcaps_t;
typedef u32 slab_uapicaps_t;

/* x86_64
typedef struct {
	bool desc_valid;
	u64 numdevices;
    xc_platformdevice_arch_desc_t arch_desc[MAX_PLATFORM_DEVICES];
} __attribute__((packed)) slab_platformdevices_t;
*/

typedef struct {
	bool desc_valid;
	u32 numdevices;
    xc_platformdevice_arch_desc_t arch_desc[MAX_PLATFORM_DEVICES];
} __attribute__((packed)) slab_platformdevices_t;


/* x86_64
//slab capabilities type
typedef struct {
    slab_privilegemask_t slab_privilegemask;
    slab_callcaps_t slab_callcaps;
    slab_uapicaps_t slab_uapicaps;
    slab_platformdevices_t slab_devices;
    u64 slab_archparams;
} __attribute__((packed)) slab_caps_t;
*/

//slab capabilities type
typedef struct {
    slab_privilegemask_t slab_privilegemask;
    slab_callcaps_t slab_callcaps;
    slab_uapicaps_t slab_uapicaps;
    slab_platformdevices_t slab_devices;
    u32 slab_archparams;
} __attribute__((packed)) slab_caps_t;


#define HIC_SLAB_CALLCAP(x) (1 << x)
#define HIC_SLAB_UAPICAP(x) (1 << x)












typedef struct {
    u64 src_slabid;
    u64 dst_slabid;
    u64 hic_calltype;
    u64 return_address;
    slab_output_params_t *oparams;
    slab_output_params_t *newoparams;
    u64 oparams_size;
    u64 iparams_size;
} __xmhfhic_safestack_element_t;


#define HIC_SLAB_PHYSMEM_EXTENT_READ       (1 << 0)
#define HIC_SLAB_PHYSMEM_EXTENT_WRITE      (1 << 1)
#define HIC_SLAB_PHYSMEM_EXTENT_EXECUTE    (1 << 2)

#define HIC_SLAB_PHYSMEM_MAXEXTENTS         5

/* x86_64
//slab physical memory extent type
typedef struct {
    u64 addr_start;
    u64 addr_end;
    u64 protection;
} slab_physmem_extent_t;
*/

//slab physical memory extent type
typedef struct {
    u32 addr_start;
    u32 addr_end;
    u32 protection;
} slab_physmem_extent_t;



/*
typedef struct {
    __attribute__((aligned(4096))) slab_info_archdata_t archdata;
	bool slab_inuse;
    slab_privilegemask_t slab_privilegemask;
    slab_callcaps_t slab_callcaps;
    slab_uapicaps_t slab_uapicaps;
    slab_platformdevices_t slab_devices;
    slab_physmem_extent_t slab_physmem_extents[HIC_SLAB_PHYSMEM_MAXEXTENTS];
	slab_entrystub_t entrystub;
} __attribute__((packed)) __attribute__((aligned(4096))) slab_info_t;
*/






//////
//modified data types
typedef struct {
    u64 *mempgtbl_pml4t;
	u64 *mempgtbl_pdpt;
	u64 *mempgtbl_pdt;
	u64 *mempgtbl_pt;

	u64 *devpgtbl_pml4t;
	u64 *devpgtbl_pdpt;
	u64 *devpgtbl_pdt;
	u64 *devpgtbl_pt;

	u8  *deviomap;
	u64 slabtype; //hypervisor, guest
	bool mempgtbl_initialized;
	bool devpgtbl_initialized;
	u64 mempgtbl_cr3;
	u32 slabtos[MAX_PLATFORM_CPUS];
} __attribute__((packed)) x_slab_info_archdata_t;


typedef struct {
    x_slab_info_archdata_t archdata;
	bool slab_inuse;
    slab_privilegemask_t slab_privilegemask;
    slab_callcaps_t slab_callcaps;
    slab_uapicaps_t slab_uapicaps;
    slab_platformdevices_t slab_devices;
    slab_physmem_extent_t slab_physmem_extents[HIC_SLAB_PHYSMEM_MAXEXTENTS];
	slab_entrystub_t entrystub;
} __attribute__((packed)) x_slab_info_t;











//////
// HIC function prototypes

void xmhfhic_arch_setup_slab_info(void);
void xmhfhic_arch_sanity_check_requirements(void);
void xmhfhic_arch_setup_slab_device_allocation(void);
void xmhfhic_arch_setup_slab_mem_page_tables(void);
void xmhfhic_arch_switch_to_smp(void);
void xmhfhic_arch_setup_base_cpu_data_structures(void);
void xmhf_hic_arch_setup_cpu_state(u64 cpuid);
void xmhfhic_smp_entry(u32 cpuid);


extern void xmhfhic_arch_relinquish_control_to_init_slab(u64 cpuid, u64 entrystub, u64 mempgtbl_cr3, u64 slabtos);



bool __xmhfhic_callcaps(u64 src_slabid, u64 dst_slabid);

void __xmhfhic_safepush(u64 cpuid, u64 src_slabid, u64 dst_slabid, u64 hic_calltype, u64 return_address,
                        slab_output_params_t *oparams, slab_output_params_t *newoparams, u64 oparams_size, u64 iparams_size);

void __xmhfhic_safepop(u64 cpuid, u64 *src_slabid, u64 *dst_slabid, u64 *hic_calltype, u64 *return_address,
                       slab_output_params_t **oparams, slab_output_params_t **newoparams, u64 *oparams_size, u64 *iparams_size);


__attribute__((naked)) void __xmhfhic_rtm_intercept_stub(void);
void __xmhfhic_rtm_intercept(x86regs_t *r);
__attribute__((naked)) void __xmhfhic_rtm_trampoline_stub(void);

//void __xmhfhic_rtm_exception_stub(u32 vector, u32 error_code);
void __xmhfhic_rtm_exception_stub(x86vmx_exception_frame_t *exframe);

void __xmhfhic_rtm_trampoline(u64 hic_calltype, slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 dst_slabid, u64 src_slabid, u64 cpuid, u64 return_address, u64 return_rsp);
//void __xmhfhic_rtm_uapihandler(u64 uapicall, u64 uapicall_num, u64 uapicall_subnum,
//                               u64 reserved, u64 iparams, u64 oparams,
//                               u64 src_slabid, u64 cpuid);


void __xmhfhic_rtm_uapihandler(slab_params_t *sp);



//////
// HIC data decls.


//init, setup data
extern __attribute__(( section(".sharedro_xcbootinfoptr") )) XMHF_BOOTINFO *xcbootinfo; //ro
extern __attribute__((section(".data"))) slab_physmem_extent_t _xmhfhic_init_setupdata_slab_physmem_extents[XMHF_HIC_MAX_SLABS][HIC_SLAB_PHYSMEM_MAXEXTENTS]; //ro
extern __attribute__((section(".data"))) slab_physmem_extent_t _xmhfhic_init_setupdata_hic_physmem_extents[HIC_SLAB_PHYSMEM_MAXEXTENTS]; //ro
extern __attribute__((section(".data"))) slab_caps_t _xmhfhic_init_setupdata_slab_caps[XMHF_HIC_MAX_SLABS]; //ro


//runtime data

//extern __attribute__((aligned(4096))) slab_info_t _xmhfhic_common_slab_info_table[XMHF_HIC_MAX_SLABS];
extern __attribute__((section(".data"))) __attribute__((aligned(4096))) x_slab_info_t _xmhfhic_common_slab_info_table[XMHF_HIC_MAX_SLABS];

extern __attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_slpgtbl_t _dbuf_devpgtbl[XMHF_HIC_MAX_SLABS];


extern __attribute__((section(".data"))) slab_physmem_extent_t _xmhfhic_common_hic_physmem_extents[HIC_SLAB_PHYSMEM_MAXEXTENTS]; //ro
extern __attribute__((section(".data"))) u64 __xmhfhic_safestack_indices[MAX_PLATFORM_CPUS];
extern __attribute__((section(".data"))) __xmhfhic_safestack_element_t __xmhfhic_safestack[MAX_PLATFORM_CPUS][512];

//arch. dependent runtime data
extern __attribute__((section(".data"))) __attribute__(( aligned(16) )) u64 __xmhfhic_x86vmx_gdt_start[];     //ro
extern __attribute__((section(".data"))) __attribute__(( aligned(16) )) arch_x86_gdtdesc_t __xmhfhic_x86vmx_gdt;  //ro
extern __attribute__((section(".data"))) __attribute__(( aligned(4096) )) u8 __xmhfhic_x86vmx_tss[MAX_PLATFORM_CPUS][PAGE_SIZE_4K]; //ro
extern __attribute__((section(".data"))) __attribute__(( aligned(8) )) u32 __xmhfhic_x86vmx_cpuidtable[MAX_X86_APIC_ID]; //ro

extern __attribute__((section(".data"))) u32  __xmhfhic_exceptionstubs[]; //ro

extern __attribute__((section(".data"))) __attribute__(( aligned(16) )) idtentry_t __xmhfhic_x86vmx_idt_start[EMHF_XCPHANDLER_MAXEXCEPTIONS]; //ro
extern __attribute__((section(".data"))) __attribute__(( aligned(16) )) arch_x86_idtdesc_t __xmhfhic_x86vmx_idt; //ro

extern __attribute__((section(".data"))) __attribute__(( aligned(2097152) )) u64 _dbuf_mempgtbl_pml4t[XMHF_HIC_MAX_SLABS][PAE_MAXPTRS_PER_PML4T]; //ro
extern __attribute__((section(".data"))) __attribute__((aligned(4096)))	u64 _dbuf_mempgtbl_pdpt[XMHF_HIC_MAX_SLABS][PAE_MAXPTRS_PER_PDPT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096)))	u64 _dbuf_mempgtbl_pdt[XMHF_HIC_MAX_SLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
extern __attribute__((section(".data"))) __attribute__((aligned(4096)))  u64 _dbuf_mempgtbl_pt[XMHF_HIC_MAX_SLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT][PAE_PTRS_PER_PT];


extern __attribute__((section(".data"))) __attribute__(( aligned(4096) )) u8 __xmhfhic_x86vmx_tss_stack[MAX_PLATFORM_CPUS][PAGE_SIZE_4K];
extern __attribute__((section(".data"))) __attribute__(( aligned(4096) )) u8 __xmhfhic_rtm_trampoline_stack[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];
extern __attribute__((section(".data"))) __attribute__(( aligned(4096) )) xc_cpuarchdata_x86vmx_t __xmhfhic_x86vmx_archdata[MAX_PLATFORM_CPUS];

//libxmhfdebug
extern __attribute__(( section(".libxmhfdebugdata") )) u32 libxmhfdebug_lock;







#endif //__ASSEMBLY__

#endif //__XMHF_HIC_H__


