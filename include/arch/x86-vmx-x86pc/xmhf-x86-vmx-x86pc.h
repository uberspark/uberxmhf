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

// xmhf-x86-vmx-x86pc.h
// XMHF x86-vmx-x86pc arch header
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef _XMHF_X86_VMX_X86PC_H_
#define _XMHF_X86_VMX_X86PC_H_

#include "_config.h"								//include arch. specific configuration parameters

#include <xmhfhw/platform/x86pc/_multiboot.h>		//multiboot
#include <xmhfhw/cpu/x86/_processor.h>  			//CPU
#include <xmhfhw/cpu/x86/_msr.h>        			//model specific registers
#include <xmhfhw/cpu/x86/_paging.h>     			//MMU
#include <xmhfhw/cpu/x86/_io.h>         			//legacy I/O
#include <xmhfhw/cpu/x86/_apic.h>       			//APIC
#include <xmhfhw/cpu/x86/txt/_txt.h>				//Trusted eXecution Technology (SENTER support)
#include <xmhfhw/container/vmx/_vmx.h>				//VMX extensions
#include <xmhfhw/platform/x86pc/_pci.h>        		//PCI bus glue
#include <xmhfhw/platform/x86pc/_acpi.h>			//ACPI glue
#include <xmhfhw/platform/x86pc/_com.h>        		//UART/serial
#include <xmhfhw/platform/x86pc/vtd/vtd.h>			//VMX DMA protection
#include <xmhfhw/platform/x86pc/_memaccess.h>		//platform memory access
#include <xmhfhw/platform/x86pc/_tpm.h>        		//TPM
#include <xmhfhw/platform/x86pc/_biosdata.h>		//BIOS data areas

#ifndef __ASSEMBLY__

typedef struct {
    u64 pci_bus;
    u64 pci_device;
    u64 pci_function;
    u64 vendor_id;
    u64 device_id;
}__attribute__((packed)) xc_platformdevice_arch_desc_t;


typedef struct {
    u32 ap_cr3;
    u32 ap_cr4;
    u32 ap_entrypoint;
    u32 ap_gdtdesc_limit __attribute__((aligned(16)));
    u32 ap_gdtdesc_base;
    u32 ap_cs_selector;
    u32 ap_eip;
    u64 ap_gdt[X86SMP_APBOOTSTRAP_MAXGDTENTRIES] __attribute__ ((aligned (16)));
}__attribute__((aligned(16),packed)) x86smp_apbootstrapdata_t;

typedef struct {
  u32 eip;
  u32 cs;
  u32 eflags;
} __attribute__((packed)) INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE;

//---platform
typedef struct {
  u32 errorcode;
  u32 eip;
  u32 cs;
  u32 eflags;
} __attribute__((packed)) INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE;

//MTRR memory type structure
struct _memorytype {
  u64 startaddr;
  u64 endaddr;
  u32 type;
  u32 invalid;
  u32 reserved[6];
} __attribute__((packed));

//---platform
#define MAX_MEMORYTYPE_ENTRIES    98    //8*11 fixed MTRRs and 10 variable MTRRs
#define MAX_FIXED_MEMORYTYPE_ENTRIES  88
#define MAX_VARIABLE_MEMORYTYPE_ENTRIES 10


//---platform
//total number of FIXED and VARIABLE MTRRs on current x86 platforms
#define NUM_MTRR_MSRS		31


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

//---platform
#define IA32_VMX_MSRCOUNT   								12


// segment selectors
#define 	__CS_CPL0 	0x0008 	//CPL-0 code segment selector
#define 	__DS_CPL0 	0x0010 	//CPL-0 data segment selector
#define		__CS_CPL3	0x001b	//CPL-3 code segment selector
#define		__DS_CPL3	0x0023  //CPL-3 data segment selector
#define 	__TRSEL 	0x0028  //TSS (task) selector


//*
//x86 GDT descriptor type
typedef struct {
		u16 size;
		u64 base;
} __attribute__((packed)) arch_x86_gdtdesc_t;

//*
//x86 IDT descriptor type
typedef struct {
		u16 size;
		u64 base;
} __attribute__((packed)) arch_x86_idtdesc_t;

//*
//TSS descriptor (partial)
typedef struct __tss {
	u32 reserved;
	u64 rsp0;
} tss_t;

#define	EMHF_XCPHANDLER_MAXEXCEPTIONS	32
#define EMHF_XCPHANDLER_IDTSIZE			(EMHF_XCPHANDLER_MAXEXCEPTIONS * 8)


//----------------------------------------------------------------------
// function decls.
//----------------------------------------------------------------------


//void _ap_pmode_entry_with_paging(void);

//get CPU vendor
//u32 xmhf_baseplatform_arch_getcpuvendor(void);

//initialize CPU state
//void xmhf_baseplatform_arch_cpuinitialize(void);

//initialize SMP
//void xmhf_baseplatform_arch_smpinitialize(void);

//initialize basic platform elements
//void xmhf_baseplatform_arch_initialize(void);

//reboot platform
//void xmhf_baseplatform_arch_reboot(context_desc_t context_desc);

//returns true if CPU has support for XSAVE/XRSTOR
bool xmhf_baseplatform_arch_x86_cpuhasxsavefeature(void);


u32 xmhf_baseplatform_arch_x86_getcpuvendor(void);

void xmhf_baseplatform_arch_x86_cpu_initialize(void);

//return 1 if the calling CPU is the BSP
bool xmhf_baseplatform_arch_x86_isbsp(void);

//wake up APs using the LAPIC by sending the INIT-SIPI-SIPI IPI sequence
void xmhf_baseplatform_arch_x86_wakeupAPs(void);

//generic x86 platform reboot
void xmhf_baseplatform_arch_x86_reboot(void);

//get the physical address of the root system description pointer (rsdp)
u32 xmhf_baseplatform_arch_x86_acpi_getRSDP(ACPI_RSDP *rsdp);

//PCI subsystem initialization
void xmhf_baseplatform_arch_x86_pci_initialize(void);

//does a PCI type-1 write of PCI config space for a given bus, device,
//function and index
void xmhf_baseplatform_arch_x86_pci_type1_write(u32 bus, u32 device, u32 function, u32 index, u32 len,
	u32 value);

//does a PCI type-1 read of PCI config space for a given bus, device,
//function and index
void xmhf_baseplatform_arch_x86_pci_type1_read(u32 bus, u32 device, u32 function, u32 index, u32 len,
			u32 *value);

//microsecond delay
void xmhf_baseplatform_arch_x86_udelay(u32 usecs);

//initialize GDT
void xmhf_baseplatform_arch_x86_initializeGDT(void);

//initialize IO privilege level
void xmhf_baseplatform_arch_x86_initializeIOPL(void);

//initialize IDT
void xmhf_baseplatform_arch_x86_initializeIDT(void);

//setup core page tables
u32 xmhf_baseplatform_arch_x86_setup_pagetables(void);

//initialize paging
void xmhf_baseplatform_arch_x86_initialize_paging(u32 pgtblbase);

void xmhf_baseplatform_arch_x86_savecpumtrrstate(void);
void xmhf_baseplatform_arch_x86_restorecpumtrrstate(void);

u64 xmhf_baseplatform_arch_x86_getgdtbase(void);
u64 xmhf_baseplatform_arch_x86_getidtbase(void);
u64 xmhf_baseplatform_arch_x86_gettssbase(void);


typedef struct {
	u32 portnum;
	u32 access_type;
	u32 access_size;
} xc_hypapp_arch_param_x86vmx_cbtrapio_t;

typedef struct {
	u32 portnum;
	u32 access_size;
} xc_hypapp_arch_param_x86vmx_trapio_t;

typedef struct {
	x86desc_t cs;
	x86desc_t ds;
	x86desc_t es;
	x86desc_t fs;
	x86desc_t gs;
	x86desc_t ss;
	x86desc_t idtr;
	x86desc_t ldtr;
	x86desc_t gdtr;
	x86desc_t tr;
} xc_hypapp_arch_param_x86vmx_cpustate_desc_t;

typedef struct {
	u64 rip;
	u64 rflags;
	u32 activity_state;
	u32 interruptibility;
} xc_hypapp_arch_param_x86vmx_cpustate_activity_t;

typedef struct {
	u64 cr0;
	u64 control_cr0_shadow;
	u64 cr3;
	u64 cr4;
} xc_hypapp_arch_param_x86vmx_cpustate_controlregs_t;

typedef struct {
	u32 sysenter_cs;
	u64 sysenter_rsp;
	u64 sysenter_rip;
} xc_hypapp_arch_param_x86vmx_cpustate_sysenter_t;

typedef struct {
  u32  info_vminstr_error;
  u32  info_vmexit_reason;
  u32  info_vmexit_interrupt_information;
  u32  info_vmexit_interrupt_error_code;
  u32  info_idt_vectoring_information;
  u32  info_idt_vectoring_error_code;
  u32  info_vmexit_instruction_length;
  u32  info_vmx_instruction_information;
  u64  info_exit_qualification;
  u64  info_io_rcx;
  u64  info_io_rsi;
  u64  info_io_rdi;
  u64  info_io_rip;
  u64  info_guest_linear_address;
  u64  info_guest_paddr_full;
} xc_hypapp_arch_param_x86vmx_cpustate_inforegs_t;


typedef struct {
	u32 operation;
	union {
		struct regs cpugprs;
		xc_hypapp_arch_param_x86vmx_cbtrapio_t cbtrapio;
		xc_hypapp_arch_param_x86vmx_trapio_t trapio;
		xc_hypapp_arch_param_x86vmx_cpustate_desc_t desc;
		xc_hypapp_arch_param_x86vmx_cpustate_activity_t activity;
		xc_hypapp_arch_param_x86vmx_cpustate_controlregs_t controlregs;
		xc_hypapp_arch_param_x86vmx_cpustate_inforegs_t inforegs;
		xc_hypapp_arch_param_x86vmx_cpustate_sysenter_t sysenter;
	} param;
} __attribute__ ((packed)) xc_hypapp_arch_param_t;

typedef struct {
  u8 vmx_vmxon_region[PAGE_SIZE_4K] __attribute__((aligned(4096)));
  u8 vmx_vmcs_region[PAGE_SIZE_4K] __attribute__((aligned(4096)));
  u8 vmx_msr_area_host_region[2*PAGE_SIZE_4K] __attribute__((aligned(4096)));
  u8 vmx_msr_area_guest_region[2*PAGE_SIZE_4K] __attribute__((aligned(4096)));
  u64 vmx_msrs[IA32_VMX_MSRCOUNT];
  u64 vmx_msr_efer;
  u64 vmx_msr_efcr;
} __attribute__((packed)) xc_cpuarchdata_x86vmx_t;


typedef struct {
  u8 vmx_ept_pml4_table[PAGE_SIZE_4K];												//PML4 table
  u8 vmx_ept_pdp_table[PAGE_SIZE_4K];												//PDP table
  u8 vmx_ept_pd_tables[PAGE_SIZE_4K * PAE_PTRS_PER_PDPT];					//PD tables
  u8 vmx_ept_p_tables[PAGE_SIZE_4K * PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT];	//P tables
} __attribute__ ((packed)) xc_partition_hptdata_x86vmx_t;

typedef struct {
  u8 vmx_iobitmap_region[2*PAGE_SIZE_4K];		//I/O Bitmap area
  u8 vmx_msrbitmaps_region[PAGE_SIZE_4K];		//MSR bitmap area
} __attribute__ ((packed)) xc_partition_trapmaskdata_x86vmx_t;

#define XC_HYPAPP_ARCH_PARAM_OPERATION_CBTRAP_IO		(0x101)



#define XC_HYPAPP_ARCH_PARAM_OPERATION_TRAP_IO			(0xC01)


#define XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS		(0xD01)
#define XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_DESC		(0xD02)
#define XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY	(0xD03)
#define XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS	(0xD04)
#define XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_INFOREGS	(0xD05)
#define XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_SYSENTER	(0xD06)

//------------------------------------------------------
// functions
//------------------------------------------------------

//initialize CPU state
void xmhf_baseplatform_arch_x86vmx_cpuinitialize(void);

//wake up application processors (cores) in the system
void xmhf_baseplatform_arch_x86vmx_wakeupAPs(void);

//allocate and setup VCPU structure for all the CPUs
void xmhf_baseplatform_arch_x86vmx_allocandsetupvcpus(u32 cpu_vendor);

//--debug: dumpVMCS dumps VMCS contents
//void xmhf_baseplatform_arch_x86vmx_dumpVMCS(VCPU *vcpu);

void xmhf_memprot_arch_x86vmx_flushmappings(void); //flush hardware page table mappings (TLB)
u64 xmhf_memprot_arch_x86vmx_get_EPTP(void); // get or set EPTP (only valid on Intel)
void xmhf_memprot_arch_x86vmx_set_EPTP(u64 eptp);

void xmhf_parteventhub_arch_x86vmx_entry(void);




#endif //__ASSEMBLY__

#endif // #define _XMHF_X86_VMX_X86PC_H_

