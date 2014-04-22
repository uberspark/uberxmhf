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

// xc-x86.h - XMHF core x86 arch. main header file 
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef _XC_X86_H_
#define _XC_X86_H_

#include <xmhf.h>
#include <xmhf-core.h>

//xc-baseplatform
#include "platform/x86pc/include/common/_multiboot.h"		//multiboot
#include "cpu/x86/include/common/_processor.h"  	//CPU
#include "cpu/x86/include/common/_msr.h"        	//model specific registers
#include "cpu/x86/include/common/_paging.h"     	//MMU
#include "cpu/x86/include/common/_io.h"         	//legacy I/O
#include "cpu/x86/include/common/_apic.h"       	//APIC
#include "cpu/x86/include/intel/vmx/_vmx.h"			//VMX extensions
#include "cpu/x86/include/intel/txt/_txt.h"			//Trusted eXecution Technology (SENTER support)
#include "platform/x86pc/include/common/_pci.h"        	//PCI bus glue
#include "platform/x86pc/include/common/_acpi.h"			//ACPI glue
#include "platform/x86pc/include/intel/vtd/vtd.h"		//VMX DMA protection
#include "platform/x86pc/include/common/_memaccess.h"	//platform memory access


#ifndef __ASSEMBLY__


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



//x86 GDT descriptor type
typedef struct {
		u16 size;
		u32 base;
} __attribute__((packed)) arch_x86_gdtdesc_t;

//x86 IDT descriptor type
typedef struct {
		u16 size;
		u32 base;
} __attribute__((packed)) arch_x86_idtdesc_t;

//TSS descriptor (partial)
typedef struct __tss {
	u32 prevlink;
	u32 esp0;
	u32 ss0;
} tss_t;

#define	EMHF_XCPHANDLER_MAXEXCEPTIONS	32
#define EMHF_XCPHANDLER_IDTSIZE			(EMHF_XCPHANDLER_MAXEXCEPTIONS * 8)


//----------------------------------------------------------------------
// function decls.
//----------------------------------------------------------------------


void _ap_pmode_entry_with_paging(void);

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

void xmhf_baseplatform_arch_x86_cpuinitialize(void);

//return 1 if the calling CPU is the BSP
u32 xmhf_baseplatform_arch_x86_isbsp(void);

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

u32 xmhf_baseplatform_arch_x86_getgdtbase(void);
u32 xmhf_baseplatform_arch_x86_getidtbase(void);
u32 xmhf_baseplatform_arch_x86_gettssbase(void);


#endif //__ASSEMBLY__

#endif // _XC_X86_H_
