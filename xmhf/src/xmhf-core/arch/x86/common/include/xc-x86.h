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
//structure which holds values of guest MTRRs (64-bit)
struct _guestmtrrmsrs {
	u32 lodword;
	u32 hidword;
} __attribute__((packed));


//---platform
//VMX MSR indices for the vcpu structure
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


//the vcpu structure which holds the current state of a core
typedef struct _vcpu {
  //common fields	
  u32 esp;                //used to establish stack for the CPU
  //u32 sipi_page_vaddr;    //SIPI page of the CPU used for SIPI handling
  u32 id;                 //LAPIC id of the core
  u32 idx;                //this vcpu's index in the g_vcpubuffers array
  //u32 sipivector;         //SIPI vector 
  //u32 sipireceived;       //SIPI received indicator, 1 if yes
  //u32 nmiinhvm;           //this is 1 if there was a NMI when in HVM, else 0        
	u32 cpu_vendor;					//Intel or AMD
	u32 isbsp;							//1 if this core is BSP else 0
  u32 quiesced;				//1 if this core is currently quiesced
	
  //VMX specific fields
  u64 vmx_msrs[IA32_VMX_MSRCOUNT];  //VMX msr values
  u64 vmx_msr_efer;
  u64 vmx_msr_efcr;
  u32 vmx_vmxonregion_vaddr;    //virtual address of the vmxon region
  u32 vmx_vmcs_vaddr;           //virtual address of the VMCS region
  
  u32 vmx_vaddr_iobitmap;		//virtual address of the I/O Bitmap area
  u32 vmx_vaddr_msr_area_host;		//virtual address of the host MSR area
  u32 vmx_vaddr_msr_area_guest;		//virtual address of the guest MSR area
  u32 vmx_vaddr_msrbitmaps;				//virtual address of the MSR bitmap area
  
  u32 vmx_vaddr_ept_pml4_table;	//virtual address of EPT PML4 table
  u32 vmx_vaddr_ept_pdp_table;	//virtual address of EPT PDP table
  u32 vmx_vaddr_ept_pd_tables;	//virtual address of base of EPT PD tables
  u32 vmx_vaddr_ept_p_tables;		//virtual address of base of EPT P tables
  struct _memorytype vmx_ept_memorytypes[MAX_MEMORYTYPE_ENTRIES]; //EPT memory types array
  //guest MTRR shadow MSRs
	struct _guestmtrrmsrs vmx_guestmtrrmsrs[NUM_MTRR_MSRS];

  //guest state fields
  //u32 vmx_guest_currentstate;		//current operating mode of guest
  //u32 vmx_guest_nextstate;		  //next operating mode of guest
	u32 vmx_guest_unrestricted;		//this is 1 if the CPU VMX implementation supports unrestricted guest execution
  //struct _vmx_vmcsfields vmcs;   //the VMCS fields

} __attribute__((packed)) VCPU;

#define SIZE_STRUCT_VCPU    (sizeof(struct _vcpu))
#define CPU_VENDOR (g_vcpubuffers[0].cpu_vendor)


//VCPU structure for each "guest OS" core
//extern VCPU g_vcpubuffers[] __attribute__(( section(".data") ));
extern VCPU g_bplt_vcpu[] __attribute__(( section(".data") ));

//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------

//get CPU vendor
u32 xmhf_baseplatform_arch_getcpuvendor(void);

//initialize CPU state
void xmhf_baseplatform_arch_cpuinitialize(void);

//initialize SMP
void xmhf_baseplatform_arch_smpinitialize(void);

//initialize basic platform elements
void xmhf_baseplatform_arch_initialize(void);

//reboot platform
void xmhf_baseplatform_arch_reboot(context_desc_t context_desc);

//returns true if CPU has support for XSAVE/XRSTOR
bool xmhf_baseplatform_arch_x86_cpuhasxsavefeature(void);




//----------------------------------------------------------------------
//x86 ARCH. INTERFACES
//----------------------------------------------------------------------
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


//core GDT
extern arch_x86_gdtdesc_t x_gdt;

//runtime TSS
//extern u8 g_runtime_TSS[PAGE_SIZE_4K] __attribute__(( section(".data") ));

//signal that basic base platform data structure initialization is complete 
//(used by the exception handler component)
extern bool g_bplt_initiatialized __attribute__(( section(".data") ));


//----------------------------------------------------------------------

extern void _ap_pmode_entry_with_paging(void);

/*
//this is the start of the real-mode AP bootstrap code (bplt-x86-smptrampoline.S)
extern u32 _ap_bootstrap_start[];

//this is the end of the real-mode AP bootstrap code (bplt-x86-smptrampoline.S)
extern u32 _ap_bootstrap_end[];

//the CR3 value to be loaded by the AP boot-strap code is placed in this
//variable by the runtime before waking up the APs (bplt-x86-smptrampoline.S)
extern u32 _ap_cr3_value;

//the CR4 value to be loaded by the AP boot-strap code is placed in this
//variable by the runtime before waking up the APs (bplt-x86-smptrampoline.S)
extern u32 _ap_cr4_value;


extern u32 _ap_runtime_entrypoint;


extern u8 _ap_bootstrap_blob[256];

extern u32 * _ap_bootstrap_blob_cr3;

extern u32 * _ap_bootstrap_blob_cr4;

extern u32 * _ap_bootstrap_blob_runtime_entrypoint;

extern u8 * _ap_bootstrap_blob_mle_join_start;
*/

//core PAE page tables
//extern u8 x_3level_pdpt[];
//extern u8 x_3level_pdt[];


//----------------------------------------------------------------------

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

static inline u64 VCPU_gdtr_base(VCPU *vcpu)
{
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_GDTR_base;
}

static inline size_t VCPU_gdtr_limit(VCPU *vcpu)
{
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_GDTR_limit;
}

static inline u64 VCPU_grflags(VCPU *vcpu)
{
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RFLAGS;
}

static inline void VCPU_grflags_set(VCPU *vcpu, u64 val)
{
    ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RFLAGS = val;
}

static inline u64 VCPU_grip(VCPU *vcpu)
{
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RIP;
}

static inline void VCPU_grip_set(VCPU *vcpu, u64 val)
{
    ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RIP = val;
}

static inline u64 VCPU_grsp(VCPU *vcpu)
{
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RSP;
}

static inline void VCPU_grsp_set(VCPU *vcpu, u64 val)
{
    ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RSP = val;
}

static inline u64 VCPU_gcr3(VCPU *vcpu)
{
    return vcpu->vmcs.guest_CR3;
}

static inline void VCPU_gcr3_set(VCPU *vcpu, u64 cr3)
{
    vcpu->vmcs.guest_CR3 = cr3;
}

static inline u64 VCPU_gcr4(VCPU *vcpu)
{
    return vcpu->vmcs.guest_CR4;
}

//xc-xcphandler

#define	EMHF_XCPHANDLER_MAXEXCEPTIONS	32
#define EMHF_XCPHANDLER_IDTSIZE			(EMHF_XCPHANDLER_MAXEXCEPTIONS * 8)

//----------------------------------------------------------------------
//exported DATA 

//core IDT
//extern u64 xmhf_xcphandler_idt_start[];

//core IDT descriptor
//extern arch_x86_idtdesc_t xmhf_xcphandler_idt;

//array of exception handler stubs
extern u8 xmhf_xcphandler_exceptionstubs[]; 

//IDT descriptor
//extern arch_x86_idtdesc_t xmhf_xcphandler_idt;

//start of interrupt descriptor table 
//extern u8 xmhf_xcphandler_idt_start[];

//EMHF exception handler hub
void xmhf_xcphandler_hub(u32 vector, struct regs *r);

//EMHF exception handler hub
void xmhf_xcphandler_arch_hub(u32 vector, struct regs *r);



//xc-richguest

//----------------------------------------------------------------------
//rich guest memory functions

static inline bool xmhf_smpguest_readu16(context_desc_t context_desc, const void *guestaddress, u16 *valueptr){
		u16 *tmp = (u16 *)xmhf_smpguest_arch_walk_pagetables(context_desc, guestaddress);
		if((u32)tmp == 0xFFFFFFFFUL || valueptr == NULL)
			return false;
		*valueptr = xmhfhw_sysmemaccess_readu16((u32)tmp);
		return true;
}

static inline bool xmhf_smpguest_writeu16(context_desc_t context_desc, const void *guestaddress, u16 value){
		u16 *tmp = (u16 *)xmhf_smpguest_arch_walk_pagetables(context_desc, guestaddress);
		if((u32)tmp == 0xFFFFFFFFUL || 
			( ((u32)tmp >= xcbootinfo->physmem_base) && ((u32)tmp <= (xcbootinfo->physmem_base+xcbootinfo->size)) ) 
		  )
			return false;
		xmhfhw_sysmemaccess_writeu16((u32)tmp, value);
		return true;
}

static inline bool xmhf_smpguest_memcpyfrom(context_desc_t context_desc, void *buffer, const void *guestaddress, size_t numbytes){
	u8 *guestbuffer = (u8 *)xmhf_smpguest_arch_walk_pagetables(context_desc, guestaddress);
	if((u32)guestbuffer == 0xFFFFFFFFUL)
		return false;
	xmhfhw_sysmemaccess_copy(buffer, gpa2hva(guestbuffer), numbytes);
}

static inline bool xmhf_smpguest_memcpyto(context_desc_t context_desc, void *guestaddress, const void *buffer, size_t numbytes){
	u8 *guestbuffer = (u8 *)xmhf_smpguest_arch_walk_pagetables(context_desc, guestaddress);
	if((u32)guestbuffer == 0xFFFFFFFFUL || 
		( ((u32)guestbuffer >= xcbootinfo->physmem_base) && ((u32)guestbuffer <= (xcbootinfo->physmem_base+xcbootinfo->size)) ) 
	  )
		return false;
	xmhfhw_sysmemaccess_copy(gpa2hva(guestbuffer), buffer, numbytes);
}

//quiesce interface to switch all guest cores into hypervisor mode
void xmhf_smpguest_arch_quiesce(VCPU *vcpu);

//endquiesce interface to resume all guest cores after a quiesce
void xmhf_smpguest_arch_endquiesce(VCPU *vcpu);

//quiescing handler for #NMI (non-maskable interrupt) exception event
void xmhf_smpguest_arch_eventhandler_nmiexception(struct regs *r);

/*
//xc-apihub
// hypapp PAE page tables
extern u64 hypapp_3level_pdpt[] __attribute__(( section(".palign_data") ));
extern u64 hypapp_3level_pdt[] __attribute__(( section(".palign_data") ));

//core PAE page tables
extern u64 core_3level_pdpt[] __attribute__(( section(".palign_data") ));
extern u64 core_3level_pdt[] __attribute__(( section(".palign_data") ));

//core and hypapp page table base address (PTBA)
extern u32 core_ptba;
extern u32 hypapp_ptba;
*/

#endif //__ASSEMBLY__

#endif // _XC_X86_H_
