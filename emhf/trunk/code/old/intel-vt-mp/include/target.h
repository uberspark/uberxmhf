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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

//target.h - sechyp target declarations
//author: amit vasudevan (amitvasudevan@acm.org)
#ifndef __TARGET_H_
#define __TARGET_H_

//---includes for the target----------------------------------------------------
#include <types.h>      //always comes first
#include <print.h>      //early chance to disable/enable debug printfs
#include <error.h>      //error handling and assertions

#include <processor.h>  //CPU
#include <msr.h>        //model specific registers
#include <paging.h>     //MMU
#include <io.h>         //legacy I/O
#include <apic.h>       //APIC
//#include <svm.h>        //SVM extensions
#include <vtx.h>        //VT extensions

#include <pci.h>        //PCI bus glue


//language specifics
#include <sarg.h>
#include <str.h>
#include <div64.h>

//boot manager (multiboot)
#include <multiboot.h>
//------------------------------------------------------------------------------

//runtime base address (virtual)
#define __TARGET_BASE	0xC0000000

//guest boot record is always loaded at 0000:7C00
#define __GUESTOSBOOTMODULE_BASE	0x7c00

#define __CS 0x0008     //code segment selector
#define __DS 0x0010     //data segment selector
#define __TRSEL 0x0018  //selector for TSS


#define MAX_E820_ENTRIES    (64)  //maximum E820 entries we support, 64 should
                                  //be enough
#define MAX_PCPU_ENTRIES  (4)
#define MPFP_SIGNATURE (0x5F504D5FUL) //"_MP_"
#define MPCONFTABLE_SIGNATURE (0x504D4350UL)  //"PCMP"
#define MAX_MIDTAB_ENTRIES  (MAX_PCPU_ENTRIES)
#define AP_BOOTSTRAP_CODE_SEG 0x1000
#define RUNTIME_STACK_SIZE  (16384)     //16K stack for each core
#define MAX_VCPU_ENTRIES    (MAX_PCPU_ENTRIES)
#define RUNTIME_TSS_SIZE    (4096)

#ifdef __NESTED_PAGING__
#define ASID_GUEST_KERNEL 2
#endif

//VT MSR indices for the vcpu structure
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
#ifdef __NESTED_PAGING__
  #define INDEX_IA32_VMX_PROCBASED_CTLS2_MSR  0xB
#endif

#ifdef __NESTED_PAGING__
  #define IA32_VMX_MSRCOUNT   12
#else
  #define IA32_VMX_MSRCOUNT   11
#endif

#define LIMBO_GDT_SIZE	0x2000
#define LIMBO_TSS_SIZE	0x1000

//sechyp app constant definitions
#define APP_IOINTERCEPT_CHAIN   0xA0
#define APP_IOINTERCEPT_SKIP    0xA1
#define APP_INIT_SUCCESS        0x0
#define APP_INIT_FAIL           0xFF

#ifndef __ASSEMBLY__

    

extern u32 __limbo_gdt[];
extern u32 __limbo_tss[];
extern u32 limbo_rsp;


#define SIZE_STRUCT_GRUBE820  (sizeof(GRUBE820))
#define SIZE_STRUCT_PCPU      (sizeof(PCPU))
#define SIZE_STRUCT_MIDTAB    (sizeof(MIDTAB))
#define SIZE_STRUCT_VCPU      (sizeof(VCPU))

//same privilege level exception/interrupt stack frame
typedef struct {
  u32 eip;
  u32 cs;
  u32 eflags;
} __attribute__((packed)) INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE;

typedef struct {
  u32 errorcode;
  u32 eip;
  u32 cs;
  u32 eflags;
} __attribute__((packed)) INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE;


//the master-id table, which is used by the AP bootstrap code
//to locate its own vcpu structure
//this structure __MUST__ be 8 bytes
typedef struct {
  u32 cpu_lapic_id;       //CPU LAPIC id (unique)
  u32 vcpu_vaddr_ptr;     //virt. addr. pointer to vcpu struct for this CPU
} __attribute__((packed)) MIDTAB;


#define	GSTATE_DEAD									(0)
#define GSTATE_REALMODE							(1UL << 0)
#define GSTATE_PROTECTEDMODE				(1UL << 1)
#define GSTATE_PROTECTEDMODE_TR			(1UL << 2)
#define GSTATE_PROTECTEDMODE_GDTR		(1UL << 3)
#define GSTATE_PROTECTEDMODE_IDTR		(1UL << 4)
#define GSTATE_PROTECTEDMODE_PG			(1UL << 5)

//VMX VMCS fields
struct vmcsfields {
#if defined(__NESTED_PAGING__)
	//16-bit control fields
	unsigned int control_vpid;
#endif
  // Natural 32-bit Control fields
  unsigned int  control_VMX_pin_based;
  unsigned int  control_VMX_cpu_based;
#if defined(__NESTED_PAGING__)
	unsigned int  control_VMX_seccpu_based;
#endif
  unsigned int  control_exception_bitmap;
  unsigned int  control_pagefault_errorcode_mask; 
  unsigned int  control_pagefault_errorcode_match; 
  unsigned int  control_CR3_target_count;
  unsigned int  control_VM_exit_controls;
  unsigned int  control_VM_exit_MSR_store_count;
  unsigned int  control_VM_exit_MSR_load_count;
  unsigned int  control_VM_entry_controls;
  unsigned int  control_VM_entry_MSR_load_count;
  unsigned int  control_VM_entry_interruption_information;
  unsigned int  control_VM_entry_exception_errorcode;
  unsigned int  control_VM_entry_instruction_length;
  unsigned int  control_Task_PRivilege_Threshold;
  // Natural 64-bit Control fields
  unsigned long long  control_CR0_mask;
  unsigned long long  control_CR4_mask;
  unsigned long long  control_CR0_shadow;
  unsigned long long  control_CR4_shadow;
  unsigned long long  control_CR3_target0;
  unsigned long long  control_CR3_target1;
  unsigned long long  control_CR3_target2;
  unsigned long long  control_CR3_target3;
  // Full 64-bit Control fields
  unsigned int  control_IO_BitmapA_address_full;
  unsigned int  control_IO_BitmapA_address_high;
  unsigned int  control_IO_BitmapB_address_full;
  unsigned int  control_IO_BitmapB_address_high;
  unsigned int  control_MSR_Bitmaps_address_full;
  unsigned int  control_MSR_Bitmaps_address_high;
  unsigned int  control_VM_exit_MSR_store_address_full;
  unsigned int  control_VM_exit_MSR_store_address_high;
  unsigned int  control_VM_exit_MSR_load_address_full;
  unsigned int  control_VM_exit_MSR_load_address_high;
  unsigned int  control_VM_entry_MSR_load_address_full;
  unsigned int  control_VM_entry_MSR_load_address_high;
  unsigned int  control_Executive_VMCS_pointer_full;
  unsigned int  control_Executive_VMCS_pointer_high;
  unsigned int  control_TSC_offset_full;
  unsigned int  control_TSC_offset_high;
  unsigned int  control_virtual_APIC_page_address_full;
  unsigned int  control_virtual_APIC_page_address_high;
#if defined(__NESTED_PAGING__)
	unsigned int control_EPT_pointer_full; 
	unsigned int control_EPT_pointer_high;
#endif
  // Natural 64-bit Host-State fields
  unsigned long long  host_CR0;
  unsigned long long  host_CR3;
  unsigned long long  host_CR4;
  unsigned long long  host_FS_base;
  unsigned long long  host_GS_base;
  unsigned long long  host_TR_base;
  unsigned long long  host_GDTR_base;
  unsigned long long  host_IDTR_base;
  unsigned long long  host_SYSENTER_ESP;
  unsigned long long  host_SYSENTER_EIP;
  unsigned long long  host_RSP;
  unsigned long long  host_RIP;
  // Natural 32-bit Host-State fields
  unsigned int  host_SYSENTER_CS;
  // Natural 16-bit Host-State fields
  unsigned int  host_ES_selector;
  unsigned int  host_CS_selector;
  unsigned int  host_SS_selector;
  unsigned int  host_DS_selector;
  unsigned int  host_FS_selector;
  unsigned int  host_GS_selector;
  unsigned int  host_TR_selector;
  // Natural 64-bit Guest-State fields
  unsigned long long  guest_CR0;
  unsigned long long  guest_CR3;
  unsigned long long  guest_CR4;
  unsigned long long  guest_ES_base;
  unsigned long long  guest_CS_base; 
  unsigned long long  guest_SS_base;
  unsigned long long  guest_DS_base;
  unsigned long long  guest_FS_base;
  unsigned long long  guest_GS_base;
  unsigned long long  guest_LDTR_base;
  unsigned long long  guest_TR_base;
  unsigned long long  guest_GDTR_base;
  unsigned long long  guest_IDTR_base;
  unsigned long long  guest_DR7;
  unsigned long long  guest_RSP; 
  unsigned long long  guest_RIP; 
  unsigned long long  guest_RFLAGS; 
  unsigned long long  guest_pending_debug_x;
  unsigned long long  guest_SYSENTER_ESP;
  unsigned long long  guest_SYSENTER_EIP;
  // Natural 32-bit Guest-State fields
  unsigned int  guest_ES_limit;
  unsigned int  guest_CS_limit;
  unsigned int  guest_SS_limit;
  unsigned int  guest_DS_limit;
  unsigned int  guest_FS_limit;
  unsigned int  guest_GS_limit;
  unsigned int  guest_LDTR_limit; 
  unsigned int  guest_TR_limit;
  unsigned int  guest_GDTR_limit;
  unsigned int  guest_IDTR_limit;
  unsigned int  guest_ES_access_rights; 
  unsigned int  guest_CS_access_rights;
  unsigned int  guest_SS_access_rights;
  unsigned int  guest_DS_access_rights;
  unsigned int  guest_FS_access_rights;
  unsigned int  guest_GS_access_rights;
  unsigned int  guest_LDTR_access_rights;
  unsigned int  guest_TR_access_rights;
  unsigned int  guest_interruptibility; 
  unsigned int  guest_activity_state; 
  unsigned int  guest_SMBASE;	
  unsigned int  guest_SYSENTER_CS; 
  // Natural 16-bit Guest-State fields
  unsigned int  guest_ES_selector;
  unsigned int  guest_CS_selector;
  unsigned int  guest_SS_selector;
  unsigned int  guest_DS_selector;
  unsigned int  guest_FS_selector;
  unsigned int  guest_GS_selector;
  unsigned int  guest_LDTR_selector;
  unsigned int  guest_TR_selector;
  // Full 64-bit Guest-State fields
  unsigned int  guest_VMCS_link_pointer_full;
  unsigned int  guest_VMCS_link_pointer_high;
  unsigned int  guest_IA32_DEBUGCTL_full;
  unsigned int  guest_IA32_DEBUGCTL_high;
  #if defined(__NESTED_PAGING__)
    unsigned int 	guest_paddr_full;
    unsigned int 	guest_paddr_high;
    unsigned int  guest_PDPTE0_full; 
	  unsigned int  guest_PDPTE0_high;
    unsigned int  guest_PDPTE1_full; 
	  unsigned int  guest_PDPTE1_high;
    unsigned int  guest_PDPTE2_full; 
	  unsigned int  guest_PDPTE2_high;
    unsigned int  guest_PDPTE3_full; 
	  unsigned int  guest_PDPTE3_high;
  #endif
  //Read-Only Fields
  unsigned int  info_vminstr_error;
  unsigned int  info_vmexit_reason;
  unsigned int  info_vmexit_interrupt_information;
  unsigned int  info_vmexit_interrupt_error_code;
  unsigned int  info_IDT_vectoring_information;
  unsigned int  info_IDT_vectoring_error_code;
  unsigned int  info_vmexit_instruction_length;
  unsigned int  info_vmx_instruction_information;
  unsigned long long  info_exit_qualification;
  unsigned long long  info_IO_RCX;
  unsigned long long  info_IO_RSI;
  unsigned long long  info_IO_RDI;
  unsigned long long  info_IO_RIP;
  unsigned long long  info_guest_linear_address;
} __attribute__((packed));

//the vcpu structure which holds the current state of a core
typedef struct {
  u32 esp;                //used to establish stack for the CPU
  u32 id;                 //LAPIC id of the core
  u32 sipivector;         //SIPI vector 
  u32 sipireceived;       //SIPI received indicator, 1 if yes
  u32 nmiinhvm;           //this is 1 if there was a NMI when in HVM, else 0        
  u64 vmx_msrs[IA32_VMX_MSRCOUNT];  //VMX msr values
  u64 msr_efer;
  u64 msr_efcr;
  u32 vmxonregion_vaddr;    //virtual address of the vmxon region
  u32 vmcs_vaddr;           //virtual address of the VMCS region
  
  //guest state fields
  u32 guest_currentstate;		//current operating mode of guest
  u32 guest_nextstate;		  //next operating mode of guest
  struct vmcsfields vmcs;   //the VMCS fields
} __attribute__((packed)) VCPU;

typedef struct {
  u32 signature;
  u32 paddrpointer;
  u8 length;
  u8 spec_rev;
  u8 checksum;
  u8 mpfeatureinfo1;
  u8 mpfeatureinfo2;
  u8 mpfeatureinfo3;
  u8 mpfeatureinfo4;
  u8 mpfeatureinfo5;
} __attribute__ ((packed)) MPFP;


typedef struct{
  u32 signature;
  u16 length;
  u8 spec_rev;
  u8 checksum;
  u8 oemid[8];
  u8 productid[12];
  u32 oemtableptr;
  u16 oemtablesize;
  u16 entrycount;
  u32 lapicaddr;
  u16 exttablelength;
  u16 exttablechecksum;
} __attribute__ ((packed)) MPCONFTABLE;

typedef struct {
  u8 entrytype;
  u8 lapicid;
  u8 lapicver;
  u8 cpuflags;
  u32 cpusig;
  u32 featureflags;
  u32 res0;
  u32 res1;
} __attribute__ ((packed)) MPENTRYCPU;




typedef struct {
  u32 lapic_id;
  u32 lapic_ver;
  u32 lapic_base;
  u32 isbsp;
} __attribute__((packed)) PCPU;


#define __pa(x) (x)

#define __hva2spa__(x) ((x) - __TARGET_BASE + lpb->XtVmmRuntimePhysBase)
#define __spa2hva__(x) ((x) + __TARGET_BASE - lpb->XtVmmRuntimePhysBase)


typedef struct {
  u32 baseaddr_low;
  u32 baseaddr_high;
  u32 length_low;
  u32 length_high;
  u32 type;  
} __attribute__((packed)) GRUBE820;



typedef struct {
	u32 XtVmmEntryPoint;
	u32 XtVmmPdptBase;
	u32 XtVmmPdtsBase;
	u32 XtVmmNpdtBase;
	u32 XtVmmNestedNpdtBase;
	u32 XtGuestOSBootModuleBase;
	u32 XtGuestOSBootModuleSize;
	u32 XtGuestOSBootModuleBaseSup1;
	u32 XtGuestOSBootModuleSizeSup1;
	u32 XtVmmStackBase;
	u32 XtVmmStackSize;
	u32 XtVmmGdt;
	u32 XtVmmNetworkAdapterStructureBase;
	u32 XtVmmHsaveBase;
	u32 XtVmmVMCBBase;
	u32 XtVmmIopmBase;
	u32 XtVmmNestedPdptBase;
	u32 XtVmmNestedPdtsBase;
	u32 XtVmmNestedPtsBase;
	u32 XtVmmIdt;
	u32 XtVmmIdtFunctionPointers;
	u32 XtVmmIdtEntries;
	u32 XtVmmE1000DescBase;
	u32 XtVmmE1000HeaderBase;
	u32 XtVmmE1000BodyBase;
	u32 XtVmmRuntimePhysBase;
	u32 XtVmmRuntimeVirtBase;
	u32 XtVmmRuntimeSize;
	u32 XtVmmE820Buffer;
	u32 XtVmmE820NumEntries;
	u32 XtVmmMPCpuinfoBuffer;
	u32 XtVmmMPCpuinfoNumEntries;
	u32 XtVmmTSSBase;
} __attribute__((packed)) XTLPB, *PXTLPB;

extern PXTLPB	lpb;

#include <v86monitor.h> //VT V86 monitor
#include <hardware_paging.h>  //VT EPT support
#include <libsechyp.h> //the SecHyp interface library


//sechyp app interface declarations
extern u32 sechyp_app_main(VCPU *vcpu);
extern u32 sechyp_app_handleintercept_portaccess(VCPU *vcpu, struct regs *r, u32 portnum, u32 access_type, u32 access_size); 


#endif

#endif /* __TARGET_H_ */
