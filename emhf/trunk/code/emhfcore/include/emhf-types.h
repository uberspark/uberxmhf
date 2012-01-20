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

//types.h - base types
#ifndef __EMHF_TYPES_H_
#define __EMHF_TYPES_H_


#ifndef __ASSEMBLY__

typedef u32 	paddr_t;		//physical address
typedef void* 	hva_t; 			//hypervisor virtual address 
typedef u64 	spa_t; 			//system physical address 
typedef u32 	gva_t; 			//guest virtual address. we only support 32-bit guests 
typedef u64 	gpa_t; 			//guest physical address. can be 64-bit with PAE 


//----------------------------------------------------------------------
//the master-id table, which is used by the AP bootstrap code
//to locate its own vcpu structure
//NOTE: The size of this structure _MUST_ be _EXACTLY_EQUAL_ to 8 bytes
//as it is made use of in low-level assembly language stubs
typedef struct _midtab {
  u32 cpu_lapic_id;       //CPU LAPIC id (unique)
  u32 vcpu_vaddr_ptr;     //virt. addr. pointer to vcpu struct for this CPU
} __attribute__((packed)) MIDTAB;

#define SIZE_STRUCT_MIDTAB  (sizeof(struct _midtab))


//---platform
//MTRR memory type structure
struct _memorytype {
  u64 startaddr;
  u64 endaddr;
  u32 type;
  u32 invalid;
  u32 reserved[6];
} __attribute__((packed));

//---platform
#define MAX_MEMORYTYPE_ENTRIES    96    //8*11 fixed MTRRs and 8 variable MTRRs
#define MAX_FIXED_MEMORYTYPE_ENTRIES  88
#define MAX_VARIABLE_MEMORYTYPE_ENTRIES 8

//---platform
//total number of FIXED and VARIABLE MTRRs on current x86 platforms
#define NUM_MTRR_MSRS		29

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
  u32 sipi_page_vaddr;    //SIPI page of the CPU used for SIPI handling
  u32 id;                 //LAPIC id of the core
  u32 idx;                //this vcpu's index in the g_vcpubuffers array
  u32 sipivector;         //SIPI vector 
  u32 sipireceived;       //SIPI received indicator, 1 if yes
  u32 nmiinhvm;           //this is 1 if there was a NMI when in HVM, else 0        
	u32 cpu_vendor;					//Intel or AMD
	u32 isbsp;							//1 if this core is BSP else 0
	
  //SVM specific fields
  u32 hsave_vaddr_ptr;    //VM_HSAVE area of the CPU
  u32 vmcb_vaddr_ptr;     //VMCB of the CPU
  u32 npt_vaddr_ptr;      //NPT base of the CPU
  u32 npt_vaddr_pdts;      
  u32 npt_asid;           //NPT ASID for this core
  u32 npt_vaddr_pts;      //NPT page-tables for protection manipulation

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
  u32 vmx_guest_currentstate;		//current operating mode of guest
  u32 vmx_guest_nextstate;		  //next operating mode of guest
	u32 vmx_guest_unrestricted;		//this is 1 if the CPU VMX implementation supports unrestricted guest execution
  struct _vmx_vmcsfields vmcs;   //the VMCS fields
} __attribute__((packed)) VCPU;

#define SIZE_STRUCT_VCPU    (sizeof(struct _vcpu))
#define CPU_VENDOR (g_vcpubuffers[0].cpu_vendor)



//NOTE: The declaration here _MUST_ match definition of RPB in runtimesup.S	
typedef struct {
	u32 magic;
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
	u32 RtmSVMDevBitmapBase;
	u32 RtmVMXVTdPdpt;
	u32 RtmVMXVTdPdts;
	u32 RtmVMXVTdPts;
	u32 RtmVMXVTdRET;
	u32 RtmVMXVTdCET;
    uart_config_t uart_config;	        /* runtime options parsed in init and passed forward */
	u32 isEarlyInit;					//1 for an "early init" else 0 (late-init)
} __attribute__((packed)) RPB, *PRPB;


//----------------------------------------------------------------------
// EMHF application related declarations
//----------------------------------------------------------------------

//generic catch-all app return codes
#define APP_SUCCESS     (0x1)
#define APP_ERROR				(0x0)

//application parameter block
//for now it holds the bootsector and optional module info loaded by GRUB
//eventually this will be generic enough for both boot-time and dynamic loading
//capabilities
typedef struct {
  u32 bootsector_ptr;
  u32 bootsector_size;
  u32 optionalmodule_ptr;
  u32 optionalmodule_size;
  u32 runtimephysmembase;
} __attribute__((packed)) APP_PARAM_BLOCK;

//EMHF application callbacks
extern u32 emhf_app_main(VCPU *vcpu, APP_PARAM_BLOCK *apb);
extern u32 emhf_app_handleintercept_portaccess(VCPU *vcpu, struct regs *r, u32 portnum, u32 access_type, u32 access_size); 
extern u32 emhf_app_handleintercept_hwpgtblviolation(VCPU *vcpu,
      struct regs *r,
      u64 gpa, u64 gva, u64 violationcode);
extern void emhf_app_handleshutdown(VCPU *vcpu, struct regs *r);
extern u32 emhf_app_handlehypercall(VCPU *vcpu, struct regs *r);	//returns APP_SUCCESS if handled, else APP_ERROR      


#endif /*ifndef __ASSEMBLY__*/

#endif /* __EMHF_TYPES_H_ */
