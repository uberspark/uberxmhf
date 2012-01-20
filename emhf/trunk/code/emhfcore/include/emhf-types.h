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


//runtime base address (virtual)
#define __TARGET_BASE	0xC0000000

//"sl" parameter block magic value
#define SL_PARAMETER_BLOCK_MAGIC	0xDEADBEEF

//"runtime" parameter block magic value
#define RUNTIME_PARAMETER_BLOCK_MAGIC	0xF00DDEAD

//16K stack for each core during runtime
#define RUNTIME_STACK_SIZE  (16384)     

//8K stack for each core in "init"
#define INIT_STACK_SIZE	(8192)					

//----------------------------------------------------------------------
//XXX: to sort

//preferred TPM locality to use for access inside hypervisor
//needs to be 2 or 1 (4 is hw-only, 3 is sinit-only on Intel)
#define EMHF_TPM_LOCALITY_PREF 2


//guest boot record is always loaded at 0000:7C00
#define __GUESTOSBOOTMODULE_BASE		0x7c00
#define __GUESTOSBOOTMODULESUP1_BASE	0x7C00

#define __CS 0x0008 /* Selector for GDT entry 1. RPL 0 */
#define __DS 0x0010 /* Selector for GDT enry 0. RPL 0 */
#define __TRSEL 0x0018  //selector for TSS


//size of runtime IDT, 32 exception vectors each 8 bytes
#define	SIZE_RUNTIME_IDT	(8*32)

#define MPFP_SIGNATURE (0x5F504D5FUL) //"_MP_"
#define MPCONFTABLE_SIGNATURE (0x504D4350UL)  //"PCMP"


#define AP_BOOTSTRAP_CODE_SEG 0x1000
#define SLB_BOOTSTRAP_CODE_BASE 0x40000000 /* 0x80000 */ /* 0x20000 */

#ifdef __NESTED_PAGING__
#define ASID_GUEST_KERNEL 2
#endif

//LAPIC emulation defines
#define LAPIC_OP_RSVD   (3)
#define LAPIC_OP_READ   (2)
#define LAPIC_OP_WRITE  (1)

//VMX runtime TSS size
#define VMX_RUNTIME_TSS_SIZE    (4096)

#define TEMPORARY_HARDCODED_MLE_SIZE       0x10000
#define TEMPORARY_MAX_MLE_HEADER_SIZE      0x80
#define TEMPORARY_HARDCODED_MLE_ENTRYPOINT TEMPORARY_MAX_MLE_HEADER_SIZE


//VMX Unrestricted Guest (UG) E820 hook support
//we currently use the BIOS data area (BDA) unused region
//at 0x0040:0x00AC
#define	VMX_UG_E820HOOK_CS				(0x0040)	
#define	VMX_UG_E820HOOK_IP				(0x00AC)

//----------------------------------------------------------------------





#ifndef __ASSEMBLY__

typedef u32 	paddr_t;		//physical address
typedef void* 	hva_t; 			//hypervisor virtual address 
typedef u64 	spa_t; 			//system physical address 
typedef u32 	gva_t; 			//guest virtual address. we only support 32-bit guests 
typedef u64 	gpa_t; 			//guest physical address. can be 64-bit with PAE 


#ifndef __ASSEMBLY__
#define BAD_INTEGRITY_HASH "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"

/* SHA-1 hash of runtime should be defined during build process.
 * However, if it's not, don't fail.  Just proceed with all zeros.
 * XXX TODO Disable proceeding with insecure hash value. */
#ifndef ___RUNTIME_INTEGRITY_HASH___
#define ___RUNTIME_INTEGRITY_HASH___ BAD_INTEGRITY_HASH
#endif /*  ___RUNTIME_INTEGRITY_HASH___ */

//"golden" digest values injected using CFLAGS during build process
//NOTE: NO WAY TO SELF-CHECK slbelow64K; JUST A SANITY-CHECK
typedef struct _integrity_measurement_values {
    u8 sha_slbelow64K[20]; // TODO: play nice with SHA_DIGEST_LENGTH in sha1.h
    u8 sha_slabove64K[20];
    u8 sha_runtime[20];
} INTEGRITY_MEASUREMENT_VALUES;
#endif /* __ASSEMBLY__ */


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
#define MAX_MIDTAB_ENTRIES  (4)


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

//---platform
typedef struct _grube820 {
  u32 baseaddr_low;
  u32 baseaddr_high;
  u32 length_low;
  u32 length_high;
  u32 type;  
} __attribute__((packed)) GRUBE820;

#define SIZE_STRUCT_GRUBE820  (sizeof(struct _grube820))
#define MAX_E820_ENTRIES    (64)  //maximum E820 entries we support, 64 should
                                  //be enough
//---platform
typedef struct _pcpu {
  u32 lapic_id;
  u32 lapic_ver;
  u32 lapic_base;
  u32 isbsp;
} __attribute__((packed)) PCPU;

#define SIZE_STRUCT_PCPU  (sizeof(struct _pcpu))
#define MAX_PCPU_ENTRIES  (MAX_MIDTAB_ENTRIES)


//---platform
//same privilege level exception/interrupt stack frame
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

//---platform
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

//---platform
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

//---platform
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
#define MAX_VCPU_ENTRIES    (MAX_PCPU_ENTRIES)
#define CPU_VENDOR (g_vcpubuffers[0].cpu_vendor)



//NOTE: The declaration here _MUST_ match definition of RPB in runtimesup.S	
typedef struct {
	u32 magic;
	u32 XtVmmEntryPoint;
	u32 XtVmmPdptBase;
	u32 XtVmmPdtsBase;
	//u32 XtVmmNpdtBase;
	//u32 XtVmmNestedNpdtBase;
	u32 XtGuestOSBootModuleBase;
	u32 XtGuestOSBootModuleSize;
	u32 XtGuestOSBootModuleBaseSup1;
	u32 XtGuestOSBootModuleSizeSup1;
	u32 XtVmmStackBase;
	u32 XtVmmStackSize;
	u32 XtVmmGdt;
	//u32 XtVmmNetworkAdapterStructureBase;
	//u32 XtVmmHsaveBase;
	//u32 XtVmmVMCBBase;
	//u32 XtVmmIopmBase;
	//u32 XtVmmNestedPdptBase;
	//u32 XtVmmNestedPdtsBase;
	//u32 XtVmmNestedPtsBase;
	u32 XtVmmIdt;
	u32 XtVmmIdtFunctionPointers;
	u32 XtVmmIdtEntries;
	//u32 XtVmmE1000DescBase;
	//u32 XtVmmE1000HeaderBase;
	//u32 XtVmmE1000BodyBase;
	u32 XtVmmRuntimePhysBase;
	u32 XtVmmRuntimeVirtBase;
	u32 XtVmmRuntimeSize;
	u32 XtVmmE820Buffer;
	u32 XtVmmE820NumEntries;
	u32 XtVmmMPCpuinfoBuffer;
	u32 XtVmmMPCpuinfoNumEntries;
	u32 XtVmmTSSBase;
	//u32 RtmSVMDevBitmapBase;
	//u32 RtmVMXVTdPdpt;
	//u32 RtmVMXVTdPdts;
	//u32 RtmVMXVTdPts;
	//u32 RtmVMXVTdRET;
	//u32 RtmVMXVTdCET;
    uart_config_t uart_config;	        /* runtime options parsed in init and passed forward */
	u32 isEarlyInit;					//1 for an "early init" else 0 (late-init)
} __attribute__((packed)) RPB, *PRPB;


//"sl" parameter block structure 
typedef struct _sl_parameter_block {
	u32 magic;	//magic identifier
	u32 hashSL;	//hash of the secure loader
	u32 errorHandler;	//error handler
	u32 isEarlyInit;	//"early" or "late" init
	u32 numE820Entries;		//number of E820 entries
	GRUBE820 e820map[MAX_E820_ENTRIES];	//E820 memory-map buffer
	u32 numCPUEntries;	//number of cores
	PCPU pcpus[MAX_PCPU_ENTRIES];	//CPU table buffer
	u32 runtime_size;			//size of the runtime image
	u32 runtime_osbootmodule_base;	//guest OS bootmodule base
	u32 runtime_osbootmodule_size;	//guest OS bootmodule size
    // Performance measurements related to DRTM
    u64 rdtsc_before_drtm;
    u64 rdtsc_after_drtm;

    /* runtime options parsed in init and passed forward */
    uart_config_t uart_config;
} __attribute__((packed)) SL_PARAMETER_BLOCK;



//----------------------------------------------------------------------
// EMHF application related declarations
//----------------------------------------------------------------------

//generic catch-all app return codes
#define APP_SUCCESS     (0x1)
#define APP_ERROR				(0x0)

//emhf app constant definitions
#define APP_IOINTERCEPT_CHAIN   0xA0
#define APP_IOINTERCEPT_SKIP    0xA1
#define APP_INIT_SUCCESS        0x0
#define APP_INIT_FAIL           0xFF


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
