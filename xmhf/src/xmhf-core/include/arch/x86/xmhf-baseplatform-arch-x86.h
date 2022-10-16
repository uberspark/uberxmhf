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

// EMHF base platform component
// x86 arch. specific declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_BASEPLATFORM_ARCH_X86_H__
#define __EMHF_BASEPLATFORM_ARCH_X86_H__

#include "_configx86.h"		//EMHF arch. specific configurable definitions
#include "_multiboot.h"  	//boot manager (multiboot)
#include "_cmdline.h"		//GRUB command line handling functions
#include "_error.h"      	//error handling and assertions
#include "_processor.h"  	//CPU
#include "_msr.h"        	//model specific registers
#include "_paging.h"     	//MMU
#include "_io.h"         	//legacy I/O
#include "_apic.h"       	//APIC
#include "_svm.h"        	//SVM extensions
#include "_vmx.h"			//VMX extensions
#include "_txt.h"			//Trusted eXecution Technology (SENTER support)
#include "_pci.h"        	//PCI bus glue
#include "_acpi.h"			//ACPI glue
#include "_svm_eap.h"		//SVM DMA protection
#include "_vmx_eap.h"		//VMX DMA protection
#include "_vmx_ctls.h"		//VMX control bits


//SMP configuration table signatures on x86 platforms
#define MPFP_SIGNATURE 					(0x5F504D5FUL) //"_MP_"
#define MPCONFTABLE_SIGNATURE 			(0x504D4350UL)  //"PCMP"


#ifndef __ASSEMBLY__

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

//MTRR memory type structure
struct _memorytype {
  u64 startaddr;
  u64 endaddr;
  u32 type;
  u32 invalid;
  u32 reserved[6];
} __attribute__((packed));
#endif //__ASSEMBLY__

//---platform
#define NUM_FIXED_MTRRS 11
#define MAX_VARIABLE_MTRR_PAIRS 10


//---platform

#ifndef __ASSEMBLY__
//---platform
//structure which holds values of guest MTRRs (64-bit)
struct _guestvarmtrrmsrpair {
    u64 base;   /* IA32_MTRR_PHYSBASEi */
    u64 mask;   /* IA32_MTRR_PHYSMASKi */
};

struct _guestmtrrmsrs {
    u64 def_type;                   /* IA32_MTRR_DEF_TYPE */
    u64 fix_mtrrs[NUM_FIXED_MTRRS]; /* IA32_MTRR_FIX*, see fixed_mtrr_prop */
    u32 var_count;                  /* Number of valid var_mtrrs's */
    struct _guestvarmtrrmsrpair var_mtrrs[MAX_VARIABLE_MTRR_PAIRS];
};
#endif //__ASSEMBLY__

//---platform
//VMX MSR indices for the vcpu structure
#define INDEX_IA32_VMX_BASIC_MSR                0x0
#define INDEX_IA32_VMX_PINBASED_CTLS_MSR        0x1
#define INDEX_IA32_VMX_PROCBASED_CTLS_MSR       0x2
#define INDEX_IA32_VMX_EXIT_CTLS_MSR            0x3
#define INDEX_IA32_VMX_ENTRY_CTLS_MSR           0x4
#define INDEX_IA32_VMX_MISC_MSR                 0x5
#define INDEX_IA32_VMX_CR0_FIXED0_MSR           0x6
#define INDEX_IA32_VMX_CR0_FIXED1_MSR           0x7
#define INDEX_IA32_VMX_CR4_FIXED0_MSR           0x8
#define INDEX_IA32_VMX_CR4_FIXED1_MSR           0x9
#define INDEX_IA32_VMX_VMCS_ENUM_MSR            0xA
#define INDEX_IA32_VMX_PROCBASED_CTLS2_MSR      0xB
#define INDEX_IA32_VMX_EPT_VPID_CAP_MSR         0xC
#define INDEX_IA32_VMX_TRUE_PINBASED_CTLS_MSR   0xD
#define INDEX_IA32_VMX_TRUE_PROCBASED_CTLS_MSR  0xE
#define INDEX_IA32_VMX_TRUE_EXIT_CTLS_MSR       0xF
#define INDEX_IA32_VMX_TRUE_ENTRY_CTLS_MSR      0x10
#define INDEX_IA32_VMX_VMFUNC_MSR               0x11

//---platform
#define IA32_VMX_MSRCOUNT                       18

#ifndef __ASSEMBLY__

/*
 * Control NMI blocking. Note that this is different from hardware NMI blocking
 * or virtual-NMI blocking.
 */
typedef struct {
  /* Whether guest wants to blocks NMI */
  bool guest_nmi_block;
  /*
   * Number of pending NMI interrupts to inject to the guest.
   * When the guest OS is blocking NMIs (using "Blocking by NMI" bit in VMCS),
   * the maximum number of this field is 1. Otherwise, the maximum is 2.
   * guest_nmi_block does not affect the maximum number of this field.
   */
  u32 guest_nmi_pending;
} guest_nmi_t;

//the vcpu structure which holds the current state of a core
typedef struct _vcpu {
  //common fields
#ifdef __AMD64__
  hva_t rsp;              //used to establish stack for the CPU
#elif defined(__I386__)
  hva_t esp;              //used to establish stack for the CPU
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
  hva_t sipi_page_vaddr;  //SIPI page of the CPU used for SIPI handling
  u32 id;                 //LAPIC id of the core
  u32 idx;                //this vcpu's index in the g_vcpubuffers array
  u32 sipivector;         //SIPI vector
  volatile u32 sipireceived; //SIPI received indicator, 1 if yes
  //u32 nmiinhvm;           //this is 1 if there was a NMI when in HVM, else 0
  u32 cpu_vendor;         //Intel or AMD
  u32 isbsp;              //1 if this core is BSP else 0
  u32 quiesced;           //1 if this core is currently quiesced

  //SVM specific fields
  hva_t hsave_vaddr_ptr;    //VM_HSAVE area of the CPU
  //u32 vmcb_vaddr_ptr;     //VMCB of the CPU
  struct _svm_vmcbfields *vmcb_vaddr_ptr;
  //u32 npt_vaddr_ptr;      //NPT base of the CPU
  hva_t npt_vaddr_ptr;      //NPT base of the CPU
  hva_t npt_vaddr_pdts;
  u32 npt_asid;           //NPT ASID for this core
  hva_t npt_vaddr_pts;      //NPT page-tables for protection manipulation
  hva_t svm_vaddr_iobitmap; //virtual address of the I/O Bitmap area

  //VMX specific fields
  u64 vmx_msrs[IA32_VMX_MSRCOUNT];  //VMX msr values
  u64 vmx_pinbased_ctls;          //IA32_VMX_PINBASED_CTLS or IA32_VMX_TRUE_...
  u64 vmx_procbased_ctls;         //IA32_VMX_PROCBASED_CTLS or IA32_VMX_TRUE_...
  u64 vmx_exit_ctls;              //IA32_VMX_EXIT_CTLS or IA32_VMX_TRUE_...
  u64 vmx_entry_ctls;             //IA32_VMX_ENTRY_CTLS or IA32_VMX_TRUE_...
  vmx_ctls_t vmx_caps;            //VMX controls that are supported by hardware

  hva_t vmx_vmxonregion_vaddr;    //virtual address of the vmxon region
  hva_t vmx_vmcs_vaddr;           //virtual address of the VMCS region

  hva_t vmx_vaddr_iobitmap;       //virtual address of the I/O Bitmap area
  hva_t vmx_vaddr_msr_area_host;  //virtual address of the host MSR area
  hva_t vmx_vaddr_msr_area_guest; //virtual address of the guest MSR area
  hva_t vmx_vaddr_msrbitmaps;     //virtual address of the MSR bitmap area

  hva_t vmx_vaddr_ept_pml4_table; //virtual address of EPT PML4 table
  hva_t vmx_vaddr_ept_pdp_table;  //virtual address of EPT PDP table
  hva_t vmx_vaddr_ept_pd_tables;  //virtual address of base of EPT PD tables
  hva_t vmx_vaddr_ept_p_tables;   //virtual address of base of EPT P tables


  u32 vmx_ept_defaulttype;        //default EPT memory type
  u32 vmx_ept_mtrr_enable;
  u32 vmx_ept_fixmtrr_enable;
  u64 vmx_ept_paddrmask;          //mask from bit 12 to MAXPHYADDR
  //guest MTRR shadow MSRs
  struct _guestmtrrmsrs vmx_guestmtrrmsrs;

  /*
   * Whether the hypervisor is not busy so that it can inject NMI to the guest.
   * If not, NMI exception should set vmx_mhv_nmi_visited to true. The
   * hypervisor will check that variable later when it is not busy.
   */
  volatile bool vmx_mhv_nmi_enable;
  /* Whether an NMI exception arrived during vmx_mhv_nmi_enable = false */
  volatile u32 vmx_mhv_nmi_visited;
  /*
   * Argument to NMI exception handler, decides how the NMI exception is
   * handled. Values are macros starting with "SMPG_VMX_NMI_".
   *
   * Note for verification: this variable is similar to a function pointer.
   * Need to prove that it only has a few fixed values.
   */
  u32 vmx_mhv_nmi_handler_arg;

  /* Configure NMI blocking for the guest */
  guest_nmi_t vmx_guest_nmi_cfg;

  //guest state fields
  u32 vmx_guest_unrestricted;   //this is 1 if the CPU VMX implementation supports unrestricted guest execution
  struct _vmx_vmcsfields vmcs;   //the VMCS fields

} VCPU;

#define SIZE_STRUCT_VCPU    (sizeof(struct _vcpu))
#define CPU_VENDOR (g_vcpubuffers[0].cpu_vendor)

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

//read 8-bits from absolute physical address
u8 xmhf_baseplatform_arch_flat_readu8(u32 addr);

//read 32-bits from absolute physical address
u32 xmhf_baseplatform_arch_flat_readu32(u32 addr);

//read 64-bits from absolute physical address
u64 xmhf_baseplatform_arch_flat_readu64(u32 addr);

//write 32-bits to absolute physical address
void xmhf_baseplatform_arch_flat_writeu32(u32 addr, u32 val);

//write 64-bits to absolute physical address
void xmhf_baseplatform_arch_flat_writeu64(u32 addr, u64 val);

//memory copy from absolute physical address (src) to
//data segment relative address (dest)
void xmhf_baseplatform_arch_flat_copy(u8 *dest, u8 *src, u32 size);

//reboot platform
void xmhf_baseplatform_arch_reboot(VCPU *vcpu);

//returns true if CPU has support for XSAVE/XRSTOR
bool xmhf_baseplatform_arch_x86_cpuhasxsavefeature(void);

#endif //__ASSEMBLY__

//----------------------------------------------------------------------
//x86 ARCH. INTERFACES
//----------------------------------------------------------------------
#ifdef __AMD64__
#define 	__CS 	0x0008 	//runtime code segment selector
#define 	__DS 	0x0018 	//runtime data segment selector
#define 	__CS32 	0x0010 	//runtime 32-bit code segment selector
#define 	__TRSEL 0x0020  //runtime TSS (task) selector
#elif defined(__I386__)
#define 	__CS 	0x0008 	//runtime code segment selector
#define 	__DS 	0x0010 	//runtime data segment selector
#define 	__TRSEL 0x0018  //runtime TSS (task) selector
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */


#ifndef __ASSEMBLY__

//x86 GDT descriptor type
typedef struct {
  u16 size;
  uintptr_t base;
} __attribute__((packed)) arch_x86_gdtdesc_t;


//runtime TSS
extern u8 g_runtime_TSS[PAGE_SIZE_4K] __attribute__(( section(".data") ));

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



//return 1 if the calling CPU is the BSP
u32 xmhf_baseplatform_arch_x86_isbsp(void);

//wake up APs using the LAPIC by sending the INIT-SIPI-SIPI IPI sequence
void xmhf_baseplatform_arch_x86_wakeupAPs(void);

//generic x86 platform reboot
void xmhf_baseplatform_arch_x86_reboot(void);

//get the physical address of the root system description pointer (rsdp)
uintptr_t xmhf_baseplatform_arch_x86_acpi_getRSDP(ACPI_RSDP *rsdp);

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


static inline u64 VCPU_gdtr_base(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_GDTR_base;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->gdtr.base;
  } else {
    HALT_ON_ERRORCOND(false);
    return 0;
  }
}

static inline size_t VCPU_gdtr_limit(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_GDTR_limit;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->gdtr.limit;
  } else {
    HALT_ON_ERRORCOND(false);
    return 0;
  }
}

static inline u64 VCPU_grflags(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RFLAGS;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->rflags;
  } else {
    HALT_ON_ERRORCOND(false);
    return 0;
  }
}

static inline void VCPU_grflags_set(VCPU *vcpu, u64 val)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RFLAGS = val;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->rflags = val;
  } else {
    HALT_ON_ERRORCOND(false);
  }
}

static inline u64 VCPU_grip(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RIP;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->rip;
  } else {
    HALT_ON_ERRORCOND(false);
    return 0;
  }
}

static inline void VCPU_grip_set(VCPU *vcpu, u64 val)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RIP = val;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->rip = val;
  } else {
    HALT_ON_ERRORCOND(false);
  }
}

static inline u64 VCPU_grsp(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RSP;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->rsp;
  } else {
    HALT_ON_ERRORCOND(false);
    return 0;
  }
}

static inline void VCPU_grsp_set(VCPU *vcpu, u64 val)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RSP = val;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->rsp = val;
  } else {
    HALT_ON_ERRORCOND(false);
  }
}

static inline ulong_t VCPU_gcr0(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return vcpu->vmcs.guest_CR0;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->cr0;
  } else {
    HALT_ON_ERRORCOND(false);
    return 0;
  }
}

static inline void VCPU_gcr0_set(VCPU *vcpu, ulong_t cr0)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    vcpu->vmcs.guest_CR0 = cr0;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->cr0 = cr0;
  } else {
    HALT_ON_ERRORCOND(false);
  }
}

static inline u64 VCPU_gcr3(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return vcpu->vmcs.guest_CR3;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->cr3;
  } else {
    HALT_ON_ERRORCOND(false);
    return 0;
  }
}

static inline void VCPU_gcr3_set(VCPU *vcpu, u64 cr3)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    vcpu->vmcs.guest_CR3 = cr3;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->cr3 = cr3;
  } else {
    HALT_ON_ERRORCOND(false);
  }
}

static inline ulong_t VCPU_gcr4(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return vcpu->vmcs.guest_CR4;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->cr4;
  } else {
    HALT_ON_ERRORCOND(false);
    return 0;
  }
}

static inline void VCPU_gcr4_set(VCPU *vcpu, ulong_t cr4)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    vcpu->vmcs.guest_CR4 = cr4;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct _svm_vmcbfields*)vcpu->vmcb_vaddr_ptr)->cr4 = cr4;
  } else {
    HALT_ON_ERRORCOND(false);
  }
}

/* Return whether guest OS is in long mode (return 1 or 0) */
static inline u32 VCPU_glm(VCPU *vcpu) {
    if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
        return (vcpu->vmcs.control_VM_entry_controls >>
                VMX_VMENTRY_IA_32E_MODE_GUEST) & 1U;
    } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
        /* Not implemented */
        HALT_ON_ERRORCOND(false);
        return 0;
    } else {
        HALT_ON_ERRORCOND(false);
        return 0;
    }
}

/*
 * Return whether guest application is in 64-bit mode (return 1 or 0).
 * If guest OS is in long mode, return 1 if guest application in 64-bit mode.
 * If guest OS in legacy mode (e.g. protected mode), will always return 0;
 */
static inline u32 VCPU_g64(VCPU *vcpu) {
    if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
        return (vcpu->vmcs.guest_CS_access_rights >> 13) & 1U;
    } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
        /* Not implemented */
        HALT_ON_ERRORCOND(false);
        return 0;
    } else {
        HALT_ON_ERRORCOND(false);
        return 0;
    }
}

/*
 * Update vcpu->vmcs.guest_PDPTE{0..3} for PAE guests. This is needed
 * after guest CR3 is changed.
 */
static inline void VCPU_gpdpte_set(VCPU *vcpu, u64 pdptes[4]) {
    if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
        vcpu->vmcs.guest_PDPTE0 = pdptes[0];
        vcpu->vmcs.guest_PDPTE1 = pdptes[1];
        vcpu->vmcs.guest_PDPTE2 = pdptes[2];
        vcpu->vmcs.guest_PDPTE3 = pdptes[3];
    } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
        /* Not implemented */
        HALT_ON_ERRORCOND(false);
    } else {
        HALT_ON_ERRORCOND(false);
    }
}

/*
 * Selector for VCPU_reg_get and VCPU_reg_set
 */
enum CPU_Reg_Sel
{
    CPU_REG_AX,
    CPU_REG_CX,
    CPU_REG_DX,
    CPU_REG_BX,
    CPU_REG_SP,
    CPU_REG_BP,
    CPU_REG_SI,
    CPU_REG_DI,
#ifdef __AMD64__
    CPU_REG_R8,
    CPU_REG_R9,
    CPU_REG_R10,
    CPU_REG_R11,
    CPU_REG_R12,
    CPU_REG_R13,
    CPU_REG_R14,
    CPU_REG_R15,
#elif !defined(__I386__)
    #error "Unsupported Arch"
#endif /* !defined(__I386__) */

    CPU_REG_FLAGS,
    CPU_REG_IP
};

/*
 * Get a guest register
 */
static inline ulong_t VCPU_reg_get(VCPU *vcpu, struct regs* r,
                                     enum CPU_Reg_Sel sel)
{
    switch (sel)
    {
#ifdef __AMD64__
        case CPU_REG_AX: return r->rax;
        case CPU_REG_CX: return r->rcx;
        case CPU_REG_DX: return r->rdx;
        case CPU_REG_BX: return r->rbx;
        /* CPU_REG_SP is managed by VCPU_grsp() */
        case CPU_REG_BP: return r->rbp;
        case CPU_REG_SI: return r->rsi;
        case CPU_REG_DI: return r->rdi;
        case CPU_REG_R8: return r->r8;
        case CPU_REG_R9: return r->r9;
        case CPU_REG_R10: return r->r10;
        case CPU_REG_R11: return r->r11;
        case CPU_REG_R12: return r->r12;
        case CPU_REG_R13: return r->r13;
        case CPU_REG_R14: return r->r14;
        case CPU_REG_R15: return r->r15;
#elif defined(__I386__)
        case CPU_REG_AX: return r->eax;
        case CPU_REG_CX: return r->ecx;
        case CPU_REG_DX: return r->edx;
        case CPU_REG_BX: return r->ebx;
        /* CPU_REG_SP is managed by VCPU_grsp() */
        case CPU_REG_BP: return r->ebp;
        case CPU_REG_SI: return r->esi;
        case CPU_REG_DI: return r->edi;
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */

        case CPU_REG_SP: return VCPU_grsp(vcpu);
        case CPU_REG_FLAGS: return VCPU_grflags(vcpu);
        case CPU_REG_IP: return VCPU_grip(vcpu);

        default:
            printf("VCPU_reg_get: Invalid guest CPU register is given (sel:%u)!\n", sel);
            HALT();
            return 0; // should never hit
    }
}

/*
 * Set a guest register
 */
static inline void VCPU_reg_set(VCPU *vcpu, struct regs* r,
                                enum CPU_Reg_Sel sel, ulong_t val)
{
    switch (sel)
    {
#ifdef __AMD64__
        case CPU_REG_AX: r->rax = val; break;
        case CPU_REG_CX: r->rcx = val; break;
        case CPU_REG_DX: r->rdx = val; break;
        case CPU_REG_BX: r->rbx = val; break;
        /* CPU_REG_SP is managed by VCPU_grsp_set() */
        case CPU_REG_BP: r->rbp = val; break;
        case CPU_REG_SI: r->rsi = val; break;
        case CPU_REG_DI: r->rdi = val; break;
        case CPU_REG_R8: r->r8 = val; break;
        case CPU_REG_R9: r->r9 = val; break;
        case CPU_REG_R10: r->r10 = val; break;
        case CPU_REG_R11: r->r11 = val; break;
        case CPU_REG_R12: r->r12 = val; break;
        case CPU_REG_R13: r->r13 = val; break;
        case CPU_REG_R14: r->r14 = val; break;
        case CPU_REG_R15: r->r15 = val; break;
#elif defined(__I386__)
        case CPU_REG_AX: r->eax = val; break;
        case CPU_REG_CX: r->ecx = val; break;
        case CPU_REG_DX: r->edx = val; break;
        case CPU_REG_BX: r->ebx = val; break;
        /* CPU_REG_SP is managed by VCPU_grsp_set() */
        case CPU_REG_BP: r->ebp = val; break;
        case CPU_REG_SI: r->esi = val; break;
        case CPU_REG_DI: r->edi = val; break;
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */

        case CPU_REG_SP: 
            VCPU_grsp_set(vcpu, val);
            break;
        case CPU_REG_FLAGS:
            VCPU_grflags_set(vcpu, val);
            break;
        case CPU_REG_IP:
            VCPU_grip_set(vcpu, val);
            break;

        default:
            printf("VCPU_reg_set: Invalid guest CPU register is given (sel:%u)!\n", sel);
            HALT();
    }
}

//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------

//this is the MLE Join stucture to bring up the APs (bplt-x86-smptrampoline.S)
extern u32 _mle_join_start[];


//VMX VMCS read-only field encodings
extern struct _vmx_vmcsrofields_encodings g_vmx_vmcsrofields_encodings[] __attribute__(( section(".data") ));

//count of VMX VMCS read-only fields
extern unsigned int g_vmx_vmcsrofields_encodings_count __attribute__(( section(".data") ));

//VMX VMCS read-write field encodings
extern struct _vmx_vmcsrwfields_encodings g_vmx_vmcsrwfields_encodings[] __attribute__(( section(".data") ));

//count of VMX VMCS read-write fields
extern unsigned int g_vmx_vmcsrwfields_encodings_count __attribute__(( section(".data") ));

//VMX VMXON buffers
extern u8 g_vmx_vmxon_buffers[] __attribute__(( section(".bss.palign_data") ));

//VMX VMCS buffers
extern u8 g_vmx_vmcs_buffers[] __attribute__(( section(".bss.palign_data") ));

//VMX IO bitmap buffers
extern u8 g_vmx_iobitmap_buffer[] __attribute__(( section(".bss.palign_data") ));

// 2nd IO bitmap buffers. Some hypapps may need a 2nd bitmap.
extern u8 g_vmx_iobitmap_buffer_2nd[] __attribute__(( section(".bss.palign_data") ));

//VMX guest and host MSR save area buffers
extern u8 g_vmx_msr_area_host_buffers[] __attribute__(( section(".bss.palign_data") ));
extern u8 g_vmx_msr_area_guest_buffers[] __attribute__(( section(".bss.palign_data") ));

//VMX MSR bitmap buffers
extern u8 g_vmx_msrbitmap_buffers[] __attribute__(( section(".bss.palign_data") ));


//initialize CPU state
void xmhf_baseplatform_arch_x86vmx_cpuinitialize(void);

//wake up application processors (cores) in the system
void xmhf_baseplatform_arch_x86vmx_wakeupAPs(void);

//allocate and setup VCPU structure for all the CPUs
void xmhf_baseplatform_arch_x86vmx_allocandsetupvcpus(u32 cpu_vendor);

// VMWRITE and VMREAD of different sizes
void __vmx_vmwrite16(unsigned long encoding, u16 value);
void __vmx_vmwrite64(unsigned long encoding, u64 value);
void __vmx_vmwrite32(unsigned long encoding, u32 value);
void __vmx_vmwriteNW(unsigned long encoding, ulong_t value);
u16 __vmx_vmread16(unsigned long encoding);
u64 __vmx_vmread64(unsigned long encoding);
u32 __vmx_vmread32(unsigned long encoding);
ulong_t __vmx_vmreadNW(unsigned long encoding);

// routine takes vcpu vmcsfields and stores it in the CPU VMCS
void xmhf_baseplatform_arch_x86vmx_putVMCS(VCPU *vcpu);

// routine takes CPU VMCS and stores it in vcpu vmcsfields
void xmhf_baseplatform_arch_x86vmx_getVMCS(VCPU *vcpu);

//--debug: dump_vcpu dumps vcpu contents (including VMCS)
void xmhf_baseplatform_arch_x86vmx_dump_vcpu(VCPU *vcpu);

//VMX specific platform reboot
void xmhf_baseplatform_arch_x86vmx_reboot(VCPU *vcpu);

//----------------------------------------------------------------------
//x86svm SUBARCH. INTERFACES
//----------------------------------------------------------------------

#ifdef __NESTED_PAGING__
#define ASID_GUEST_KERNEL 2
#endif

//SVM VM_HSAVE buffers
extern u8 g_svm_hsave_buffers[]__attribute__(( section(".bss.palign_data") ));

//SVM VMCB buffers
extern u8 g_svm_vmcb_buffers[]__attribute__(( section(".bss.palign_data") ));

//SVM IO bitmap buffer
extern u8 g_svm_iobitmap_buffer[]__attribute__(( section(".bss.palign_data") ));

//SVM MSR bitmap buffer
extern u8 g_svm_msrpm[]__attribute__(( section(".bss.palign_data") ));


//wake up application processors (cores) in the system
void xmhf_baseplatform_arch_x86svm_wakeupAPs(void);

//allocate and setup VCPU structure for all the CPUs
void xmhf_baseplatform_arch_x86svm_allocandsetupvcpus(u32 cpu_vendor);

//SVM specific platform reboot
void xmhf_baseplatform_arch_x86svm_reboot(VCPU *vcpu);






#endif	//__ASSEMBLY__

#endif //__EMHF_BASEPLATFORM_ARCH_X86_H__
