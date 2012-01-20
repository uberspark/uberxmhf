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

//emhf.h - main EMHF core header file 
// this orchestrates the inclusion of other core component specific
// headers
//author: amit vasudevan (amitvasudevan@acm.org)
//
#ifndef __EMHF_H_
#define __EMHF_H_

/* SHA-1 hash of runtime should be defined during build process.
 * However, if it's not, don't fail.  Just proceed with all zeros.
 * XXX TODO Disable proceeding with insecure hash value. */
#ifndef ___RUNTIME_INTEGRITY_HASH___
#define ___RUNTIME_INTEGRITY_HASH___ BAD_INTEGRITY_HASH
#endif /*  ___RUNTIME_INTEGRITY_HASH___ */


//---includes for the target----------------------------------------------------
#ifndef __ASSEMBLY__
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>
#endif /* __ASSEMBLY__ */


#include <_ctype.h>		//the ctype variable definition for debug printf
#include <_com.h>		//serial UART as debugging backend
//#include <_print.h>      //early chance to disable/enable debug printfs
#include <_multiboot.h>  //boot manager (multiboot)
#include <_cmdline.h>	//GRUB command line handling functions
#include <_error.h>      //error handling and assertions

#include <_processor.h>  //CPU
#include <_msr.h>        //model specific registers
#include <_paging.h>     //MMU
#include <_io.h>         //legacy I/O
#include <_apic.h>       //APIC
#include <_svm.h>        //SVM extensions
#include <_vmx.h>				//VMX extensions

#include <_txt.h>		//Trusted eXecution Technology (SENTER support)

#include <_pci.h>        //PCI bus glue
#include <_acpi.h>				//ACPI glue

#include <_svm_eap.h>		//SVM DMA protection
#include <_vmx_eap.h>		//VMX DMA protection

#include <_tpm.h>			//generic TPM functions
#include <_tpm_emhf.h>		//EMHF-specific TPM functions

//language specifics
#include <_sarg.h>
#include <_div64.h>

#include <_perf.h>			//performance measurement routines



#include <emhf-types.h>		//EMHF specific base types

//----------------------------------------------------------------------
// component headers
#include <emhf-debug.h>		//EMHF debug component
#include <emhf-sl.h>		//EMHF secure loader component
#include <emhf-memprot.h>	//EMHF memory protection component
#include <emhf-dmaprot.h>	//EMHF DMA protection component
#include <emhf-parteventhub.h>	//EMHF partition event-hub component
#include <emhf-smpguest.h>		//EMHF SMP guest component
#include <emhf-xcphandler.h>	//EMHF exception handler component
#include <emhf-baseplatform.h>	//EMHF base platform component



//------------------------------------------------------------------------------
//preferred TPM locality to use for access inside hypervisor
//needs to be 2 or 1 (4 is hw-only, 3 is sinit-only on Intel)
#define EMHF_TPM_LOCALITY_PREF 2

//runtime base address (virtual)
#define __TARGET_BASE	0xC0000000

//"sl" parameter block magic value
#define SL_PARAMETER_BLOCK_MAGIC	0xDEADBEEF

//"runtime" parameter block magic value
#define RUNTIME_PARAMETER_BLOCK_MAGIC	0xF00DDEAD

//guest boot record is always loaded at 0000:7C00
#define __GUESTOSBOOTMODULE_BASE	0x7c00
#define __GUESTOSBOOTMODULESUP1_BASE	0x7C00

#define __CS 0x0008 /* Selector for GDT entry 1. RPL 0 */
#define __DS 0x0010 /* Selector for GDT enry 0. RPL 0 */
#define __TRSEL 0x0018  //selector for TSS


//size of runtime IDT, 32 exception vectors each 8 bytes
#define	SIZE_RUNTIME_IDT	(8*32)

#define MAX_E820_ENTRIES    (64)  //maximum E820 entries we support, 64 should
                                  //be enough
//#define SIZE_STRUCT_GRUBE820  (20)

//#define SIZE_STRUCT_PCPU  (16)
#define MAX_PCPU_ENTRIES  (4)

#define MPFP_SIGNATURE (0x5F504D5FUL) //"_MP_"
#define MPCONFTABLE_SIGNATURE (0x504D4350UL)  //"PCMP"

//#define SIZE_STRUCT_MIDTAB  (8)
#define MAX_MIDTAB_ENTRIES  (MAX_PCPU_ENTRIES)

#define MAX_VCPU_ENTRIES    (MAX_PCPU_ENTRIES)

#define AP_BOOTSTRAP_CODE_SEG 0x1000
#define SLB_BOOTSTRAP_CODE_BASE 0x40000000 /* 0x80000 */ /* 0x20000 */

#define RUNTIME_STACK_SIZE  (16384)     //16K stack for each core
#define INIT_STACK_SIZE	(8192)					//8K stack for each core in "init"

#ifdef __NESTED_PAGING__
#define ASID_GUEST_KERNEL 2
#endif

//emhf app constant definitions
#define APP_IOINTERCEPT_CHAIN   0xA0
#define APP_IOINTERCEPT_SKIP    0xA1
#define APP_INIT_SUCCESS        0x0
#define APP_INIT_FAIL           0xFF

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


#ifndef __ASSEMBLY__

//#include <_bitfield.h> /* bit manipulation helpers */
//#include <hpt.h> /* hardware page table types */

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




typedef struct _pcpu {
  u32 lapic_id;
  u32 lapic_ver;
  u32 lapic_base;
  u32 isbsp;
} __attribute__((packed)) PCPU;

#define SIZE_STRUCT_PCPU  (sizeof(struct _pcpu))

typedef struct _grube820 {
  u32 baseaddr_low;
  u32 baseaddr_high;
  u32 length_low;
  u32 length_high;
  u32 type;  
} __attribute__((packed)) GRUBE820;

#define SIZE_STRUCT_GRUBE820  (sizeof(struct _grube820))


/*typedef struct {
  u32 baseaddr_low;
  u32 baseaddr_high;
  u32 length_low;
  u32 length_high;
  u32 type;  
} __attribute__((packed)) E820MAP;*/


#define BAD_INTEGRITY_HASH "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"

//"golden" digest values injected using CFLAGS during build process
//NOTE: NO WAY TO SELF-CHECK slbelow64K; JUST A SANITY-CHECK
typedef struct _integrity_measurement_values {
    u8 sha_slbelow64K[20]; // TODO: play nice with SHA_DIGEST_LENGTH in sha1.h
    u8 sha_slabove64K[20];
    u8 sha_runtime[20];
} INTEGRITY_MEASUREMENT_VALUES;

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
// host to guest, guest to host VA to PA helpers
// XXX: should belong in the "platform" component
/* defined in global.h. can't just include globals.h because it
   depends on this header */
static inline void* spa2hva(spa_t spa);
static inline spa_t hva2spa(void *hva);
static inline spa_t gpa2spa(gpa_t gpa);
static inline gpa_t spa2gpa(spa_t spa);
static inline void* gpa2hva(gpa_t gpa);
static inline gpa_t hva2gpa(hva_t hva);

//#define __pa(x) (x)
//#define __hva2spa__(x) (hva2spa(x))
//#define __spa2hva__(x) (spa2hva(x))
//----------------------------------------------------------------------


//----------------------------------------------------------------------
// memory protection and platform specific EMHFapp interfaces
// XXX: move these into appropriate components and document


/*#define VCPU_get_pml1es emhf_memprot_get_lvl1_pagemap_address
#define VCPU_get_pml2es emhf_memprot_get_lvl2_pagemap_address
#define VCPU_get_pml3es emhf_memprot_get_lvl3_pagemap_address
#define VCPU_get_pml4 emhf_memprot_get_lvl4_pagemap_address*/






static inline u64 VCPU_gdtr_base(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_GDTR_base;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->gdtr.base;
  } else {
    ASSERT(false);
    return 0;
  }
}

static inline size_t VCPU_gdtr_limit(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_GDTR_limit;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->gdtr.limit;
  } else {
    ASSERT(false);
    return 0;
  }
}

static inline u64 VCPU_grflags(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RFLAGS;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->rflags;
  } else {
    ASSERT(false);
    return 0;
  }
}

static inline void VCPU_grflags_set(VCPU *vcpu, u64 val)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RFLAGS = val;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->rflags = val;
  } else {
    ASSERT(false);
  }
}

static inline u64 VCPU_grip(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RIP;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->rip;
  } else {
    ASSERT(false);
    return 0;
  }
}

static inline void VCPU_grip_set(VCPU *vcpu, u64 val)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RIP = val;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->rip = val;
  } else {
    ASSERT(false);
  }
}

static inline u64 VCPU_grsp(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RSP;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->rsp;
  } else {
    ASSERT(false);
    return 0;
  }
}

static inline void VCPU_grsp_set(VCPU *vcpu, u64 val)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    ((struct _vmx_vmcsfields*)&(vcpu->vmcs))->guest_RSP = val;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->rsp = val;
  } else {
    ASSERT(false);
  }
}

static inline u64 VCPU_gcr3(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return vcpu->vmcs.guest_CR3;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->cr3;
  } else {
    ASSERT(false);
    return 0;
  }
}

static inline void VCPU_gcr3_set(VCPU *vcpu, u64 cr3)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    vcpu->vmcs.guest_CR3 = cr3;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->cr3 = cr3;
  } else {
    ASSERT(false);
  }
}

static inline u64 VCPU_gcr4(VCPU *vcpu)
{
  if (vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
    return vcpu->vmcs.guest_CR4;
  } else if (vcpu->cpu_vendor == CPU_VENDOR_AMD) {
    return ((struct vmcb_struct*)vcpu->vmcb_vaddr_ptr)->cr4;
  } else {
    ASSERT(false);
    return 0;
  }
}

//----------------------------------------------------------------------

//generic isolation layer interface
struct isolation_layer {
	//void 	(*initialize)(VCPU *vcpu);
	
	//void	(*runtime_exception_handler)(u32 vector, struct regs *r);
	
	//u32		(*isbsp)(void);
	//void 	(*wakeup_aps)(void);
	
	//void 	(*hvm_initialize_csrip)(VCPU *vcpu, u16 cs_selector, u32 cs_base, u64 rip);
	//void 	(*hvm_apic_setup)(VCPU *vcpu);
	//void 	(*hvm_start)(VCPU *vcpu);
	//u32 	(*hvm_intercept_handler)(VCPU *vcpu, struct regs *r);
	
	//void 	(*do_quiesce)(VCPU *vcpu);
	//void 	(*do_wakeup)(VCPU *vcpu);
	//void 	(*setupvcpus)(u32 cpu_vendor);
}; 



/* TODO: is this a reasonable home for this prototype? */
u32 smp_getinfo(PCPU *pcpus, u32 *num_pcpus);


#include <_globals.h>

#endif

#endif /* __EMHF_H_ */
