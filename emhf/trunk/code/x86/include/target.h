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
#include <svm.h>        //SVM extensions

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

//"sl" parameter block magic value
#define SL_PARAMETER_BLOCK_MAGIC	0xDEADBEEF


//"runtime" parameter block magic value
#define RUNTIME_PARAMETER_BLOCK_MAGIC	0xF00DDEAD

//guest boot record is always loaded at 0000:7C00
#define __GUESTOSBOOTMODULE_BASE	0x7c00
#define __GUESTOSBOOTMODULESUP1_BASE	0x7C00

#define __CS 0x0008 /* Selector for GDT entry 1. RPL 0 */
#define __DS 0x0010 /* Selector for GDT enry 0. RPL 0 */

#define MAX_E820_ENTRIES    (64)  //maximum E820 entries we support, 64 should
                                  //be enough
#define SIZE_STRUCT_GRUBE820  (20)

#define SIZE_STRUCT_PCPU  (16)
#define MAX_PCPU_ENTRIES  (4)

#define MPFP_SIGNATURE (0x5F504D5FUL) //"_MP_"
#define MPCONFTABLE_SIGNATURE (0x504D4350UL)  //"PCMP"

#define SIZE_STRUCT_MIDTAB  (8)
#define MAX_MIDTAB_ENTRIES  (MAX_PCPU_ENTRIES)

#define SIZE_STRUCT_VCPU    (52)
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


#ifndef __ASSEMBLY__




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
typedef struct {
  u32 cpu_lapic_id;       //CPU LAPIC id (unique)
  u32 vcpu_vaddr_ptr;     //virt. addr. pointer to vcpu struct for this CPU
} __attribute__((packed)) MIDTAB;

//the vcpu structure which holds the current state of a core
typedef struct {
  u32 esp;                //used to establish stack for the CPU
  u32 hsave_vaddr_ptr;    //VM_HSAVE area of the CPU
  u32 vmcb_vaddr_ptr;     //VMCB of the CPU
  u32 npt_vaddr_ptr;      //NPT base of the CPU
  u32 sipi_page_vaddr;    //SIPI page of the CPU used for SIPI handling
  u32 npt_asid;           //NPT ASID for this core
  u32 npt_vaddr_pts;      //NPT page-tables for protection manipulation
  u32 id;                 //LAPIC id of the core
  u32 sipivector;         //SIPI vector 
  u32 sipireceived;       //SIPI received indicator, 1 if yes
  u32 nmiinhvm;           //this is 1 if there was a NMI when in HVM, else 0        
	u32 cpu_vendor;					//Intel or AMD
	u32 isbsp;							//1 if this core is BSP else 0
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

#define __hva2spa__(x) ((x) - __TARGET_BASE + rpb->XtVmmRuntimePhysBase)


typedef struct {
  u32 baseaddr_low;
  u32 baseaddr_high;
  u32 length_low;
  u32 length_high;
  u32 type;  
} __attribute__((packed)) GRUBE820;


typedef struct {
  u32 baseaddr_low;
  u32 baseaddr_high;
  u32 length_low;
  u32 length_high;
  u32 type;  
} __attribute__((packed)) E820MAP;


//"sl" parameter block structure 
typedef struct {
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
} __attribute__((packed)) SL_PARAMETER_BLOCK;


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
} __attribute__((packed)) RPB, *PRPB;


#include <_libsechyp.h> //the SecHyp interface library



//generic isolation layer interface
struct isolation_layer {
	void 	(*initialize)(VCPU *vcpu);
	
	void	(*runtime_exception_handler)(u32 vector, struct regs *r);
	
	u32		(*isbsp)(void);
	void 	(*wakeup_aps)(void);
	
	void 	(*hvm_initialize_csrip)(VCPU *vcpu, u16 cs_selector, u32 cs_base, u64 rip);
	void 	(*hvm_apic_setup)(VCPU *vcpu);
	void 	(*hvm_start)(VCPU *vcpu);
	u32 	(*hvm_intercept_handler)(VCPU *vcpu, struct regs *r);
	
	void 	(*do_quiesce)(VCPU *vcpu);
	void 	(*setupvcpus)(u32 cpu_vendor);
}; 


extern struct isolation_layer g_isolation_layer_svm;

//SVM isolation layer interfaces
void svm_initialize(VCPU *vcpu);
void svm_runtime_exception_handler(u32 vector, struct regs *r);
u32 svm_isbsp(void);
void svm_wakeup_aps(void);
void svm_initialize_vmcb_csrip(VCPU *vcpu, u16 cs_selector, u32 cs_base, u64 rip);
void svm_apic_setup(VCPU *vcpu);
void svm_start_hvm(VCPU *vcpu);
u32 svm_intercept_handler(VCPU *vcpu, struct regs *r);
void svm_do_quiesce(VCPU *vcpu);
void svm_setupvcpus(u32 cpu_vendor);

//other SVM isolation layer global functions
u32 svm_lapic_access_handler(VCPU *vcpu, u32 paddr, u32 errorcode);
void svm_lapic_access_dbexception(VCPU *vcpu, struct regs *r);
void __svm_start_hvm(VCPU *vcpu, u32 vmcb_phys_addr);
u32 svm_kernel_pt_walker(struct vmcb_struct *vmcb, u32 vaddr);
void svm_apic_wakeupAPs(void);

#endif

#endif /* __TARGET_H_ */
