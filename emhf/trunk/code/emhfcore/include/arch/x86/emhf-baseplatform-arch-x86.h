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

// EMHF base platform component 
// x86 arch. specific declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_BASEPLATFORM_ARCH_X86_H__
#define __EMHF_BASEPLATFORM_ARCH_X86_H__


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

//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------

//get CPU vendor
u32 emhf_baseplatform_arch_getcpuvendor(void);

//initialize CPU state
void emhf_baseplatform_arch_cpuinitialize(void);

//initialize SMP
void emhf_baseplatform_arch_smpinitialize(void);

//initialize basic platform elements
void emhf_baseplatform_arch_initialize(void);

//read 8-bits from absolute physical address
u8 emhf_baseplatform_arch_flat_readu8(u32 addr);

//read 32-bits from absolute physical address
u32 emhf_baseplatform_arch_flat_readu32(u32 addr);

//read 64-bits from absolute physical address
u64 emhf_baseplatform_arch_flat_readu64(u32 addr);

//write 32-bits to absolute physical address
void emhf_baseplatform_arch_flat_writeu32(u32 addr, u32 val);

//write 64-bits to absolute physical address
void emhf_baseplatform_arch_flat_writeu64(u32 addr, u64 val);

//memory copy from absolute physical address (src) to
//data segment relative address (dest)
void emhf_baseplatform_arch_flat_copy(u8 *dest, u8 *src, u32 size);

//reboot platform
void emhf_baseplatform_arch_reboot(VCPU *vcpu);


//----------------------------------------------------------------------
//x86 ARCH. INTERFACES
//----------------------------------------------------------------------


//x86 GDT descriptor type
typedef struct {
		u16 size;
		u32 base;
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
u32 emhf_baseplatform_arch_x86_isbsp(void);

//wake up APs using the LAPIC by sending the INIT-SIPI-SIPI IPI sequence
void emhf_baseplatform_arch_x86_wakeupAPs(void);

//generic x86 platform reboot
void emhf_baseplatform_arch_x86_reboot(void);

//get the physical address of the root system description pointer (rsdp)
u32 emhf_baseplatform_arch_x86_acpi_getRSDP(ACPI_RSDP *rsdp);

//PCI subsystem initialization
void emhf_baseplatform_arch_x86_pci_initialize(void);

//does a PCI type-1 write of PCI config space for a given bus, device, 
//function and index
void emhf_baseplatform_arch_x86_pci_type1_write(u32 bus, u32 device, u32 function, u32 index, u32 len,
	u32 value);
	
//does a PCI type-1 read of PCI config space for a given bus, device, 
//function and index
void emhf_baseplatform_arch_x86_pci_type1_read(u32 bus, u32 device, u32 function, u32 index, u32 len,
			u32 *value);

//microsecond delay
void emhf_baseplatform_arch_x86_udelay(u32 usecs);


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
extern u8 g_vmx_vmxon_buffers[] __attribute__(( section(".palign_data") ));

//VMX VMCS buffers
extern u8 g_vmx_vmcs_buffers[] __attribute__(( section(".palign_data") ));
		
//VMX IO bitmap buffers
extern u8 g_vmx_iobitmap_buffers[] __attribute__(( section(".palign_data") ));
		
//VMX guest and host MSR save area buffers
extern u8 g_vmx_msr_area_host_buffers[] __attribute__(( section(".palign_data") ));
extern u8 g_vmx_msr_area_guest_buffers[] __attribute__(( section(".palign_data") ));

//VMX MSR bitmap buffers
extern u8 g_vmx_msrbitmap_buffers[] __attribute__(( section(".palign_data") ));


//initialize CPU state
void emhf_baseplatform_arch_x86vmx_cpuinitialize(void);

//wake up application processors (cores) in the system
void emhf_baseplatform_arch_x86vmx_wakeupAPs(void);

//allocate and setup VCPU structure for all the CPUs
void emhf_baseplatform_arch_x86vmx_allocandsetupvcpus(u32 cpu_vendor);

// routine takes vcpu vmcsfields and stores it in the CPU VMCS 
void emhf_baseplatform_arch_x86vmx_putVMCS(VCPU *vcpu);

// routine takes CPU VMCS and stores it in vcpu vmcsfields  
void emhf_baseplatform_arch_x86vmx_getVMCS(VCPU *vcpu);

//--debug: dumpVMCS dumps VMCS contents
void emhf_baseplatform_arch_x86vmx_dumpVMCS(VCPU *vcpu);

//VMX specific platform reboot
void emhf_baseplatform_arch_x86vmx_reboot(VCPU *vcpu);

//----------------------------------------------------------------------
//x86svm SUBARCH. INTERFACES
//----------------------------------------------------------------------

//SVM VM_HSAVE buffers 
extern u8 g_svm_hsave_buffers[]__attribute__(( section(".palign_data") ));

//SVM VMCB buffers 
extern u8 g_svm_vmcb_buffers[]__attribute__(( section(".palign_data") )); 

//SVM IO bitmap buffer
extern u8 g_svm_iopm[]__attribute__(( section(".palign_data") )); 

//SVM MSR bitmap buffer
extern u8 g_svm_msrpm[]__attribute__(( section(".palign_data") ));


//wake up application processors (cores) in the system
void emhf_baseplatform_arch_x86svm_wakeupAPs(void);

//allocate and setup VCPU structure for all the CPUs
void emhf_baseplatform_arch_x86svm_allocandsetupvcpus(u32 cpu_vendor);

//SVM specific platform reboot
void emhf_baseplatform_arch_x86svm_reboot(VCPU *vcpu);






#endif	//__ASSEMBLY__

#endif //__EMHF_BASEPLATFORM_ARCH_X86_H__
