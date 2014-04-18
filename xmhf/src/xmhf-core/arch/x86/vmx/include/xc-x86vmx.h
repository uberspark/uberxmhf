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

// xc-x86.h - XMHF core x86 vmx arch. main header file 
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef _XC_X86VMX_H_
#define _XC_X86VMX_H_

#include <xmhf.h>
#include <xmhf-core.h>

#ifndef __ASSEMBLY__

typedef struct {
  u32 vmx_vmxon_region[PAGE_SIZE_4K];    		
  u32 vmx_vmcs_region[PAGE_SIZE_4K];           
  u32 vmx_msr_area_host_region[2*PAGE_SIZE_4K];		
  u32 vmx_msr_area_guest_region[2*PAGE_SIZE_4K];		
  u64 vmx_msrs[IA32_VMX_MSRCOUNT];  
  u64 vmx_msr_efer;
  u64 vmx_msr_efcr;
} xc_cpuarchdata_x86vmx_t;
	
	


//xc-richguest

//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------

//void xmhf_smpguest_arch_x86vmx_initialize(VCPU *vcpu);
void xmhf_smpguest_arch_x86vmx_eventhandler_dbexception(context_desc_t context_desc, 
	struct regs *r);
void xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(VCPU *vcpu, struct regs *r);
u32 xmhf_smpguest_arch_x86vmx_eventhandler_hwpgtblviolation(context_desc_t context_desc, u32 paddr, u32 errorcode);
void xmhf_smpguest_arch_x86vmx_quiesce(VCPU *vcpu);
void xmhf_smpguest_arch_x86vmx_endquiesce(VCPU *vcpu);


//perform required setup after a guest awakens a new CPU
//void xmhf_smpguest_arch_x86vmx_postCPUwakeup(VCPU *vcpu);
//walk guest page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
u8 * xmhf_smpguest_arch_x86vmx_walk_pagetables(VCPU *vcpu, u32 vaddr);


//xc-baseplatform
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
extern u8 g_vmx_iobitmap_buffer[] __attribute__(( section(".palign_data") ));
		
//VMX guest and host MSR save area buffers
extern u8 g_vmx_msr_area_host_buffers[] __attribute__(( section(".palign_data") ));
extern u8 g_vmx_msr_area_guest_buffers[] __attribute__(( section(".palign_data") ));

//VMX MSR bitmap buffers
//extern u8 g_vmx_msrbitmap_buffers[] __attribute__(( section(".palign_data") ));
extern u8 g_vmx_msrbitmap_buffer[] __attribute__(( section(".palign_data") ));

//initialize CPU state
void xmhf_baseplatform_arch_x86vmx_cpuinitialize(void);

//wake up application processors (cores) in the system
void xmhf_baseplatform_arch_x86vmx_wakeupAPs(void);

//allocate and setup VCPU structure for all the CPUs
void xmhf_baseplatform_arch_x86vmx_allocandsetupvcpus(u32 cpu_vendor);

// routine takes vcpu vmcsfields and stores it in the CPU VMCS 
void xmhf_baseplatform_arch_x86vmx_putVMCS(VCPU *vcpu);

// routine takes CPU VMCS and stores it in vcpu vmcsfields  
void xmhf_baseplatform_arch_x86vmx_getVMCS(VCPU *vcpu);

//--debug: dumpVMCS dumps VMCS contents
void xmhf_baseplatform_arch_x86vmx_dumpVMCS(VCPU *vcpu);

//VMX specific platform reboot
void xmhf_baseplatform_arch_x86vmx_reboot(VCPU *vcpu);

//xc-memprot

//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------
//void xmhf_memprot_arch_x86vmx_initialize(VCPU *vcpu);	//initialize memory protection for a core
void xmhf_memprot_arch_x86vmx_flushmappings(VCPU *vcpu); //flush hardware page table mappings (TLB) 
void xmhf_memprot_arch_x86vmx_setprot(VCPU *vcpu, u64 gpa, u32 prottype); //set protection for a given physical memory address
u32 xmhf_memprot_arch_x86vmx_getprot(VCPU *vcpu, u64 gpa); //get protection for a given physical memory address
u64 xmhf_memprot_arch_x86vmx_get_EPTP(VCPU *vcpu); // get or set EPTP (only valid on Intel)
void xmhf_memprot_arch_x86vmx_set_EPTP(VCPU *vcpu, u64 eptp);

//VMX EPT PML4 table buffers
extern u8 g_vmx_ept_pml4_table_buffers[] __attribute__(( section(".palign_data") ));		

//VMX EPT PDP table buffers
extern u8 g_vmx_ept_pdp_table_buffers[] __attribute__(( section(".palign_data") ));
		
//VMX EPT PD table buffers
extern u8 g_vmx_ept_pd_table_buffers[] __attribute__(( section(".palign_data") ));

//VMX EPT P table buffers
extern u8 g_vmx_ept_p_table_buffers[] __attribute__(( section(".palign_data") ));

//xc-parteventhub
//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------
void xmhf_parteventhub_arch_x86vmx_entry(void);
u32 xmhf_parteventhub_arch_x86vmx_intercept_handler(VCPU *vcpu, struct regs *r);

//XXX: FIX this
//extern u8 * _vmx_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr);
extern void _vmx_putVMCS(VCPU *vcpu);
extern void _vmx_getVMCS(VCPU *vcpu);
extern void _vmx_dumpVMCS(VCPU *vcpu);


//xc-partition
//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------
//initialize partition monitor for a given CPU
//void xmhf_partition_arch_x86vmx_initializemonitor(VCPU *vcpu);

//setup guest OS state for the partition
//void xmhf_partition_arch_x86vmx_setupguestOSstate(VCPU *vcpu);

//start executing the partition and guest OS
//void xmhf_partition_arch_x86vmx_start(VCPU *vcpu);

//low-level HVM start routine (part-x86vmx-sup.S)
u32 __vmx_start_hvm(void);

//set legacy I/O protection for the partition
void xmhf_partition_arch_x86vmx_legacyIO_setprot(VCPU *vcpu, u32 port, u32 size, u32 prottype);

#endif // __ASSEMBLY__


#endif // _XC_X86_H_
