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

// xc-x86vmx.h - XMHF core x86 vmx arch. main header file 
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef _XC_X86VMX_H_
#define _XC_X86VMX_H_

#include <xmhf.h>
#include <xmhf-core.h>

#ifndef __ASSEMBLY__

typedef struct {
  u8 vmx_vmxon_region[PAGE_SIZE_4K];    		
  u8 vmx_vmcs_region[PAGE_SIZE_4K];           
  u8 vmx_msr_area_host_region[2*PAGE_SIZE_4K];		
  u8 vmx_msr_area_guest_region[2*PAGE_SIZE_4K];		
  u64 vmx_msrs[IA32_VMX_MSRCOUNT];  
  u64 vmx_msr_efer;
  u64 vmx_msr_efcr;
} __attribute__((packed)) xc_cpuarchdata_x86vmx_t;
	
	
typedef struct {
  u8 vmx_ept_pml4_table[PAGE_SIZE_4K];												//PML4 table
  u8 vmx_ept_pdp_table[PAGE_SIZE_4K];												//PDP table
  u8 vmx_ept_pd_tables[PAGE_SIZE_4K * PAE_PTRS_PER_PDPT];					//PD tables
  u8 vmx_ept_p_tables[PAGE_SIZE_4K * PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT];	//P tables
} __attribute__ ((packed)) xc_partition_hptdata_x86vmx_t;

typedef struct {
  u8 vmx_iobitmap_region[2*PAGE_SIZE_4K];		//I/O Bitmap area
  u8 vmx_msrbitmaps_region[PAGE_SIZE_4K];		//MSR bitmap area
} __attribute__ ((packed)) xc_partition_trapmaskdata_x86vmx_t;


//------------------------------------------------------
// functions
//------------------------------------------------------

//initialize CPU state
void xmhf_baseplatform_arch_x86vmx_cpuinitialize(void);

//wake up application processors (cores) in the system
void xmhf_baseplatform_arch_x86vmx_wakeupAPs(void);

//allocate and setup VCPU structure for all the CPUs
void xmhf_baseplatform_arch_x86vmx_allocandsetupvcpus(u32 cpu_vendor);

//--debug: dumpVMCS dumps VMCS contents
//void xmhf_baseplatform_arch_x86vmx_dumpVMCS(VCPU *vcpu);

void xmhf_memprot_arch_x86vmx_flushmappings(void); //flush hardware page table mappings (TLB) 
u64 xmhf_memprot_arch_x86vmx_get_EPTP(void); // get or set EPTP (only valid on Intel)
void xmhf_memprot_arch_x86vmx_set_EPTP(u64 eptp);

void xmhf_parteventhub_arch_x86vmx_entry(void);


#endif // __ASSEMBLY__


#endif // _XC_X86VMX_H_
