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

// EMHF memory protection component
// intel VMX arch. backend implementation
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf-core.h> 
#include <xc-x86.h>
#include <xc-x86vmx.h>


// initialize memory protection structures for a given core (vcpu)
static void xmhf_memprot_arch_x86vmx_initialize(xc_partition_hptdata_x86vmx_t *eptdata){
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (1 <<1) | (1 << 5)) );
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VPID, 1);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_FULL, (hva2spa((void*)eptdata->vmx_ept_pml4_table) | 0x1E) );
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_HIGH, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) & ~(1 << 15) & ~(1 << 16)) );
}

//flush hardware page table mappings (TLB) 
void xmhf_memprot_arch_x86vmx_flushmappings(void){
  __vmx_invept(VMX_INVEPT_SINGLECONTEXT, 
          (u64)xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_EPT_POINTER_FULL));
}


u64 xmhf_memprot_arch_x86vmx_get_EPTP(void)
{
  return
    ((u64)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_EPT_POINTER_HIGH)) << 32)
    | (u64)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_EPT_POINTER_FULL));
}
void xmhf_memprot_arch_x86vmx_set_EPTP(u64 eptp)
{
  xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_FULL, (u32)eptp);
  xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_HIGH, (u32)(eptp >> 32));
}


//get protection for a given physical memory address
u32 xmhf_memprot_arch_x86vmx_getprot(xc_partition_hptdata_x86vmx_t *eptdata, u64 gpa){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;	//grab page frame number
  u64 *pt = (u64 *)eptdata->vmx_ept_p_tables;
  u64 entry = pt[pfn];
  u32 prottype;
  
  if(! (entry & 0x1) ){
	prottype = MEMP_PROT_NOTPRESENT;
	return prottype;
  }
 
  prottype = MEMP_PROT_PRESENT;
  
  if( entry & 0x2 )
	prottype |= MEMP_PROT_READWRITE;
  else
	prottype |= MEMP_PROT_READONLY;

  if( entry & 0x4 )
	prottype |= MEMP_PROT_EXECUTE;
  else
	prottype |= MEMP_PROT_NOEXECUTE;

  return prottype;
}

//======================================================================
// global interfaces (functions) exported by this component

void xmhf_memprot_arch_initialize(xc_cpu_t *xc_cpu, xc_partition_t *xc_partition){
	xc_partition_hptdata_x86vmx_t *eptdata = (xc_partition_hptdata_x86vmx_t *)xc_partition->hptdata;
	
	xmhf_memprot_arch_x86vmx_initialize(eptdata);
}

//set protection for a given physical memory address
//void xmhf_memprot_arch_setprot(context_desc_t context_desc, xc_partition_t *xc_partition, u64 gpa, u32 prottype){
//	xc_partition_hptdata_x86vmx_t *eptdata = (xc_partition_hptdata_x86vmx_t *)xc_partition->hptdata;
//
//	xmhf_memprot_arch_x86vmx_setprot(eptdata, gpa, prottype);
//}

//get protection for a given physical memory address
u32 xmhf_memprot_arch_getprot(context_desc_t context_desc, xc_partition_t *xc_partition, u64 gpa){
	xc_partition_hptdata_x86vmx_t *eptdata = (xc_partition_hptdata_x86vmx_t *)xc_partition->hptdata;

	return xmhf_memprot_arch_x86vmx_getprot(eptdata, gpa);
}

//flush hardware page table mappings (TLB) 
void xmhf_memprot_arch_flushmappings(context_desc_t context_desc){
		xc_cpu_t *xc_cpu = (xc_cpu_t *)context_desc.cpu_desc.xc_cpu;
		
		xmhf_smpguest_arch_x86vmx_quiesce(xc_cpu);
		xmhf_memprot_arch_x86vmx_flushmappings();
		xmhf_smpguest_arch_x86vmx_endquiesce(xc_cpu);
}


void xmhf_memprot_arch_setsingularhpt(u64 hpt){
		u32 i;
		
		printf("\n%s: starting...", __FUNCTION__);
        for( i=0 ; i<g_xc_cpu_count; i++ )  {
				xmhf_memprot_arch_x86vmx_set_EPTP(hpt);

			printf("\n CPU %02x: set HPT to %x",  i, (u32)hpt);
        }
		printf("\n%s: done.", __FUNCTION__);
}

//get HPT root pointer
u64 xmhf_memprot_arch_getHPTroot(context_desc_t context_desc){
	return xmhf_memprot_arch_x86vmx_get_EPTP();
}


//set HPT entry
void xmhf_memprot_arch_hpt_setentry(context_desc_t context_desc, xc_partition_t *xc_partition, u64 hpt_paddr, u64 entry){
	xc_partition_hptdata_x86vmx_t *eptdata = (xc_partition_hptdata_x86vmx_t *)xc_partition->hptdata;
	
	u64 *hpt = (u64 *)eptdata->vmx_ept_p_tables;
	u32 hpt_index = (u32)hpt_paddr / PAGE_SIZE_4K;
	
	hpt[hpt_index] = entry;

	return;
}
