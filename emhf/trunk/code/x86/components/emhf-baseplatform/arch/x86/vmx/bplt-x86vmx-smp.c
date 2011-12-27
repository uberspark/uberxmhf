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

/*
 * EMHF base platform component interface, x86 vmx backend
 * smp related functions
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <emhf.h>

//allocate and setup VCPU structure for all the CPUs
void emhf_arch_x86vmx_baseplatform_allocandsetupvcpus(u32 cpu_vendor){
  u32 i;
  VCPU *vcpu;
  
  for(i=0; i < g_midtable_numentries; i++){
    //allocate VCPU structure
	vcpu = (VCPU *)((u32)g_vcpubuffers + (u32)(i * SIZE_STRUCT_VCPU));
    memset((void *)vcpu, 0, sizeof(VCPU));
    
    vcpu->cpu_vendor = cpu_vendor;
    
	//allocate runtime stack
    vcpu->esp = ((u32)g_cpustacks + (i * RUNTIME_STACK_SIZE)) + RUNTIME_STACK_SIZE;    

    //allocate VMXON memory region
    vcpu->vmx_vmxonregion_vaddr = ((u32)g_vmx_vmxon_buffers + (i * PAGE_SIZE_4K)) ;
    memset((void *)vcpu->vmx_vmxonregion_vaddr, 0, PAGE_SIZE_4K);
    
	//allocate VMCS memory region
	vcpu->vmx_vmcs_vaddr = ((u32)g_vmx_vmcs_buffers + (i * PAGE_SIZE_4K)) ;
    memset((void *)vcpu->vmx_vmcs_vaddr, 0, PAGE_SIZE_4K);
		
	//allocate VMX IO bitmap region
	vcpu->vmx_vaddr_iobitmap = ((u32)g_vmx_iobitmap_buffers + (i * (2*PAGE_SIZE_4K))) ; 
	memset( (void *)vcpu->vmx_vaddr_iobitmap, 0, (2*PAGE_SIZE_4K));
		
	//allocate VMX guest and host MSR save areas
	vcpu->vmx_vaddr_msr_area_host = ((u32)g_vmx_msr_area_host_buffers + (i * (2*PAGE_SIZE_4K))) ; 
	memset( (void *)vcpu->vmx_vaddr_msr_area_host, 0, (2*PAGE_SIZE_4K));
	vcpu->vmx_vaddr_msr_area_guest = ((u32)g_vmx_msr_area_guest_buffers + (i * (2*PAGE_SIZE_4K))) ; 
	memset( (void *)vcpu->vmx_vaddr_msr_area_guest, 0, (2*PAGE_SIZE_4K));

	//allocate VMX MSR bitmap region
	vcpu->vmx_vaddr_msrbitmaps = ((u32)g_vmx_msrbitmap_buffers + (i * PAGE_SIZE_4K)) ; 
	memset( (void *)vcpu->vmx_vaddr_msrbitmaps, 0, PAGE_SIZE_4K);
		
	//allocate EPT paging structures
	#ifdef __NESTED_PAGING__		
	{
			vcpu->vmx_vaddr_ept_pml4_table = ((u32)g_vmx_ept_pml4_table_buffers + (i * PAGE_SIZE_4K));
			vcpu->vmx_vaddr_ept_pdp_table = ((u32)g_vmx_ept_pdp_table_buffers + (i * PAGE_SIZE_4K));  
			vcpu->vmx_vaddr_ept_pd_tables = ((u32)g_vmx_ept_pd_table_buffers + (i * (PAGE_SIZE_4K*4))); 		
			vcpu->vmx_vaddr_ept_p_tables = ((u32)g_vmx_ept_p_table_buffers + (i * (PAGE_SIZE_4K*2048))); 
	}
	#endif

	//other VCPU data such as LAPIC id, SIPI vector and receive indication
    vcpu->id = g_midtable[i].cpu_lapic_id;
    vcpu->idx = i;
    vcpu->sipivector = 0;
    vcpu->sipireceived = 0;

	//map LAPIC to VCPU in midtable
    g_midtable[i].vcpu_vaddr_ptr = (u32)vcpu;	
  }
}
