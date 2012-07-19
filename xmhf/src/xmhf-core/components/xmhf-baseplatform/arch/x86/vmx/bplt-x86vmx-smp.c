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

/*
 * EMHF base platform component interface, x86 vmx backend
 * smp related functions
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>

//allocate and setup VCPU structure for all the CPUs
void emhf_baseplatform_arch_x86vmx_allocandsetupvcpus(u32 cpu_vendor){
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
	vcpu->vmx_vaddr_iobitmap = (u32)g_vmx_iobitmap_buffer; 
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

//wake up application processors (cores) in the system
void emhf_baseplatform_arch_x86vmx_wakeupAPs(void){
	//step-1: setup AP boot-strap code at in the desired physical memory location 
	//note that we need an address < 1MB since the APs are woken up in real-mode
	//we choose 0x10000 physical or 0x1000:0x0000 logical
    {
        _ap_cr3_value = read_cr3();
        _ap_cr4_value = read_cr4();
        memcpy((void *)0x10000, (void *)_ap_bootstrap_start, (u32)_ap_bootstrap_end - (u32)_ap_bootstrap_start + 1);
    }

#if defined (__DRTM_DMA_PROTECTION__)	
    //step-2: wake up the APs sending the INIT-SIPI-SIPI sequence as per the
    //MP protocol. Use the APIC for IPI purposes.
    if(!txt_is_launched()) { // XXX TODO: Do actual GETSEC[WAKEUP] in here?
        printf("\nBSP: Using APIC to awaken APs...");
        emhf_baseplatform_arch_x86_wakeupAPs();
        printf("\nBSP: APs should be awake.");
    }else{
		//we ran SENTER, so do a GETSEC[WAKEUP]
        txt_heap_t *txt_heap;
        os_mle_data_t *os_mle_data;
        mle_join_t *mle_join;
        sinit_mle_data_t *sinit_mle_data;
        os_sinit_data_t *os_sinit_data;

        /* sl.c unity-maps 0xfed00000 for 2M so these should work fine */
        txt_heap = get_txt_heap();
        //printf("\ntxt_heap = 0x%08x", (u32)txt_heap);
        os_mle_data = get_os_mle_data_start(txt_heap);
        (void)os_mle_data;
        //printf("\nos_mle_data = 0x%08x", (u32)os_mle_data);
        sinit_mle_data = get_sinit_mle_data_start(txt_heap);
        //printf("\nsinit_mle_data = 0x%08x", (u32)sinit_mle_data);
        os_sinit_data = get_os_sinit_data_start(txt_heap);
        //printf("\nos_sinit_data = 0x%08x", (u32)os_sinit_data);
            
        // Start APs.  Choose wakeup mechanism based on
        // capabilities used. MLE Dev Guide says MLEs should
        // support both types of Wakeup mechanism. 

        // We are jumping straight into the 32-bit portion of the
        // unity-mapped trampoline that starts at 64K
        // physical. Without SENTER, or with AMD, APs start in
        // 16-bit mode.  We get to skip that. 
        printf("\nBSP: _mle_join_start = 0x%08x, _ap_bootstrap_start = 0x%08x",
			(u32)_mle_join_start, (u32)_ap_bootstrap_start);

        // enable SMIs on BSP before waking APs (which will enable them on APs)
        // because some SMM may take immediate SMI and hang if AP gets in first 
        //printf("Enabling SMIs on BSP\n");
        //__getsec_smctrl();
                
        // MLE Join structure constructed in runtimesup.S. Debug print. 
        mle_join = (mle_join_t*)((u32)_mle_join_start - (u32)_ap_bootstrap_start + 0x10000); // XXX magic number
        printf("\nBSP: mle_join.gdt_limit = %x", mle_join->gdt_limit);
        printf("\nBSP: mle_join.gdt_base = %x", mle_join->gdt_base);
        printf("\nBSP: mle_join.seg_sel = %x", mle_join->seg_sel);
        printf("\nBSP: mle_join.entry_point = %x", mle_join->entry_point);                

        write_priv_config_reg(TXTCR_MLE_JOIN, (uint64_t)(unsigned long)mle_join);

        if (os_sinit_data->capabilities.rlp_wake_monitor) {
            printf("\nBSP: joining RLPs to MLE with MONITOR wakeup");
            printf("\nBSP: rlp_wakeup_addr = 0x%x", sinit_mle_data->rlp_wakeup_addr);
            *((uint32_t *)(unsigned long)(sinit_mle_data->rlp_wakeup_addr)) = 0x01;
        }else {
            printf("\nBSP: joining RLPs to MLE with GETSEC[WAKEUP]");
            __getsec_wakeup();
            printf("\nBSP: GETSEC[WAKEUP] completed");
        }
		
	}
	
#else //!__DRTM_DMA_PROTECTION__
        printf("\nBSP: Using APIC to awaken APs...");
        emhf_baseplatform_arch_x86_wakeupAPs();
        printf("\nBSP: APs should be awake.");

#endif 
	
}
