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
void xmhf_baseplatform_arch_x86vmx_allocandsetupvcpus(u32 cpu_vendor){
  u32 i;
  VCPU *vcpu;

  for(i=0; i < g_midtable_numentries; i++){
	//allocate VCPU structure
	vcpu = (VCPU *)((hva_t)g_vcpubuffers + (hva_t)(i * SIZE_STRUCT_VCPU));

    #ifndef __XMHF_VERIFICATION__
    memset((void *)vcpu, 0, sizeof(VCPU));
    #endif

    vcpu->cpu_vendor = cpu_vendor;

	//allocate runtime stack
#ifdef __AMD64__
    vcpu->rsp = ((hva_t)g_cpustacks + (i * RUNTIME_STACK_SIZE)) + RUNTIME_STACK_SIZE;
#elif defined(__I386__)
    vcpu->esp = ((hva_t)g_cpustacks + (i * RUNTIME_STACK_SIZE)) + RUNTIME_STACK_SIZE;
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */

    //allocate VMXON memory region
    vcpu->vmx_vmxonregion_vaddr = ((hva_t)g_vmx_vmxon_buffers + (i * PAGE_SIZE_4K)) ;
    #ifndef __XMHF_VERIFICATION__
    memset((void *)vcpu->vmx_vmxonregion_vaddr, 0, PAGE_SIZE_4K);
    #endif

	//allocate VMCS memory region
	vcpu->vmx_vmcs_vaddr = ((hva_t)g_vmx_vmcs_buffers + (i * PAGE_SIZE_4K)) ;
    #ifndef __XMHF_VERIFICATION__
    memset((void *)vcpu->vmx_vmcs_vaddr, 0, PAGE_SIZE_4K);
	#endif

	//allocate VMX IO bitmap region
	vcpu->vmx_vaddr_iobitmap = (hva_t)g_vmx_iobitmap_buffer;
	#ifndef __XMHF_VERIFICATION__
	memset( (void *)vcpu->vmx_vaddr_iobitmap, 0, (2*PAGE_SIZE_4K));
	#endif

	//allocate VMX guest and host MSR save areas
	vcpu->vmx_vaddr_msr_area_host = ((hva_t)g_vmx_msr_area_host_buffers + (i * (2*PAGE_SIZE_4K))) ;
	#ifndef __XMHF_VERIFICATION__
	memset( (void *)vcpu->vmx_vaddr_msr_area_host, 0, (2*PAGE_SIZE_4K));
	#endif
	vcpu->vmx_vaddr_msr_area_guest = ((hva_t)g_vmx_msr_area_guest_buffers + (i * (2*PAGE_SIZE_4K))) ;
	#ifndef __XMHF_VERIFICATION__
	memset( (void *)vcpu->vmx_vaddr_msr_area_guest, 0, (2*PAGE_SIZE_4K));
	#endif

	//allocate VMX MSR bitmap region
	vcpu->vmx_vaddr_msrbitmaps = ((hva_t)g_vmx_msrbitmap_buffers + (i * PAGE_SIZE_4K)) ;
	#ifndef __XMHF_VERIFICATION__
	memset( (void *)vcpu->vmx_vaddr_msrbitmaps, 0, PAGE_SIZE_4K);
	#endif

	//allocate EPT paging structures
	#ifdef __NESTED_PAGING__
	{
		vcpu->vmx_vaddr_ept_pml4_table = ((hva_t)g_vmx_ept_pml4_table_buffers + (i * P4L_NPLM4T * PAGE_SIZE_4K));
		vcpu->vmx_vaddr_ept_pdp_table = ((hva_t)g_vmx_ept_pdp_table_buffers + (i * P4L_NPDPT * PAGE_SIZE_4K));
		vcpu->vmx_vaddr_ept_pd_tables = ((hva_t)g_vmx_ept_pd_table_buffers + (i * P4L_NPDT * PAGE_SIZE_4K));
		vcpu->vmx_vaddr_ept_p_tables = ((hva_t)g_vmx_ept_p_table_buffers + (i * P4L_NPT * PAGE_SIZE_4K));
	}
	#endif

	//other VCPU data such as LAPIC id, SIPI vector and receive indication
    vcpu->id = g_midtable[i].cpu_lapic_id;
    vcpu->idx = i;
    vcpu->sipivector = 0;
    vcpu->sipireceived = 0;

	//map LAPIC to VCPU in midtable
    g_midtable[i].vcpu_vaddr_ptr = (hva_t)vcpu;
  }
}

//wake up application processors (cores) in the system
void xmhf_baseplatform_arch_x86vmx_wakeupAPs(void){
	//step-1: setup AP boot-strap code at in the desired physical memory location
	//note that we need an address < 1MB since the APs are woken up in real-mode
	//we choose 0x10000 physical or 0x1000:0x0000 logical
    {
        _ap_cr3_value = read_cr3();
        _ap_cr4_value = read_cr4();
        #ifndef __XMHF_VERIFICATION__
        memcpy((void *)0x10000, (void *)_ap_bootstrap_start, (uintptr_t)_ap_bootstrap_end - (uintptr_t)_ap_bootstrap_start + 1);
        #endif
    }

#if defined (__DRT__)
    //step-2: wake up the APs sending the INIT-SIPI-SIPI sequence as per the
    //MP protocol. Use the APIC for IPI purposes.
    if(!txt_is_launched()) { // XXX TODO: Do actual GETSEC[WAKEUP] in here?
        printf("BSP: Using APIC to awaken APs...\n");
        xmhf_baseplatform_arch_x86_wakeupAPs();
        printf("BSP: APs should be awake.\n");
    }else{
		//we ran SENTER, so do a GETSEC[WAKEUP]
        txt_heap_t *txt_heap;
        os_mle_data_t *os_mle_data;
        mle_join_t *mle_join;
        sinit_mle_data_t *sinit_mle_data;
        os_sinit_data_t *os_sinit_data;

        // sl.c unity-maps 0xfed00000 for 2M so these should work fine
        #ifndef __XMHF_VERIFICATION__
        txt_heap = get_txt_heap();
        //printf("txt_heap = 0x%08lx\n", (uintptr_t)txt_heap);
        os_mle_data = get_os_mle_data_start(txt_heap);
        (void)os_mle_data;
        //printf("os_mle_data = 0x%08lx\n", (uintptr_t)os_mle_data);
        sinit_mle_data = get_sinit_mle_data_start(txt_heap);
        //printf("sinit_mle_data = 0x%08lx\n", (uintptr_t)sinit_mle_data);
        os_sinit_data = get_os_sinit_data_start(txt_heap);
        //printf("os_sinit_data = 0x%08lx\n", (uintptr_t)os_sinit_data);
	#endif

        // Start APs.  Choose wakeup mechanism based on
        // capabilities used. MLE Dev Guide says MLEs should
        // support both types of Wakeup mechanism.

        // We are jumping straight into the 32-bit portion of the
        // unity-mapped trampoline that starts at 64K
        // physical. Without SENTER, or with AMD, APs start in
        // 16-bit mode.  We get to skip that.
        printf("BSP: _mle_join_start = 0x%08lx, _ap_bootstrap_start = 0x%08lx\n",
			(uintptr_t)_mle_join_start, (uintptr_t)_ap_bootstrap_start);

        // enable SMIs on BSP before waking APs (which will enable them on APs)
        // because some SMM may take immediate SMI and hang if AP gets in first
        //printf("Enabling SMIs on BSP\n");
        //__getsec_smctrl();

        // MLE Join structure constructed in runtimesup.S. Debug print.
        #ifndef __XMHF_VERIFICATION__
        mle_join = (mle_join_t*)((uintptr_t)_mle_join_start - (uintptr_t)_ap_bootstrap_start + 0x10000); // XXX magic number
        #endif
        //printf("BSP: mle_join.gdt_limit = 0x%08x\n", mle_join->gdt_limit);
        //printf("BSP: mle_join.gdt_base = 0x%08x\n", mle_join->gdt_base);
        //printf("BSP: mle_join.seg_sel = 0x%08x\n", mle_join->seg_sel);
        //printf("BSP: mle_join.entry_point = 0x%08x\n", mle_join->entry_point);

	#ifndef __XMHF_VERIFICATION__
        write_priv_config_reg(TXTCR_MLE_JOIN, (uint64_t)(unsigned long)mle_join);

        if (os_sinit_data->capabilities.rlp_wake_monitor) {
            printf("BSP: joining RLPs to MLE with MONITOR wakeup\n");
            printf("BSP: rlp_wakeup_addr = 0x%08x\n", sinit_mle_data->rlp_wakeup_addr);
            *((uint32_t *)(unsigned long)(sinit_mle_data->rlp_wakeup_addr)) = 0x01;
        }else {
            printf("BSP: joining RLPs to MLE with GETSEC[WAKEUP]\n");
            __getsec_wakeup();
            printf("BSP: GETSEC[WAKEUP] completed\n");
        }
	#endif


	}

#else //!__DRT__
        printf("BSP: Using APIC to awaken APs...\n");
        xmhf_baseplatform_arch_x86_wakeupAPs();
        printf("BSP: APs should be awake.\n");

#endif


}
