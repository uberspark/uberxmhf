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

/**
 * XMHF secureloader x86-vmx backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
 
#include <xmhf.h>


void xmhf_sl_arch_sanitize_post_launch(void){
	#ifndef __XMHF_VERIFICATION__
        
        txt_heap_t *txt_heap;
        os_mle_data_t *os_mle_data;

        txt_heap = get_txt_heap();
		printf("SL: txt_heap = 0x%08x\n", (u32)txt_heap);
        /// compensate for special DS here in SL 
        //os_mle_data = get_os_mle_data_start((txt_heap_t*)((u32)txt_heap - sl_baseaddr));
        os_mle_data = get_os_mle_data_start((txt_heap_t*)((u32)txt_heap));
        printf("SL: os_mle_data = 0x%08x\n", (u32)os_mle_data);
        
        // restore pre-SENTER MTRRs that were overwritten for SINIT launch 
        if(!validate_mtrrs(&(os_mle_data->saved_mtrr_state))) {
            printf("SECURITY FAILURE: validate_mtrrs() failed.\n");
            HALT();
        }
        printf("SL: Validated MTRRs\n");

        restore_mtrrs(&(os_mle_data->saved_mtrr_state));
        printf("SL: Restored MTRRs\n");
    
	#endif
}


//"early" DMA protection initialization to setup minimal
//structures to protect a range of physical memory
//return 1 on success 0 on failure
u32 xmhf_dmaprot_arch_x86vmx_earlyinitialize(u64 protectedbuffer_paddr, u32 protectedbuffer_vaddr, u32 protectedbuffer_size, u64 __attribute__((unused))memregionbase_paddr, u32 __attribute__((unused))memregion){
	u32 vmx_eap_vtd_pdpt_paddr, vmx_eap_vtd_pdpt_vaddr, vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr, vmx_eap_vtd_cet_paddr, vmx_eap_vtd_cet_vaddr;

	//(void)memregionbase_paddr;
	//(void)memregion_size;
	
	printf("\nSL: Bootstrapping VMX DMA protection...");
			
	//we use 3 pages for Vt-d bootstrapping
	HALT_ON_ERRORCOND(protectedbuffer_size >= (3*PAGE_SIZE_4K));
		
	vmx_eap_vtd_pdpt_paddr = protectedbuffer_paddr; 
	vmx_eap_vtd_pdpt_vaddr = protectedbuffer_vaddr; 
	vmx_eap_vtd_ret_paddr = protectedbuffer_paddr + PAGE_SIZE_4K; 
	vmx_eap_vtd_ret_vaddr = protectedbuffer_vaddr + PAGE_SIZE_4K; 
	vmx_eap_vtd_cet_paddr = protectedbuffer_paddr + (2*PAGE_SIZE_4K); 
	vmx_eap_vtd_cet_vaddr = protectedbuffer_vaddr + (2*PAGE_SIZE_4K); 
			
	return vmx_eap_initialize(vmx_eap_vtd_pdpt_paddr, vmx_eap_vtd_pdpt_vaddr, 0, 0,	0, 0, vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr,	vmx_eap_vtd_cet_paddr, vmx_eap_vtd_cet_vaddr, 1);
}


void xmhf_sl_arch_early_dmaprot_init(u32 membase, u32 size){

		{
			u64 protectedbuffer_paddr;
			u32 protectedbuffer_vaddr;
			u32 protectedbuffer_size;
			u64 memregionbase_paddr;
			u32 memregion_size;

				protectedbuffer_paddr = __TARGET_BASE_SL + 0x100000;
				protectedbuffer_vaddr = protectedbuffer_paddr;
				protectedbuffer_size = (3 * PAGE_SIZE_4K);

			memregionbase_paddr = membase;
			memregion_size = size;

			printf("SL: Initializing DMA protections...\n");
			

			if(!xmhf_dmaprot_arch_x86vmx_earlyinitialize(protectedbuffer_paddr,
				protectedbuffer_vaddr, protectedbuffer_size,
				memregionbase_paddr, memregion_size)){
				printf("SL: Fatal, could not initialize DMA protections. Halting!\n");
				HALT();	
			}
			
			printf("SL: Initialized DMA protections successfully\n");
		
		}

}

