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

static u8 vtd_ret_table[PAGE_SIZE_4K]; //4KB Vt-d Root-Entry table
//static VTD_DRHD vtd_drhd[VTD_MAX_DRHD];
//static u32 vtd_num_drhd=0;	//total number of DMAR h/w units

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


/*//"early" DMA protection initialization to setup minimal
//structures to protect a range of physical memory
//return 1 on success 0 on failure
u32 xmhf_sl_arch_x86vmx_earlyinitialize(u64 protectedbuffer_paddr, u32 protectedbuffer_vaddr, u32 protectedbuffer_size, u64 __attribute__((unused))memregionbase_paddr, u32 __attribute__((unused))memregion){
	u32 vmx_eap_vtd_pdpt_paddr, vmx_eap_vtd_pdpt_vaddr;
	u32 vmx_eap_vtd_ret_paddr, vmx_eap_vtd_ret_vaddr;
	u32 vmx_eap_vtd_cet_paddr, vmx_eap_vtd_cet_vaddr;

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
}*/


//protect a given physical range of memory (membase to membase+size)
//using VT-d PMRs
//return true if everything went fine, else false
static bool vtd_dmaprotect(u32 membase, u32 size){
	u32 i;
	u32 vtd_dmar_table_physical_address=0;
	vtd_drhd_handle_t vtd_drhd_maxhandle;
	
#ifndef __XMHF_VERIFICATION__	

	printf("\n%s: size=%08x", __FUNCTION__, size);
	
	//scan for available DRHD units in the platform
	if(!_vtd_scanfor_drhd_units(&vtd_drhd_maxhandle, &vtd_dmar_table_physical_address))
		return false;

	//zero out RET; will be used to prevent DMA reads and writes 
	//for the entire system
	memset((void *)&vtd_ret_table, 0, sizeof(vtd_ret_table));


	
	//initialize all DRHD units
	for(i=0; i < vtd_num_drhd; i++){
		printf("\n%s: Setting up DRHD unit %u...", __FUNCTION__, i);
		
		if(!_vtd_drhd_initialize(&vtd_drhd[i]) )
			return false;

		//setup blanket (full system) DMA protection using VT-d translation
		//we just employ the RET and ensure that every entry in the RET is 0 
		//which means that the DRHD will
		//not allow any DMA requests for PCI bus 0-255 
		//(Sec 3.3.2, VT-d Spec. v1.2)
	
		//set DRHD root entry table
		if(!_vtd_drhd_set_root_entry_table(&vtd_drhd[i], (u8 *)&vtd_ret_table))
			return false;
	
		//invalidate caches
		if(!_vtd_drhd_invalidatecaches(&vtd_drhd[i]))
			return false;

		//enable VT-d translation
		_vtd_drhd_enable_translation(&vtd_drhd[i]);
	
		//disable PMRs now (since DMA protection is active via translation)
		_vtd_drhd_disable_pmr(&vtd_drhd[i]);
		
		//set PMR low base and limit to cover SL+runtime
		_vtd_drhd_set_plm_base_and_limit(&vtd_drhd[i], (u32)PAGE_ALIGN_2M(membase), (u32)(PAGE_ALIGN_2M(membase) + PAGE_ALIGN_UP2M(size)) );
		
		//set PMR high base and limit to cover SL+runtime
		_vtd_drhd_set_phm_base_and_limit(&vtd_drhd[i], (u64)PAGE_ALIGN_2M(membase), (u64)(PAGE_ALIGN_2M(membase) + PAGE_ALIGN_UP2M(size)) );
		
		//enable PMRs
		_vtd_drhd_enable_pmr(&vtd_drhd[i]);
		
		//invalidate caches
		if(!_vtd_drhd_invalidatecaches(&vtd_drhd[i]))
			return false;

		//disable translation (now that PMRs are active and protect SL+runtime)
		_vtd_drhd_disable_translation(&vtd_drhd[i]);
	
	}

#endif //__XMHF_VERIFICATION__

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup 
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	xmhf_baseplatform_arch_flat_writeu32(vtd_dmar_table_physical_address, 0UL);

	//success
	printf("\n%s: success, leaving...", __FUNCTION__);

	return true;
}


void xmhf_sl_arch_early_dmaprot_init(u32 membase, u32 size){
		/*(void)membase;
		(void)size;

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
			

			if(!xmhf_sl_arch_x86vmx_earlyinitialize(protectedbuffer_paddr,
				protectedbuffer_vaddr, protectedbuffer_size,
				memregionbase_paddr, memregion_size)){
				printf("SL: Fatal, could not initialize DMA protections. Halting!\n");
				HALT();	
			}
			
			printf("SL: Initialized DMA protections successfully\n");
		
		}*/
		
		printf("SL: Initializing DMA protections...\n");
		
		if(!vtd_dmaprotect(membase, size)){
			printf("Warning: SL: Fatal, could not initialize DMA protections. Moving on regardless...\n");
			//HALT();	
		}else{
			printf("SL: Initialized DMA protections successfully\n");
		}
	
}

