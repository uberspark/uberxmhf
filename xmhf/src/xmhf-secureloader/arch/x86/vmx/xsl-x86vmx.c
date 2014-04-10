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
#include <xmhf-sl.h>

#include "platform/x86pc/include/common/_multiboot.h"		//multiboot
#include "cpu/x86/include/common/_processor.h"  	//CPU
//#include "cpu/x86/include/common/_msr.h"        	//model specific registers
#include "cpu/x86/include/common/_paging.h"     	//MMU
//#include "cpu/x86/include/common/_io.h"         	//legacy I/O
//#include "cpu/x86/include/common/_apic.h"       	//APIC
//#include "cpu/x86/include/amd/svm/_svm.h"        	//SVM extensions
//#include "cpu/x86/include/intel/vmx/_vmx.h"			//VMX extensions
#include "cpu/x86/include/intel/txt/_txt.h"			//Trusted eXecution Technology (SENTER support)
//#include "platform/x86pc/include/common/_pci.h"        	//PCI bus glue
//#include "platform/x86pc/include/common/_acpi.h"			//ACPI glue
//#include "platform/x86pc/include/amd/dev/_svm_eap.h"		//SVM DMA protection
#include "platform/x86pc/include/intel/vtd/vtd.h"		//VMX DMA protection
#include "platform/x86pc/include/common/_memaccess.h"	//platform memory access


/**
 * XMHF secureloader x86-vmx entry module
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
 

/* sl stack, this is just a placeholder and ensures that the linker
 actually "allocates" the stack up until 0x10000*/
u8 _sl_stack[1] __attribute__((section(".sl_stack")));

__attribute__((naked)) void _xmhf_sl_entry(void) __attribute__(( section(".sl_header") )) __attribute__(( align(4096) )){
	
asm volatile ( 	".global _mle_page_table_start \r\n"
			   "_mle_page_table_start:\r\n"
			   ".fill 4096, 1, 0 \r\n" /* first page*/
			   //".global g_sl_protected_dmabuffer\r\n"
				//"g_sl_protected_dmabuffer:\r\n"
				".fill 4096, 1, 0 \r\n" /* second page*/
				".fill 4096, 1, 0 \r\n" /* third page*/
				".global _mle_page_table_end \r\n"
				"_mle_page_table_end: \r\n"
				".global _mle_hdr \r\n"
				"_mle_hdr:\r\n"
				".fill 0x80, 1, 0x90\r\n" /* XXX TODO just a guess; should really be sizeof(mle_hdr_t) */
				".global _sl_start \r\n"
				"_sl_start: \r\n"
			    "movw %%ds, %%ax \r\n" 
				"movw %%ax, %%fs \r\n"
				"movw %%ax, %%gs \r\n"
			    "movw %%ax, %%ss \r\n"
			    "movl $0x10010000, %%esp \r\n" /* XXX TODO Get rid of magic number*/
			    :
			    :
		);

		xmhf_sl_main();

}

static u8 vtd_ret_table[PAGE_SIZE_4K]; //4KB Vt-d Root-Entry table

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


//protect a given physical range of memory (membase to membase+size)
//using VT-d PMRs
//return true if everything went fine, else false
static bool vtd_dmaprotect(u32 membase, u32 size){
	vtd_drhd_handle_t drhd_handle;
	u32 vtd_dmar_table_physical_address=0;
	vtd_drhd_handle_t vtd_drhd_maxhandle;
	
#ifndef __XMHF_VERIFICATION__	

	printf("\n%s: size=%08x", __FUNCTION__, size);
	
	//scan for available DRHD units in the platform
	if(!vtd_scanfor_drhd_units(&vtd_drhd_maxhandle, &vtd_dmar_table_physical_address))
		return false;

	//zero out RET; will be used to prevent DMA reads and writes 
	//for the entire system
	memset((void *)&vtd_ret_table, 0, sizeof(vtd_ret_table));


	
	//initialize all DRHD units
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
		printf("\n%s: Setting up DRHD unit %u...", __FUNCTION__, drhd_handle);
		
		if(!vtd_drhd_initialize(drhd_handle) )
			return false;

		//setup blanket (full system) DMA protection using VT-d translation
		//we just employ the RET and ensure that every entry in the RET is 0 
		//which means that the DRHD will
		//not allow any DMA requests for PCI bus 0-255 
		//(Sec 3.3.2, VT-d Spec. v1.2)
	
		//set DRHD root entry table
		if(!vtd_drhd_set_root_entry_table(drhd_handle, (u8 *)&vtd_ret_table))
			return false;
	
		//invalidate caches
		if(!vtd_drhd_invalidatecaches(drhd_handle))
			return false;

		//enable VT-d translation
		vtd_drhd_enable_translation(drhd_handle);
	
		//disable PMRs now (since DMA protection is active via translation)
		vtd_drhd_disable_pmr(drhd_handle);
		
		//set PMR low base and limit to cover SL+runtime
		vtd_drhd_set_plm_base_and_limit(drhd_handle, (u32)PAGE_ALIGN_2M(membase), (u32)(PAGE_ALIGN_2M(membase) + PAGE_ALIGN_UP2M(size)) );
		
		//set PMR high base and limit to cover SL+runtime
		vtd_drhd_set_phm_base_and_limit(drhd_handle, (u64)PAGE_ALIGN_2M(membase), (u64)(PAGE_ALIGN_2M(membase) + PAGE_ALIGN_UP2M(size)) );
		
		//enable PMRs
		vtd_drhd_enable_pmr(drhd_handle);
		
		//invalidate caches
		if(!vtd_drhd_invalidatecaches(drhd_handle))
			return false;

		//disable translation (now that PMRs are active and protect SL+runtime)
		vtd_drhd_disable_translation(drhd_handle);
	
	}

#endif //__XMHF_VERIFICATION__

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup 
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	xmhfhw_sysmemaccess_writeu32(vtd_dmar_table_physical_address, 0UL);

	//success
	printf("\n%s: success, leaving...", __FUNCTION__);

	return true;
}


void xmhf_sl_arch_early_dmaprot_init(u32 membase, u32 size){
		printf("SL: Initializing DMA protections...\n");
		
		if(!vtd_dmaprotect(membase, size)){
			printf("SL: Fatal, could not initialize DMA protections. Halting!\n");
			HALT();	
		}else{
			printf("SL: Initialized DMA protections successfully\n");
		}
}

