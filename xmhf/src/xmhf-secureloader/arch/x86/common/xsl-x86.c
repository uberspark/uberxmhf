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
 * sl-x86.c
 * EMHF secure loader x86 arch. backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
 
#include <xmhf.h>
#include <xmhf-sl.h>
#include <xmhf-sl-arch.h>

#include "cpu/x86/include/common/_processor.h"  	//CPU
#include "cpu/x86/include/common/_paging.h"     	//MMU
#include "platform/x86pc/include/common/_acpi.h"			//ACPI glue
#include "platform/x86pc/include/common/_memaccess.h"	//platform memory access

//we only have confidence in the runtime's expected value here in the SL
//static INTEGRITY_MEASUREMENT_VALUES g_sl_gold /* __attribute__(( section("") )) */ = {
//    .sha_runtime = ___RUNTIME_INTEGRITY_HASH___,
//    .sha_slabove64K = BAD_INTEGRITY_HASH,
//    .sha_slbelow64K = BAD_INTEGRITY_HASH
//};


/* XXX TODO Read PCR values and sanity-check that DRTM was successful
 * (i.e., measurements match expectations), and integrity-check the
 * runtime. */
/* Note: calling this *before* paging is enabled is important. */
/*bool xmhf_sl_arch_integrity_check(u8* runtime_base_addr, size_t runtime_len) {
    int ret;
    u32 locality = EMHF_TPM_LOCALITY_PREF; 
    tpm_pcr_value_t pcr17, pcr18;    
	(void)g_sl_gold;

    print_hex("SL: Golden Runtime SHA-1: ", g_sl_gold.sha_runtime, SHA_DIGEST_LENGTH);

    printf("\nSL: CR0 %08lx, CD bit %ld", read_cr0(), read_cr0() & CR0_CD);
    hashandprint("SL: Computed Runtime SHA-1: ",
                 runtime_base_addr, runtime_len);    

    if(xmhf_tpm_open_locality(locality)) {
        printf("SL: FAILED to open TPM locality %d\n", locality);
        return false;
    }
    
    if((ret = tpm_pcr_read(locality, 17, &pcr17)) != TPM_SUCCESS) {
        printf("TPM: ERROR: tpm_pcr_read FAILED with error code 0x%08x\n", ret);
        return false;
    }
    print_hex("PCR-17: ", &pcr17, sizeof(pcr17));

    if((ret = tpm_pcr_read(locality, 18, &pcr18)) != TPM_SUCCESS) {
        printf("TPM: ERROR: tpm_pcr_read FAILED with error code 0x%08x\n", ret);
        return false;
    }
    print_hex("PCR-18: ", &pcr18, sizeof(pcr18));    

    // free TPM so that OS driver works as expected 
    xmhf_tpm_arch_deactivate_all_localities();
    
    return true;    
}
*/

void xmhf_sl_arch_xfer_control_to_runtime(RPB *rpb){
	u32 ptba;	//page table base address

	printf("Transferring control to runtime\n");

	#ifndef __XMHF_VERIFICATION__
	//transfer control to runtime and never return
	xmhf_sl_arch_x86_invoke_runtime_entrypoint(rpb->XtVmmEntryPoint, (rpb->XtVmmStackBase+rpb->XtVmmStackSize));
	#else
	return;
	#endif
}

void xmhf_sl_arch_baseplatform_initialize(void){
	
	//initialize PCI subsystem
	xmhf_baseplatform_arch_x86_pci_initialize();
	
	//check ACPI subsystem
	{
		ACPI_RSDP rsdp;
		#ifndef __XMHF_VERIFICATION__
			//TODO: plug in a BIOS data area map/model
			if(!xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp)){
				printf("\n%s: ACPI RSDP not found, Halting!", __FUNCTION__);
				HALT();
			}
		#endif //__XMHF_VERIFICATION__
	}
	
}


void xmhf_sl_arch_x86_invoke_runtime_entrypoint(u32 entrypoint, u32 stacktop) {
		
	asm volatile(
		"movl %0, %%esp \r\n"
		"movl %1, %%eax \r\n"
		"jmpl *%%eax \r\n"
		: //no outputs
		: "m" (stacktop), "m" (entrypoint)
		: "eax", "esp"
	);
		
		
} 
