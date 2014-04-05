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

//XXX: The following is an ugly hack and will disappear once we move
//xmhf_sl_arch_x86_setup_runtime_paging and
//xmhf_sl_arch_x86_invoke_runtime_entrypoint
//into xmhf-core 
#define 	__DS_CPL0 	0x0010 	//CPL-0 data segment selector
#define 	__CS_CPL0 	0x0008 	//CPL-0 code segment selector
#define __TARGET_BASE_CORE				0x10200000		//258M

//we only have confidence in the runtime's expected value here in the SL
//static INTEGRITY_MEASUREMENT_VALUES g_sl_gold /* __attribute__(( section("") )) */ = {
//    .sha_runtime = ___RUNTIME_INTEGRITY_HASH___,
//    .sha_slabove64K = BAD_INTEGRITY_HASH,
//    .sha_slbelow64K = BAD_INTEGRITY_HASH
//};


#ifndef __XMHF_VERIFICATION__

//---runtime paging setup-------------------------------------------------------
//physaddr and virtaddr are assumed to be 2M aligned
//returns 32-bit base address of page table root (can be loaded into CR3)
u32 xmhf_sl_arch_x86_setup_runtime_paging(RPB *rpb, u32 runtime_spa, u32 runtime_sva, u32 totalsize){
  pdpt_t xpdpt;
  pdt_t xpdt;
  u32 hva=0, i;
  u64 default_flags;
	
  printf("SL (%s): runtime_spa=%08x, runtime_sva=%08x, totalsize=%08x\n",
         __FUNCTION__, runtime_spa, runtime_sva, totalsize);
	
  xpdpt= hva2sla((void *)rpb->XtVmmPdptBase);
  xpdt = hva2sla((void *)rpb->XtVmmPdtsBase);
	
  printf("	pa xpdpt=0x%p, xpdt=0x%p\n", xpdpt, xpdt);
	
  default_flags = (u64)(_PAGE_PRESENT);

  //init pdpt
  for(i = 0; i < PAE_PTRS_PER_PDPT; i++) {
    u64 pdt_spa = sla2spa((void *)xpdt) + (i << PAGE_SHIFT_4K);
    xpdpt[i] = pae_make_pdpe(pdt_spa, default_flags);
  }

  //init pdts with unity mappings
  default_flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_PSE | _PAGE_USER);
  for(i = 0, hva = 0;
      i < (ADDR_4GB >> (PAE_PDT_SHIFT));
      i ++, hva += PAGE_SIZE_2M) {
    u64 spa = hva2spa((void*)hva);
    u64 flags = default_flags;

    if(spa == 0xfee00000 || spa == 0xfec00000) {
      //Unity-map some MMIO regions with Page Cache disabled 
      //0xfed00000 contains Intel TXT config regs & TPM MMIO 
      //0xfee00000 contains LAPIC base 
      HALT_ON_ERRORCOND(hva==spa); // expecting these to be unity-mapped
      flags |= (u64)(_PAGE_PCD);
    }

    xpdt[i] = pae_make_pde_big(spa, flags);
  }

  return sla2spa((void *)xpdpt);
}


#endif //__XMHF_VERIFICATION__


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

	#ifndef __XMHF_VERIFICATION__
	//setup paging structures for runtime 
	ptba=xmhf_sl_arch_x86_setup_runtime_paging(rpb, rpb->XtVmmRuntimePhysBase, __TARGET_BASE_CORE, PAGE_ALIGN_UP2M(rpb->XtVmmRuntimeSize));
	#endif
	
	printf("SL: setup runtime paging structures\n");        

	printf("Transferring control to runtime\n");

	#ifndef __XMHF_VERIFICATION__
	//transfer control to runtime and never return
	xmhf_sl_arch_x86_invoke_runtime_entrypoint(rpb->XtVmmGdt, rpb->XtVmmIdt, 
				rpb->XtVmmEntryPoint, (rpb->XtVmmStackBase+rpb->XtVmmStackSize), ptba);
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


void xmhf_sl_arch_x86_invoke_runtime_entrypoint(u32 gdtbase, u32 idtbase,
	u32 entrypoint, u32 stacktop, u32 cr3) {
		
	asm volatile(
		"movl	$(0x00000030), %%eax \r\n"	//CR4_PAE | CR4_PSE
		"movl	%%eax, %%cr4 \r\n"
		"movl	%0, %%edi \r\n"				//EDI = page table base address
		"movl	%%edi, %%cr3 \r\n"			
		"movl	$(0x80000015), %%eax \r\n"   // ET, EM, PE, PG
		"movl	%%eax, %%cr0 \r\n"	    	//turn on paging
		"movl 	%1, %%esi \r\n"				//gdtbase parameter
		"movl 	%2, %%edi \r\n"				//idtbase parameter
		"subl  $0x8, %%esp \r\n"
		"movw  %%fs:(%%esi), %%ax \r\n"	
		"movw  %%ax, (%%esp) \r\n"
		"movl  %%fs:0x2(%%esi), %%eax \r\n"
		"movl  %%eax, 0x2(%%esp) \r\n"
		"lgdt	(%%esp) \r\n"
		"movw  %%fs:(%%edi), %%ax \r\n"
		"movw  %%ax, (%%esp) \r\n"
		"movl  %%fs:0x2(%%edi), %%eax \r\n"
		"movl  %%eax, 0x2(%%esp) \r\n"
		"lidt	(%%esp) \r\n"
		"addl  $0x8, %%esp \r\n"
		"movl 	%3, %%edi \r\n"					//entrypoint parameter
		"movl  	%4, %%esi \r\n"					//top of stack parameter
		"movw	%5, %%ax \r\n"
		"movw	%%ax, %%ds \r\n"	
		"movw	%%ax, %%es \r\n"
		"movw	%%ax, %%fs \r\n"
		"movw	%%ax, %%gs \r\n"
		"movw  %%ax, %%ss \r\n"
		"movl  %%esi,%%esp \r\n"
		"pushl	$0x3000 \r\n"					// clear flags, but set IOPL=3 (CPL-3)
		"popf \r\n"
		"pushl	%6 \r\n"				// far jump to runtime entry point
		"pushl	%%edi \r\n"
		"lret \r\n"
		: //no outputs
		: "m" (cr3), "m" (gdtbase), "m" (idtbase), "m" (entrypoint), "m" (stacktop), "i" (__DS_CPL0), "i" (__CS_CPL0)
		: "eax", "edi", "esi", "esp"
	);
		
		
} 
