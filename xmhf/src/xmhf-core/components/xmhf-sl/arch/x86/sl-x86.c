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

//we only have confidence in the runtime's expected value here in the SL
static INTEGRITY_MEASUREMENT_VALUES g_sl_gold /* __attribute__(( section("") )) */ = {
    .sha_runtime = ___RUNTIME_INTEGRITY_HASH___,
    .sha_slabove64K = BAD_INTEGRITY_HASH,
    .sha_slbelow64K = BAD_INTEGRITY_HASH
};


/* hypervisor (runtime) virtual address to sl-address. */
void* emhf_sl_arch_hva2sla(uintptr_t x) {
  return (void*)(x - __TARGET_BASE + PAGE_SIZE_2M);
}

/* sl-address to system-physical-address */
u64 emhf_sl_arch_sla2spa(void* x) {
  return (u64)(uintptr_t)(x) + sl_baseaddr;
}


//---runtime paging setup-------------------------------------------------------
//physaddr and virtaddr are assumed to be 2M aligned
//returns 32-bit base address of page table root (can be loaded into CR3)
u32 emhf_sl_arch_x86_setup_runtime_paging(RPB *rpb, u32 runtime_spa, u32 runtime_sva, u32 totalsize){
  pdpt_t xpdpt;
  pdt_t xpdt;
  u32 hva=0, i;
 // u32 l_cr0, l_cr3, l_cr4;
  u64 default_flags;
  //u32 runtime_image_offset = PAGE_SIZE_2M;
	
  printf("\nSL (%s): runtime_spa=%08x, runtime_sva=%08x, totalsize=%08x",
         __FUNCTION__, runtime_spa, runtime_sva, totalsize);
	
  xpdpt= emhf_sl_arch_hva2sla(rpb->XtVmmPdptBase);
  xpdt = emhf_sl_arch_hva2sla(rpb->XtVmmPdtsBase);
	
  printf("\n	pa xpdpt=0x%p, xpdt=0x%p", xpdpt, xpdt);
	
  default_flags = (u64)(_PAGE_PRESENT);

  //init pdpt
  for(i = 0; i < PAE_PTRS_PER_PDPT; i++) {
    u64 pdt_spa = emhf_sl_arch_sla2spa(xpdt) + (i << PAGE_SHIFT_4K);
    xpdpt[i] = pae_make_pdpe(pdt_spa, default_flags);
  }

  /* we don't cope if the hypervisor virtual location overlaps with
     its physical location. See bug #145. */
  ASSERT(!((runtime_sva - runtime_spa) < totalsize));
  ASSERT(!((runtime_spa - runtime_sva) < totalsize));

  //init pdts with unity mappings
  default_flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_PSE);
  for(i = 0, hva = 0;
      i < (ADDR_4GB >> (PAE_PDT_SHIFT));
      i ++, hva += PAGE_SIZE_2M) {
    u64 spa = hva2spa((void*)hva);
    u64 flags = default_flags;

    if(spa == 0xfee00000 || spa == 0xfec00000) {
      /* Unity-map some MMIO regions with Page Cache disabled 
       * 0xfed00000 contains Intel TXT config regs & TPM MMIO 
       * ...but 0xfec00000 is the closest 2M-aligned addr 
       * 0xfee00000 contains APIC base 
       */
      ASSERT(hva==spa); /* expecting these to be unity-mapped */
      flags |= (u64)(_PAGE_PCD);
      printf("\nSL: updating flags for hva 0x%08x", hva);
    }

    xpdt[i] = pae_make_pde_big(spa, flags);
  }

  return emhf_sl_arch_sla2spa(xpdpt);
}

/* XXX TODO Read PCR values and sanity-check that DRTM was successful
 * (i.e., measurements match expectations), and integrity-check the
 * runtime. */
/* Note: calling this *before* paging is enabled is important. */
bool emhf_sl_arch_integrity_check(u8* runtime_base_addr, size_t runtime_len) {
    int ret;
    u32 locality = EMHF_TPM_LOCALITY_PREF; /* target.h */
    tpm_pcr_value_t pcr17, pcr18;    
	(void)g_sl_gold;

    print_hex("SL: Golden Runtime SHA-1: ", g_sl_gold.sha_runtime, SHA_DIGEST_LENGTH);

    printf("\nSL: CR0 %08lx, CD bit %ld", read_cr0(), read_cr0() & CR0_CD);
    hashandprint("SL: Computed Runtime SHA-1: ",
                 runtime_base_addr, runtime_len);    

    if(emhf_tpm_open_locality(locality)) {
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

    /* free TPM so that OS driver works as expected */
    emhf_tpm_arch_deactivate_all_localities();
    
    return true;    
}

void emhf_sl_arch_sanitize_post_launch(void){
	
    if(get_cpu_vendor_or_die() == CPU_VENDOR_INTEL) {
        txt_heap_t *txt_heap;
        os_mle_data_t *os_mle_data;

        // sl.c unity-maps 0xfed00000 for 2M so these should work fine 
        txt_heap = get_txt_heap();
        printf("\nSL: txt_heap = 0x%08x", (u32)txt_heap);
        /// compensate for special DS here in SL 
        os_mle_data = get_os_mle_data_start((txt_heap_t*)((u32)txt_heap - sl_baseaddr));
        printf("\nSL: os_mle_data = 0x%08x", (u32)os_mle_data);
        // restore pre-SENTER MTRRs that were overwritten for SINIT launch 
        if(!validate_mtrrs(&(os_mle_data->saved_mtrr_state))) {
            printf("\nSECURITY FAILURE: validate_mtrrs() failed.\n");
            HALT();
        }
        printf("\nSL: Restoring mtrrs...");
        restore_mtrrs(&(os_mle_data->saved_mtrr_state));
    }

}


void emhf_sl_arch_early_dmaprot_init(u32 runtime_size)
{

#if defined(__DMAPROT__)	
		{
			u64 protectedbuffer_paddr;
			u32 protectedbuffer_vaddr;
			u32 protectedbuffer_size;
			u64 memregionbase_paddr;
			u32 memregion_size;
			u32 cpu_vendor = get_cpu_vendor_or_die();
			
			ASSERT(cpu_vendor == CPU_VENDOR_AMD || cpu_vendor == CPU_VENDOR_INTEL);
			
			if(cpu_vendor == CPU_VENDOR_AMD){
				protectedbuffer_paddr = sl_baseaddr + (u32)&g_sl_protected_dmabuffer;
				protectedbuffer_vaddr = (u32)&g_sl_protected_dmabuffer;
				protectedbuffer_size = (2 * PAGE_SIZE_4K);
			}else{	//CPU_VENDOR_INTEL
				protectedbuffer_paddr = sl_baseaddr + 0x100000;
				protectedbuffer_vaddr = 0x100000;
				protectedbuffer_size = (3 * PAGE_SIZE_4K);
			}

			memregionbase_paddr = sl_baseaddr;
			memregion_size = (runtime_size + PAGE_SIZE_2M);

			printf("\nSL: Initializing DMA protections...");
			
			if(!emhf_dmaprot_earlyinitialize(protectedbuffer_paddr,
				protectedbuffer_vaddr, protectedbuffer_size,
				memregionbase_paddr, memregion_size)){
				printf("\nSL: Fatal, could not initialize DMA protections. Halting!");
				HALT();	
			}
			
			printf("\nSL: Initialized DMA protections successfully");
		}
		
		
#endif //__DMAPROT__
	
}

void emhf_sl_arch_xfer_control_to_runtime(RPB *rpb){
	u32 ptba;	//page table base address
//	u32 rtm_gdt, rtm_idt, rtm_ep, rtm_tos;
	
	//setup runtime TSS
	{
			TSSENTRY *t;
	  	u32 tss_base=(u32)rpb->XtVmmTSSBase;
	  	u32 gdt_base= *(u32 *)(emhf_sl_arch_hva2sla(rpb->XtVmmGdt + 2));
	
			//fix TSS descriptor, 18h
			t= (TSSENTRY *)((u32)gdt_base + __TRSEL );
		  t->attributes1= 0x89;
		  t->limit16_19attributes2= 0x10;
		  t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
		  t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
		  t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);      
		  t->limit0_15=0x67;
	}
	printf("\nSL: setup runtime TSS.");	

	//setup paging structures for runtime 
	ptba=emhf_sl_arch_x86_setup_runtime_paging(rpb, rpb->XtVmmRuntimePhysBase, __TARGET_BASE, PAGE_ALIGN_UP2M(rpb->XtVmmRuntimeSize));
	printf("\nSL: setup runtime paging structures.");        

	printf("\nTransferring control to runtime");
	printf("\nGDT=%08x, IDT=%08x, EntryPoint=%08x", rpb->XtVmmGdt, rpb->XtVmmIdt, rpb->XtVmmEntryPoint);
	printf("\nTop-of-stack=%08x, CR3=%08x", (rpb->XtVmmStackBase+rpb->XtVmmStackSize), ptba);

	//transfer control to runtime and never return
	emhf_sl_arch_x86_invoke_runtime_entrypoint(rpb->XtVmmGdt, rpb->XtVmmIdt, 
				rpb->XtVmmEntryPoint, (rpb->XtVmmStackBase+rpb->XtVmmStackSize), ptba);
	
}
