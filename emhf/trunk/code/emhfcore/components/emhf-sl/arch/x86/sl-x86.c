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

/**
 * sl-x86.c
 * EMHF secure loader x86 arch. backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
 
#include <emhf.h>
#include <sha1.h>

//we only have confidence in the runtime's expected value here in the SL
static INTEGRITY_MEASUREMENT_VALUES g_sl_gold /* __attribute__(( section("") )) */ = {
    .sha_runtime = ___RUNTIME_INTEGRITY_HASH___,
    .sha_slabove64K = BAD_INTEGRITY_HASH,
    .sha_slbelow64K = BAD_INTEGRITY_HASH
};


/* hypervisor (runtime) virtual address to sl-address. */
void* hva2sla(uintptr_t x) {
  return (void*)(x - __TARGET_BASE + PAGE_SIZE_2M);
}

/* sl-address to system-physical-address */
u64 sla2spa(void* x) {
  return (u64)(uintptr_t)(x) + sl_baseaddr;
}


//---runtime paging setup-------------------------------------------------------
//physaddr and virtaddr are assumed to be 2M aligned
void runtime_setup_paging(RPB *rpb, u32 runtime_spa, u32 runtime_sva, u32 totalsize){
  pdpt_t xpdpt;
  pdt_t xpdt;
  u32 hva=0, i;
  u32 l_cr0, l_cr3, l_cr4;
  u64 default_flags;
  u32 runtime_image_offset = PAGE_SIZE_2M;
	
  printf("\nSL (%s): runtime_spa=%08x, runtime_sva=%08x, totalsize=%08x",
         __FUNCTION__, runtime_spa, runtime_sva, totalsize);
	
  xpdpt= hva2sla(rpb->XtVmmPdptBase);
  xpdt = hva2sla(rpb->XtVmmPdtsBase);
	
  printf("\n	pa xpdpt=0x%p, xpdt=0x%p", xpdpt, xpdt);
	
  default_flags = (u64)(_PAGE_PRESENT);

  //init pdpt
  for(i = 0; i < PAE_PTRS_PER_PDPT; i++) {
    u64 pdt_spa = sla2spa(xpdt) + (i << PAGE_SHIFT_4K);
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

  printf("\nSL: preparing to turn on paging..");
  
  //setup cr4
  l_cr4 = CR4_PSE | CR4_PAE;
  write_cr4(l_cr4);
  printf("\nSL: setup CR4.");
  
  //setup cr0
	l_cr0 = 0x00000015; // ET, EM, PE
  write_cr0(l_cr0);
  printf("\nSL: setup CR0.");

  //set up cr3
  l_cr3 = sla2spa(xpdpt);
  printf("\nSL: CR3=0x%08x", l_cr3);

  write_cr3(l_cr3);
  printf("\nSL: setup CR3.");

  //disable caching 
  //l_cr0 |= (u32)CR0_CD;
  
  //enable paging
  l_cr0 |= (u32)0x80000000;
  write_cr0(l_cr0);
  printf("\nSL: paging enabled successfully.");
}

/* XXX TODO Read PCR values and sanity-check that DRTM was successful
 * (i.e., measurements match expectations), and integrity-check the
 * runtime. */
/* Note: calling this *before* paging is enabled is important. */
bool sl_integrity_check(u8* runtime_base_addr, size_t runtime_len) {
    int ret;
    u32 locality = EMHF_TPM_LOCALITY_PREF; /* target.h */
    tpm_pcr_value_t pcr17, pcr18;    

    print_hex("SL: Golden Runtime SHA-1: ", g_sl_gold.sha_runtime, SHA_DIGEST_LENGTH);

    printf("\nSL: CR0 %08lx, CD bit %ld", read_cr0(), read_cr0() & CR0_CD);
    hashandprint("SL: Computed Runtime SHA-1: ",
                 runtime_base_addr, runtime_len);    

    if(hwtpm_open_locality(locality)) {
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
    deactivate_all_localities();
    
    return true;    
}

void sanitize_post_launch(void){
	
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


void early_dmaprot_init(u32 runtime_size)
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

