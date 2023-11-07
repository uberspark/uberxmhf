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
//static INTEGRITY_MEASUREMENT_VALUES g_sl_gold /* __attribute__(( section("") )) */ = {
//    .sha_runtime = ___RUNTIME_INTEGRITY_HASH___,
//    .sha_slabove64K = BAD_INTEGRITY_HASH,
//    .sha_slbelow64K = BAD_INTEGRITY_HASH
//};

#ifdef __AMD64__
/* Access page table as an array */
extern u64 sl_pdt[2048];

/* Used to access physical addresses in C code */
extern u32 xmhf_baseplatform_arch_flat_va_offset;

/* Setup paging for secureloader */
void xmhf_setup_sl_paging(u32 baseaddr) {
    u64 default_flags;
    xmhf_baseplatform_arch_flat_va_offset = baseaddr;
    /*
     * The first page (contains sl code and stack) is set up by assembly.
     * This function sets up paging for the rest virtual pages (up to 4 GiB).
     */
    default_flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_PSE);
    for (u64 i = 1; i < (PAGE_ALIGN_UP_2M(ADDR_4GB) >> PAGE_SHIFT_2M); i++) {
        u64 sla = (i << PAGE_SHIFT_2M);
        u64 hva = sla + (u64)baseaddr;
        hva &= ADDR_4GB - 1ULL; /* wrap around for low physical addresses */
        sl_pdt[i] = p4l_make_pde_big(hva, default_flags);
    }
}
#elif !defined(__I386__)
    #error "Unsupported Arch"
#endif /* !defined(__I386__) */

#ifndef __XMHF_VERIFICATION__

#ifdef __AMD64__
//---runtime paging setup-------------------------------------------------------
//build a 4-level paging that identity maps the lowest 4GiB memory
//returns 64-bit address of PML4 Table (can be loaded into CR3)
u64 xmhf_sl_arch_x86_setup_runtime_paging(RPB *rpb, spa_t runtime_spa, hva_t runtime_sva, hva_t totalsize)
{
    pml4t_t xpml4;
    pdpt_t xpdpt;
    pdt_t xpdt;
    u64 i, default_flags;

    printf("\nSL (%s): runtime_spa=%016lx, runtime_sva=%016lx, totalsize=%016lx",
         __FUNCTION__, runtime_spa, runtime_sva, totalsize);

    HALT_ON_ERRORCOND(runtime_spa == runtime_sva);
    HALT_ON_ERRORCOND(runtime_spa < ADDR_4GB);
    HALT_ON_ERRORCOND(totalsize < ADDR_4GB);
    HALT_ON_ERRORCOND(runtime_spa + totalsize < ADDR_4GB);

    xpml4= hva2sla((void *)rpb->XtVmmPml4Base);
    xpdpt= hva2sla((void *)rpb->XtVmmPdptBase);
    xpdt = hva2sla((void *)rpb->XtVmmPdtsBase);

    printf("\n\tpa xpml4=0x%p, xpdpt=0x%p, xpdt=0x%p", xpml4, xpdpt, xpdt);

    /* PML4E -> PDPT */
    default_flags = (u64)(_PAGE_PRESENT | _PAGE_RW);
    for (i = 0; i < (PAGE_ALIGN_UP_512G(MAX_PHYS_ADDR) >> PAGE_SHIFT_512G); i++) {
        u64 pdpt_spa = sla2spa((void *)xpdpt) + (i << PAGE_SHIFT_4K);
        xpml4[i] = p4l_make_plm4e(pdpt_spa, default_flags);
    }

    /* PDPTE -> PDT */
    default_flags = (u64)(_PAGE_PRESENT | _PAGE_RW);
    for (i = 0; i < (PAGE_ALIGN_UP_1G(MAX_PHYS_ADDR) >> PAGE_SHIFT_1G); i++) {
        u64 pdt_spa = sla2spa((void *)xpdt) + (i << PAGE_SHIFT_4K);
        xpdpt[i] = p4l_make_pdpe(pdt_spa, default_flags);
    }

    /* PDE -> 2 MiB page */
    default_flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_PSE);
    for(i = 0; i < (PAGE_ALIGN_UP_2M(MAX_PHYS_ADDR) >> PAGE_SHIFT_2M); i++) {
        hva_t hva = i << PAGE_SHIFT_2M;
        spa_t spa = hva2spa((void *)hva);
        u64 flags = default_flags;
        if(spa == 0xfee00000 || spa == 0xfec00000) {
            // Unity-map some MMIO regions with Page Cache disabled
            // 0xfed00000 contains Intel TXT config regs & TPM MMIO
            // 0xfee00000 contains LAPIC base
            HALT_ON_ERRORCOND(hva == spa); // expecting these to be unity-mapped
            flags |= (u64)(_PAGE_PCD);
        }
        xpdt[i] = p4l_make_pde_big(spa, flags);
    }

    return sla2spa((void *)xpml4);
}
#elif defined(__I386__)
//---runtime paging setup-------------------------------------------------------
//physaddr and virtaddr are assumed to be 2M aligned
//returns 32-bit base address of page table root (can be loaded into CR3)
u32 xmhf_sl_arch_x86_setup_runtime_paging(RPB *rpb, u32 runtime_spa, u32 runtime_sva, u32 totalsize){
  pdpt_t xpdpt;
  pdt_t xpdt;
  hva_t hva=0;
  u32 i;
  u64 default_flags;

  printf("\nSL (%s): runtime_spa=%08x, runtime_sva=%08x, totalsize=%08x",
         __FUNCTION__, runtime_spa, runtime_sva, totalsize);

  xpdpt= hva2sla((void *)rpb->XtVmmPdptBase);
  xpdt = hva2sla((void *)rpb->XtVmmPdtsBase);

  printf("\n	pa xpdpt=0x%p, xpdt=0x%p", xpdpt, xpdt);

  default_flags = (u64)(_PAGE_PRESENT);

  //init pdpt
  for(i = 0; i < PAE_PTRS_PER_PDPT; i++) {
    u64 pdt_spa = sla2spa((void *)xpdt) + (i << PAGE_SHIFT_4K);
    xpdpt[i] = pae_make_pdpe(pdt_spa, default_flags);
  }

  //init pdts with unity mappings
  default_flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_PSE);
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
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */

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


#ifdef __DRT__
void xmhf_sl_arch_sanitize_post_launch(void){
	#ifndef __XMHF_VERIFICATION__

    if(get_cpu_vendor_or_die() == CPU_VENDOR_INTEL) {
        txt_heap_t *txt_heap;
        os_mle_data_t *os_mle_data;

        // sl.c unity-maps 0xfed00000 for 2M so these should work fine
        txt_heap = get_txt_heap();
		printf("\nSL: txt_heap = 0x%08lx", (uintptr_t)txt_heap);
        /// compensate for special DS here in SL
        os_mle_data = get_os_mle_data_start((txt_heap_t*)((uintptr_t)txt_heap - sl_baseaddr));
        printf("\nSL: os_mle_data = 0x%08lx", (uintptr_t)os_mle_data);
        // restore pre-SENTER MTRRs that were overwritten for SINIT launch
        if(!validate_mtrrs(&(os_mle_data->saved_mtrr_state))) {
            printf("\nSECURITY FAILURE: validate_mtrrs() failed.\n");
            HALT();
        }

        printf("\nSL: Restoring mtrrs...");

        restore_mtrrs(&(os_mle_data->saved_mtrr_state));
    }

	#endif
}
#endif /* __DRT__ */

#ifdef __DMAP__
void xmhf_sl_arch_early_dmaprot_init(u32 runtime_size)
{

		{
			spa_t protectedbuffer_paddr;
			sla_t protectedbuffer_vaddr;
			u32 protectedbuffer_size;
			spa_t memregionbase_paddr;
			u32 memregion_size;
			u32 cpu_vendor = get_cpu_vendor_or_die();

			HALT_ON_ERRORCOND(cpu_vendor == CPU_VENDOR_AMD || cpu_vendor == CPU_VENDOR_INTEL);


			if(cpu_vendor == CPU_VENDOR_AMD){
				protectedbuffer_paddr = sl_baseaddr + (sla_t)&g_sl_protected_dmabuffer;
				protectedbuffer_vaddr = (sla_t)&g_sl_protected_dmabuffer;
				protectedbuffer_size = (2 * PAGE_SIZE_4K);
			}else{	//CPU_VENDOR_INTEL
				protectedbuffer_paddr = sl_baseaddr + 0x100000;
				protectedbuffer_vaddr = 0x100000;
				protectedbuffer_size = (2 * PAGE_SIZE_4K);
			}

			memregionbase_paddr = sl_baseaddr;
			memregion_size = (runtime_size + PAGE_SIZE_2M);

			printf("\nSL: Initializing DMA protections...");


			if(!xmhf_dmaprot_earlyinitialize(protectedbuffer_paddr,
				protectedbuffer_vaddr, protectedbuffer_size,
				memregionbase_paddr, memregion_size)){
				printf("\nSL: Fatal, could not initialize DMA protections. Halting!");
				HALT();
			}

			printf("\nSL: Initialized DMA protections successfully");

		}

}
#endif /* __DMAP__ */


void xmhf_sl_arch_xfer_control_to_runtime(RPB *rpb){
	u32 ptba;	//page table base address
	TSSENTRY *t;
	hva_t tss_base;
	hva_t gdt_base;

	#ifndef __XMHF_VERIFICATION__
		//setup runtime TSS
		tss_base=(hva_t)rpb->XtVmmTSSBase;
		gdt_base= *(hva_t *)(hva2sla((void *)(rpb->XtVmmGdt + 2)));
	#else
		tss_base=PAGE_SIZE_2M+PAGE_SIZE_4K;
		gdt_base=PAGE_SIZE_2M+PAGE_SIZE_4K+2048;
	#endif

		//fix TSS descriptor, 18h
		t= (TSSENTRY *)((hva_t)(hva2sla((void *)gdt_base)) + __TRSEL );
		t->attributes1= 0x89;
		t->limit16_19attributes2= 0x10;
#ifdef __AMD64__
		t->baseAddr0_15= (u16)(tss_base & 0x000000000000FFFF);
		t->baseAddr16_23= (u8)((tss_base & 0x0000000000FF0000) >> 16);
		t->baseAddr24_31= (u8)((tss_base & 0x00000000FF000000) >> 24);
		t->baseAddr32_63= (u32)((tss_base & 0xFFFFFFFF00000000) >> 32);
#elif defined(__I386__)
		t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
		t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
		t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
		t->limit0_15=0x67;
	printf("\nSL: setup runtime TSS.");

	#ifndef __XMHF_VERIFICATION__
	//setup paging structures for runtime
	ptba=xmhf_sl_arch_x86_setup_runtime_paging(rpb, rpb->XtVmmRuntimePhysBase, __TARGET_BASE, PAGE_ALIGN_UP_2M(rpb->XtVmmRuntimeSize));
	#endif

	printf("\nSL: setup runtime paging structures.");

	printf("\nTransferring control to runtime");
	//printf("\nGDT=%08x, IDT=%08x, EntryPoint=%08x", rpb->XtVmmGdt, rpb->XtVmmIdt, rpb->XtVmmEntryPoint);
	//printf("\nTop-of-stack=%08x, CR3=%08x", (rpb->XtVmmStackBase+rpb->XtVmmStackSize), ptba);


	#ifndef __XMHF_VERIFICATION__
	//transfer control to runtime and never return
	xmhf_sl_arch_x86_invoke_runtime_entrypoint(rpb->XtVmmGdt, rpb->XtVmmIdt,
#ifdef __AMD64__
				rpb->XtVmmEntryPoint, (rpb->XtVmmStackBase+rpb->XtVmmStackSize), ptba, sla2spa((void *)0));
#elif defined(__I386__)
				rpb->XtVmmEntryPoint, (rpb->XtVmmStackBase+rpb->XtVmmStackSize), ptba);
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
	#else
	return;
	#endif
}
