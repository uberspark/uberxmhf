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

//sl.c 
//secure loader implementation
//author: amit vasudevan (amitvasudevan@acm.org)

#include <emhf.h> 
#include <sha1.h>

extern u32 slpb_buffer[];
RPB * rpb;
u32 sl_baseaddr=0;	
extern void XtLdrTransferControlToRtm(u32 gdtbase, u32 idtbase,
	u32 entrypoint, u32 stacktop)__attribute__((cdecl)); 

/* SHA-1 hash of runtime should be defined during build process.
 * However, if it's not, don't fail.  Just proceed with all zeros.
 * XXX TODO Disable proceeding with insecure hash value. */
#ifndef ___RUNTIME_INTEGRITY_HASH___
#define ___RUNTIME_INTEGRITY_HASH___ BAD_INTEGRITY_HASH
#endif /*  ___RUNTIME_INTEGRITY_HASH___ */

//this is the SL parameter block and is placed in a seperate UNTRUSTED
//section
struct _sl_parameter_block slpb __attribute__(( section(".sl_untrusted_params") )) = {
	.magic = SL_PARAMETER_BLOCK_MAGIC,
};

//protected DMA-protection buffer placed in seperate section ".protdmabuffer"
//u8 g_sl_protected_dmabuffer[PAGE_SIZE_4K] __attribute__(( section(".protdmabuffer") ));
extern u32 g_sl_protected_dmabuffer[];

//we only have confidence in the runtime's expected value here in the SL
INTEGRITY_MEASUREMENT_VALUES g_sl_gold /* __attribute__(( section("") )) */ = {
    .sha_runtime = ___RUNTIME_INTEGRITY_HASH___,
    .sha_slabove64K = BAD_INTEGRITY_HASH,
    .sha_slbelow64K = BAD_INTEGRITY_HASH
};

#define SERIAL_BASE 0x3f8
void raw_serial_init(void){
    // enable DLAB and set baudrate 115200
    outb(SERIAL_BASE+0x3, 0x80);
    outb(SERIAL_BASE+0x0, 0x01);
    outb(SERIAL_BASE+0x1, 0x00);
    // disable DLAB and set 8N1
    outb(SERIAL_BASE+0x3, 0x03);
    // reset IRQ register
    outb(SERIAL_BASE+0x1, 0x00);
    // enable fifo, flush buffer, enable fifo
    outb(SERIAL_BASE+0x2, 0x01);
    outb(SERIAL_BASE+0x2, 0x07);
    outb(SERIAL_BASE+0x2, 0x01);
    // set RTS,DTR
    outb(SERIAL_BASE+0x4, 0x03);
}

/* hypervisor (runtime) virtual address to sl-address. */
static void* hva2sla(uintptr_t x) {
  return (void*)(x - __TARGET_BASE + PAGE_SIZE_2M);
}

/* sl-address to system-physical-address */
u64 sla2spa(void* x) {
  return (u64)(uintptr_t)(x) + sl_baseaddr;
}

//---runtime paging setup-------------------------------------------------------
//physaddr and virtaddr are assumed to be 2M aligned
void runtime_setup_paging(u32 runtime_spa, u32 runtime_sva, u32 totalsize){
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

//we get here from slheader.S
// rdtsc_* are valid only if PERF_CRIT is not defined.  slheader.S
// sets them to 0 otherwise.
void slmain(u32 baseaddr, u32 rdtsc_eax, u32 rdtsc_edx){
	//SL_PARAMETER_BLOCK *slpb;
	u32 runtime_physical_base;
	u32 runtime_size_2Maligned;
	
	u32 runtime_gdt;
	u32 runtime_idt;
	u32 runtime_entrypoint;
	u32 runtime_topofstack;

	ASSERT( (u32)&slpb == 0x10000 ); //linker relocates sl image starting from 0, so
                                         //parameter block must be at offset 0x10000    

	//initialize debugging early on
	#ifdef __DEBUG_SERIAL__
			g_uart_config = slpb.uart_config;
			init_uart();
	#endif

	#ifdef __DEBUG_VGA__
		vgamem_clrscr();
	#endif
	
	//dump SL parameter block address
	printf("\nSL: slpb at = 0x%08x", (u32)&slpb);

	//initialze sl_baseaddr variable and print its value out
	sl_baseaddr = baseaddr;
	
	if(slpb.isEarlyInit)
		printf("\nSL(early-init): at 0x%08x, starting...", sl_baseaddr);    
    else
		printf("\nSL(late-init): at 0x%08x, starting...", sl_baseaddr);
		

	ASSERT( slpb.magic == SL_PARAMETER_BLOCK_MAGIC);
	
	printf("\n	hashSL=0x%08x", slpb.hashSL);
	printf("\n	errorHandler=0x%08x", slpb.errorHandler);
	printf("\n	isEarlyInit=0x%08x", slpb.isEarlyInit);
	printf("\n	numE820Entries=%u", slpb.numE820Entries);
	printf("\n	e820map at 0x%08x", (u32)&slpb.e820map);
	printf("\n	numCPUEntries=%u", slpb.numCPUEntries);
	printf("\n	pcpus at 0x%08x", (u32)&slpb.pcpus);
	printf("\n	runtime size= %u bytes", slpb.runtime_size);
	printf("\n	OS bootmodule at 0x%08x, size=%u bytes", 
		slpb.runtime_osbootmodule_base, slpb.runtime_osbootmodule_size);

    slpb.rdtsc_after_drtm = (u64)rdtsc_eax | ((u64)rdtsc_edx << 32);
    printf("\nSL: RDTSC before_drtm 0x%llx, after_drtm 0x%llx",
           slpb.rdtsc_before_drtm, slpb.rdtsc_after_drtm);
    printf("\nSL: [PERF] RDTSC DRTM elapsed cycles: 0x%llx",
           slpb.rdtsc_after_drtm - slpb.rdtsc_before_drtm);
    
  //debug, dump E820 and MP table
 	printf("\n	e820map:\n");
  {
    u32 i;
    for(i=0; i < slpb.numE820Entries; i++){
      printf("\n		0x%08x%08x, size=0x%08x%08x (%u)", 
          slpb.e820map[i].baseaddr_high, slpb.e820map[i].baseaddr_low,
          slpb.e820map[i].length_high, slpb.e820map[i].length_low,
          slpb.e820map[i].type);
    }
  }
  printf("\n	pcpus:\n");
  {
    u32 i;
    for(i=0; i < slpb.numCPUEntries; i++)
      printf("\n		CPU #%u: bsp=%u, lapic_id=0x%02x", i, slpb.pcpus[i].isbsp, slpb.pcpus[i].lapic_id);
  }


	//check for unsuccessful DRT
	//TODO
	
	//get runtime physical base
	runtime_physical_base = sl_baseaddr + PAGE_SIZE_2M;	//base of SL + 2M
	
	//compute 2M aligned runtime size
	runtime_size_2Maligned = PAGE_ALIGN_UP2M(slpb.runtime_size);

	printf("\nSL: runtime at 0x%08x (2M aligned size= %u bytes)", 
			runtime_physical_base, runtime_size_2Maligned);

	//sanitize cache/MTRR/SMRAM (most important is to ensure that MTRRs 
	//do not contain weird mappings)
	//TODO
    if(get_cpu_vendor_or_die() == CPU_VENDOR_INTEL) {
        txt_heap_t *txt_heap;
        os_mle_data_t *os_mle_data;

        /* sl.c unity-maps 0xfed00000 for 2M so these should work fine */
        txt_heap = get_txt_heap();
        printf("\nSL: txt_heap = 0x%08x", (u32)txt_heap);
        /* compensate for special DS here in SL */
        os_mle_data = get_os_mle_data_start((txt_heap_t*)((u32)txt_heap - sl_baseaddr));
        printf("\nSL: os_mle_data = 0x%08x", (u32)os_mle_data);
        /* restore pre-SENTER MTRRs that were overwritten for SINIT launch */
        if(!validate_mtrrs(&(os_mle_data->saved_mtrr_state))) {
            printf("\nSECURITY FAILURE: validate_mtrrs() failed.\n");
            HALT();
        }
        printf("\nSL: Restoring mtrrs...");
        restore_mtrrs(&(os_mle_data->saved_mtrr_state));
    }
    
    /* Note: calling this *before* paging is enabled is important */
#if 0
    if(sl_integrity_check((u8*)PAGE_SIZE_2M, slpb.runtime_size)) // XXX base addr
        printf("\nsl_intergrity_check SUCCESS");
    else
        printf("\nsl_intergrity_check FAILURE");
#endif

	//get a pointer to the runtime header
 	rpb=(RPB *)PAGE_SIZE_2M;	//runtime starts at offset 2M from sl base
	printf("\nSL: RPB, magic=0x%08x", rpb->magic);
	ASSERT(rpb->magic == RUNTIME_PARAMETER_BLOCK_MAGIC);

    
	//setup DMA protection on runtime (secure loader is already DMA protected)
	//WIP
	{
		//initialize PCI subsystem
		pci_initialize();
	
		//check ACPI subsystem
		{
			ACPI_RSDP rsdp;
			if(!acpi_getRSDP(&rsdp)){
				printf("\nSL: ACPI RSDP not found, Halting!");
				HALT();
			}
		}

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
			memregion_size = (slpb.runtime_size + PAGE_SIZE_2M);

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
    
	//Measure runtime and sanity check if measurements were fine
	//TODO
	
	
	//setup runtime image for startup
	
		
    //store runtime physical and virtual base addresses along with size
  	rpb->XtVmmRuntimePhysBase = runtime_physical_base;
  	rpb->XtVmmRuntimeVirtBase = __TARGET_BASE;
  	rpb->XtVmmRuntimeSize = slpb.runtime_size;

	  //store revised E820 map and number of entries
	  memcpy(hva2sla(rpb->XtVmmE820Buffer), (void *)&slpb.e820map, (sizeof(GRUBE820) * slpb.numE820Entries));
  	rpb->XtVmmE820NumEntries = slpb.numE820Entries; 

		//store CPU table and number of CPUs
    memcpy(hva2sla(rpb->XtVmmMPCpuinfoBuffer), (void *)&slpb.pcpus, (sizeof(PCPU) * slpb.numCPUEntries));
  	rpb->XtVmmMPCpuinfoNumEntries = slpb.numCPUEntries; 

   	//setup guest OS boot module info in LPB	
		rpb->XtGuestOSBootModuleBase=slpb.runtime_osbootmodule_base;
		rpb->XtGuestOSBootModuleSize=slpb.runtime_osbootmodule_size;


        /* pass command line configuration forward */
        rpb->uart_config = g_uart_config;


		//setup runtime TSS
		{
			TSSENTRY *t;
	  	u32 tss_base=(u32)rpb->XtVmmTSSBase;
	  	u32 gdt_base= *(u32 *)(hva2sla(rpb->XtVmmGdt + 2));
	
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


		//obtain runtime gdt, idt, entrypoint and stacktop values and patch
		//entry point in XtLdrTransferControltoRtm
		{
			extern u32 sl_runtime_entrypoint_patch[];
			u32 *patchloc = (u32 *)((u32)sl_runtime_entrypoint_patch + 1);
			
			runtime_gdt = rpb->XtVmmGdt;
			runtime_idt = rpb->XtVmmIdt;
			runtime_entrypoint = rpb->XtVmmEntryPoint;
			runtime_topofstack = rpb->XtVmmStackBase+rpb->XtVmmStackSize; 
			printf("\nSL: runtime entry values:");
			printf("\n	gdt=0x%08x, idt=0x%08x", runtime_gdt, runtime_idt);
			printf("\n	entrypoint=0x%08x, topofstack=0x%08x", runtime_entrypoint, runtime_topofstack);
			*patchloc = runtime_entrypoint;
		}
		
		
		//tell runtime if we started "early" or "late"
		rpb->isEarlyInit = slpb.isEarlyInit;
		
		/*//debug dump uart_config field
	    printf("\nrpb->uart_config.port = %x", rpb->uart_config.port);
		printf("\nrpb->uart_config.clock_hz = %u", rpb->uart_config.clock_hz);
		printf("\nrpb->uart_config.baud = %u", rpb->uart_config.baud);
		printf("\nrpb->uart_config.data_bits, parity, stop_bits, fifo = %x %x %x %x", 
			rpb->uart_config.data_bits, rpb->uart_config.parity, rpb->uart_config.stop_bits, rpb->uart_config.fifo);*/

		
		//setup paging for runtime 
		runtime_setup_paging(runtime_physical_base, __TARGET_BASE, runtime_size_2Maligned);
		printf("\nSL: setup runtime paging.");        

		
		
		/*if(!slpb.isEarlyInit){
				printf("\nSL(late-init): still WiP, impressed that we got this far :>");
				HALT();
		}*/

	  //transfer control to runtime
		XtLdrTransferControlToRtm(runtime_gdt, runtime_idt, 
				runtime_entrypoint, runtime_topofstack);

		//we should never get here
		printf("\nSL: Fatal, should never be here!");
		HALT();
} 

