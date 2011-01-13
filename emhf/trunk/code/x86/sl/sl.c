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

#include <target.h>


extern u32 slpb_buffer[];
RPB * rpb;
u32 sl_baseaddr=0;	
extern void XtLdrTransferControlToRtm(u32 gdtbase, u32 idtbase,
	u32 entrypoint, u32 stacktop)__attribute__((cdecl)); 

//this is the SL parameter block and is placed in a seperate section
struct _sl_parameter_block slpb __attribute__(( section(".sl_params") )) = {
	.magic = SL_PARAMETER_BLOCK_MAGIC,
};


//---runtime paging setup-------------------------------------------------------
//physaddr and virtaddr are assumed to be 2M aligned
void runtime_setup_paging(u32 physaddr, u32 virtaddr, u32 totalsize){
	pdpt_t xpdpt;
	pdt_t xpdt;
	u32 paddr=0, i, j, y;
	u32 l_cr0, l_cr3, l_cr4;
	u64 flags;
	u32 runtime_image_offset = PAGE_SIZE_2M;
	
	xpdpt=(pdpt_t)((u32)rpb->XtVmmPdptBase - __TARGET_BASE + runtime_image_offset);
	xpdt=(pdt_t)((u32)rpb->XtVmmPdtsBase  - __TARGET_BASE + runtime_image_offset);
	
	//printf("\npa xpdpt=0x%08x, xpdt=0x%08x", (u32)xpdpt, (u32)xpdt);
	
  flags = (u64)(_PAGE_PRESENT);
  //init pdpt
  for(i = 0; i < PAE_PTRS_PER_PDPT; i++){
    y = (u32)__pa((u32)sl_baseaddr + (u32)xpdt + (i << PAGE_SHIFT_4K));
    xpdpt[i] = pae_make_pdpe((u64)y, flags);
  }
 
 	//init pdts with unity mappings
  j  = ADDR_4GB >> (PAE_PDT_SHIFT);
  flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_PSE);
  for(i = 0, paddr = 0; i < j; i ++, paddr += PAGE_SIZE_2M){
    if(paddr >= physaddr && paddr < (physaddr+totalsize)){
      //map this virtual address to physical memory occupied by runtime virtual range
      u32 offset = paddr - physaddr;
      xpdt[i] = pae_make_pde_big((u64)virtaddr+offset, flags);
    }else if(paddr >= virtaddr && paddr < (virtaddr+totalsize)){
      //map this virtual addr to runtime physical addr
      u32 offset = paddr - virtaddr;
      xpdt[i] = pae_make_pde_big((u64)physaddr+offset, flags);
    }else{
        // Unity-map some MMIO regions with Page Cache disabled
        // 0xfed00000 contains Intel TXT config regs & TPM MMIO
        // 0xfee00000 contains APIC base
      if(paddr == 0xfee00000 ||
         paddr == 0xfed00000) 
        flags |= (u64)(_PAGE_PCD);
        
      xpdt[i] = pae_make_pde_big((u64)paddr, flags);
    }
  }

	//setup cr4
  l_cr4 = CR4_PSE | CR4_PAE;
  write_cr4(l_cr4);
  
  //setup cr0
	l_cr0 = 0x00000015; // ET, EM, PE
  write_cr0(l_cr0);

  //set up cr3
  l_cr3 = __pa((u32)sl_baseaddr + (u32)xpdpt);
	write_cr3(l_cr3);
  
  //enable paging
  l_cr0 |= (u32)0x80000000;
	write_cr0(l_cr0);

}


//we get here from slheader.S
void slmain(u32 baseaddr){
	//SL_PARAMETER_BLOCK *slpb;
	u32 runtime_physical_base;
	u32 runtime_size_2Maligned;
	
	u32 runtime_gdt;
	u32 runtime_idt;
	u32 runtime_entrypoint;
	u32 runtime_topofstack;
		
	//initialize debugging early on
	#ifdef __DEBUG_SERIAL__		
		init_uart();
	#endif

	#ifdef __DEBUG_VGA__
		vgamem_clrscr();
	#endif
	
	//initialze sl_baseaddr variable and print its value out
	sl_baseaddr = baseaddr;
	printf("\nSL: at 0x%08x, starting...", sl_baseaddr);
	
	//deal with SL parameter block
	//slpb = (SL_PARAMETER_BLOCK *)slpb_buffer;
	printf("\nSL: slpb at = 0x%08x", &slpb);
	ASSERT( (u32)&slpb == 0x10000 );	//linker relocates sl image starting from 0, so
																  //parameter block must be at offset 0x10000
	ASSERT( slpb.magic == SL_PARAMETER_BLOCK_MAGIC);
	
	printf("\n	hashSL=0x%08x", slpb.hashSL);
	printf("\n	errorHandler=0x%08x", slpb.errorHandler);
	printf("\n	isEarlyInit=0x%08x", slpb.isEarlyInit);
	printf("\n	numE820Entries=%u", slpb.numE820Entries);
	printf("\n	e820map at 0x%08x", &slpb.e820map);
	printf("\n	numCPUEntries=%u", slpb.numCPUEntries);
	printf("\n	pcpus at 0x%08x", &slpb.pcpus);
	printf("\n	runtime size= %u bytes", slpb.runtime_size);
	printf("\n	OS bootmodule at 0x%08x, size=%u bytes", 
		slpb.runtime_osbootmodule_base, slpb.runtime_osbootmodule_size);
	
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
	
	//setup DMA protection on runtime (secure loader is already DMA protected)
	//TODO
	
	//Measure runtime and sanity check if measurements were fine
	//TODO
	
	
	//setup runtime image for startup
	
		//get a pointer to the runtime header
  	rpb=(RPB *)PAGE_SIZE_2M;	//runtime starts at offset 2M from sl base
		ASSERT(rpb->magic == RUNTIME_PARAMETER_BLOCK_MAGIC);
		
    //store runtime physical and virtual base addresses along with size
  	rpb->XtVmmRuntimePhysBase = runtime_physical_base;
  	rpb->XtVmmRuntimeVirtBase = __TARGET_BASE;
  	rpb->XtVmmRuntimeSize = slpb.runtime_size;

	  //store revised E820 map and number of entries
	  memcpy((void *)((u32)rpb->XtVmmE820Buffer - __TARGET_BASE + PAGE_SIZE_2M), (void *)&slpb.e820map, (sizeof(GRUBE820) * slpb.numE820Entries));
  	rpb->XtVmmE820NumEntries = slpb.numE820Entries; 

		//store CPU table and number of CPUs
    memcpy((void *)((u32)rpb->XtVmmMPCpuinfoBuffer - __TARGET_BASE + PAGE_SIZE_2M), (void *)&slpb.pcpus, (sizeof(PCPU) * slpb.numCPUEntries));
  	rpb->XtVmmMPCpuinfoNumEntries = slpb.numCPUEntries; 

   	//setup guest OS boot module info in LPB	
		rpb->XtGuestOSBootModuleBase=slpb.runtime_osbootmodule_base;
		rpb->XtGuestOSBootModuleSize=slpb.runtime_osbootmodule_size;

	 	//setup runtime IDT
		{
			u32 *fptr, idtbase;
			idtentry_t *idtentry;
			u32 i;
			
			fptr=(u32 *)((u32)rpb->XtVmmIdtFunctionPointers - __TARGET_BASE + PAGE_SIZE_2M);
			idtbase= *(u32 *)(((u32)rpb->XtVmmIdt - __TARGET_BASE + PAGE_SIZE_2M) + 2);
			for(i=0; i < rpb->XtVmmIdtEntries; i++){
				idtentry_t *idtentry=(idtentry_t *)((u32)idtbase+ (i*8));
				idtentry->isrLow= (u16)fptr[i];
				idtentry->isrHigh= (u16) ( (u32)fptr[i] >> 16 );
				idtentry->isrSelector = __CS;
				idtentry->count=0x0;
				idtentry->type=0x8E;
			}
			printf("\nSL: setup runtime IDT.");
		}

		//setup runtime TSS
		{
			TSSENTRY *t;
	  	u32 tss_base=(u32)rpb->XtVmmTSSBase;
	  	u32 gdt_base= *(u32 *)(((u32)rpb->XtVmmGdt - __TARGET_BASE + PAGE_SIZE_2M)+2);
	
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
		
		//setup paging for runtime 
		runtime_setup_paging(runtime_physical_base, __TARGET_BASE, runtime_size_2Maligned);
		printf("\nSL: setup runtime paging.");	

	  //transfer control to runtime
		XtLdrTransferControlToRtm(runtime_gdt, runtime_idt, 
				runtime_entrypoint, runtime_topofstack);

		//we should never get here
		printf("\nSL: Fatal, should never be here!");
		HALT();
} 
