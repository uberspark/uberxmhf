//lentry.c - loader initialization and functionality
//author: amit vasudevan (amitvasudevan@acm.org)

//---includes-------------------------------------------------------------------
#include <target.h>

//---forward prototypes---------------------------------------------------------
void XtLdrTransferControlToRtm(u32 gdtAddr, u32 idtAddr, u32 entryPoint, u32 stackTop) __attribute__((cdecl));
void cstartup(unsigned long magic, unsigned long addr);
MPFP * MP_GetFPStructure(void);
u32 _MPFPComputeChecksum(u32 spaddr, u32 size);

//---globals--------------------------------------------------------------------
u32 runtime_phys_addr=0;
u32 runtime_size_bytes=0;
u32 runtime_size_2Maligned=0;
PXTLPB	lpb;
GRUBE820 grube820list[MAX_E820_ENTRIES];
u32 grube820list_numentries=0;        //actual number of e820 entries returned
                                  //by grub

PCPU pcpus[MAX_PCPU_ENTRIES];
u32 pcpus_numentries=0;


//---runtime paging setup-------------------------------------------------------
//physaddr and virtaddr are assumed to be 2M aligned
void runtime_setup_paging(u32 physaddr, u32 virtaddr, u32 totalsize){
	pdpt_t xpdpt;
	pdt_t xpdt;
	u32 paddr=0, i, j, y;
	u32 l_cr0, l_cr3, l_cr4;
	u64 flags;
	
	xpdpt=(pdpt_t)((u32)lpb->XtVmmPdptBase - __TARGET_BASE + runtime_phys_addr);
	xpdt=(pdt_t)((u32)lpb->XtVmmPdtsBase  - __TARGET_BASE + runtime_phys_addr);
	
	//printf("\npa xpdpt=0x%08x, xpdt=0x%08x", (u32)xpdpt, (u32)xpdt);
	
  flags = (u64)(_PAGE_PRESENT);
  //init pdpt
  for(i = 0; i < PAE_PTRS_PER_PDPT; i++){
    y = (u32)__pa((u32)xpdt + (i << PAGE_SHIFT_4K));
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
      //unity map
      if(paddr == 0xfee00000)
        flags |= (u64)(_PAGE_PCD);
        
      xpdt[i] = pae_make_pde_big((u64)paddr, flags);
    }
  }

	//setup cr4
  l_cr4 = CR4_PSE | CR4_PAE;
  write_cr4(l_cr4);
  
  //setup cr0
	l_cr0 = 0x00000021; // ET, EM, PE
  write_cr0(l_cr0);

  //set up cr3
  l_cr3 = __pa((u32)xpdpt);
  write_cr3(l_cr3);
  
  //enable paging
  l_cr0 |= (u32)0x80000000;
	write_cr0(l_cr0);

}

//---E820 parsing and handling--------------------------------------------------
//runtimesize is assumed to be 2M aligned
u32 dealwithE820(multiboot_info_t *mbi, u32 runtimesize){
  //check if GRUB has a valid E820 map
  if(!(mbi->flags & MBI_MEMMAP)){
    printf("\n%s: FATAL error, no E820 map provided!", __FUNCTION__);
    HALT();
  }
  
  //zero out grub e820 list
  memset((void *)&grube820list, 0, sizeof(GRUBE820)*MAX_E820_ENTRIES);
  
  //grab e820 list into grube820list
  {
    memory_map_t *mmap;
    for ( mmap = (memory_map_t *) mbi->mmap_addr;
          (unsigned long) mmap < mbi->mmap_addr + mbi->mmap_length;
           mmap = (memory_map_t *) ((unsigned long) mmap
                                       + mmap->size + sizeof (mmap->size))){
      grube820list[grube820list_numentries].baseaddr_low = mmap->base_addr_low;
      grube820list[grube820list_numentries].baseaddr_high = mmap->base_addr_high;
      grube820list[grube820list_numentries].length_low = mmap->length_low;
      grube820list[grube820list_numentries].length_high = mmap->length_high; 
      grube820list[grube820list_numentries].type = mmap->type;
      grube820list_numentries++;
    }
  }

  //traverse e820 list backwards to find an entry with type=0x1 (free)
  //with free amount of memory for runtime
  {
    u32 foundentry=0;
    u32 runtimephysicalbase=0;
    int i;
     
    for(i= (int)(grube820list_numentries-1); i >=0; i--){
      u32 baseaddr, size;
      baseaddr = grube820list[i].baseaddr_low;
      size = grube820list[i].length_low;
    
      if(grube820list[i].type == 0x1){ //free memory?
        if(grube820list[i].baseaddr_high) //greater than 4GB? then skip
          continue; 

        if(grube820list[i].length_high){
          printf("\noops 64-bit length unhandled!");
          HALT();
        }
      
        runtimephysicalbase = PAGE_ALIGN_2M((u32)baseaddr + size) - runtimesize;

        if( runtimephysicalbase >= baseaddr ){
          foundentry=1;
          break;
        }
      }
    } 
    
    if(!foundentry){
      printf("\nFatal: unable to find E820 memory for runtime!");
      HALT();
    }

    //entry number we need to split is indexed by i, we need to
    //make place for 1 extra entry at position i
    if(grube820list_numentries == MAX_E820_ENTRIES){
      printf("\noops, exhausted max E820 entries!");
      HALT();
    }

    if(i == (int)(grube820list_numentries-1)){
      //if this is the last entry, we dont need memmove
      //deal with i and i+1
      
    }else{
      memmove( (void *)&grube820list[i+2], (void *)&grube820list[i+1], (grube820list_numentries-i-1)*sizeof(GRUBE820));
      memset (&grube820list[i+1], 0, sizeof(GRUBE820));
      //deal with i and i+1 
      {
        u32 sizetosplit= grube820list[i].length_low;
        u32 newsizeofiplusone = grube820list[i].baseaddr_low + sizetosplit - runtimephysicalbase;
        u32 newsizeofi = runtimephysicalbase - grube820list[i].baseaddr_low;
        grube820list[i].length_low = newsizeofi;
        grube820list[i+1].baseaddr_low = runtimephysicalbase;
        grube820list[i+1].type = 0x2;// reserved
        grube820list[i+1].length_low = newsizeofiplusone;
      
      }
    }
    grube820list_numentries++;
    
    
    printf("\nRuntime physical base=0x%08x", runtimephysicalbase);
    return runtimephysicalbase;
     
  }
  
  
}


//---MP config table handling---------------------------------------------------
void dealwithMP(void){
	if(!smp_getinfo(&pcpus, &pcpus_numentries)){
		printf("\nFatal error with SMP detection. Halting!");
		HALT();
	}
}



//---loader main----------------------------------------------------------------
void cstartup(unsigned long magic, unsigned long addr)
{
	multiboot_info_t *mbi;
	module_t *mod_array;
	u32 mods_count;
	u32 xsize, entrypoint, i;

#ifdef __DEBUG_SERIAL__		
	init_uart();
#endif

#ifdef __DEBUG_VGA__
	vgamem_clrscr();
#endif

  mbi = (multiboot_info_t *) addr;
  mod_array = (module_t*)mbi->mods_addr;
  mods_count = mbi->mods_count;

	printf("\nIntel-VT-MP: loader initializaing...");
	printf("\ntotal modules:%u", mods_count);
  
  //runtime, OS boot sector and optional module for the time-being
  ASSERT(mods_count >=2 && mods_count <=3);  

  //E820 handling and runtime physical mem. relocation
  runtime_size_bytes = mod_array[0].mod_end - mod_array[0].mod_start;   
  runtime_size_2Maligned = PAGE_ALIGN_UP2M(runtime_size_bytes);
  runtime_phys_addr = dealwithE820(mbi, runtime_size_2Maligned); 
  printf("\nrelocated runtime to phys mem at 0x%08x", runtime_phys_addr);
  printf("\nruntime size=0x%08x, 2Maligned=0x%08x", runtime_size_bytes, runtime_size_2Maligned);
  
  //copy runtime image to relocated phys. addr and get a pointer to the runtime header
  memcpy((void*)runtime_phys_addr, (void*)mod_array[0].mod_start, runtime_size_bytes);
  lpb=(PXTLPB)runtime_phys_addr;

  //setup paging for runtime and reinitialize pointer to the runtime header
	runtime_setup_paging(runtime_phys_addr, __TARGET_BASE, runtime_size_2Maligned);
	printf("\nPaging setup..");	
  lpb=(PXTLPB)__TARGET_BASE;

  //store runtime physical and virtual base addresses along with size
  lpb->XtVmmRuntimePhysBase = runtime_phys_addr;
  lpb->XtVmmRuntimeVirtBase = __TARGET_BASE;
  lpb->XtVmmRuntimeSize = runtime_size_2Maligned;
  
  //store revised E820 map and number of entries
  memcpy((void *)lpb->XtVmmE820Buffer, (void *)grube820list, sizeof(grube820list));
  lpb->XtVmmE820NumEntries = grube820list_numentries; 

 	//setup guest OS boot sector info in LPB	
  xsize = mod_array[1].mod_end - mod_array[1].mod_start;   
  printf("\nGuest OS Boot Sector Module: size=%u, start=0x%08X", xsize, (u32)mod_array[1].mod_start);
	lpb->XtGuestOSBootModuleBase=mod_array[1].mod_start;
	lpb->XtGuestOSBootModuleSize=xsize;
	
	//if there is an optional module present, setup its info in LPB as well
  if(mods_count == 3){
    xsize = mod_array[2].mod_end - mod_array[2].mod_start;   
    printf("\nGuest OS Optional Module: size=%u, start=0x%08X", xsize, (u32)mod_array[2].mod_start);
	  lpb->XtGuestOSBootModuleBaseSup1=mod_array[2].mod_start;
	  lpb->XtGuestOSBootModuleSizeSup1=xsize;
	}
	
  //deal with MP and get CPU table
  dealwithMP();
  memcpy((void *)lpb->XtVmmMPCpuinfoBuffer, (void *)pcpus, sizeof(pcpus));
  lpb->XtVmmMPCpuinfoNumEntries = pcpus_numentries; 

 	//setup runtime IDT
	{
		u32 *fptr, idtbase;
		idtentry_t *idtentry;
		
		printf("\nXtVmmIdt=0x%08X, XtVmmIdtFunctionPointers=0x%08X, XtVmmIdtEntries=0x%08X", 
			lpb->XtVmmIdt, lpb->XtVmmIdtFunctionPointers, lpb->XtVmmIdtEntries);
		fptr=(u32 *)lpb->XtVmmIdtFunctionPointers;
		idtbase= *(u32 *)((u32)lpb->XtVmmIdt+2);
		printf("\nidtbase=0x%08X", idtbase);
		for(i=0; i < lpb->XtVmmIdtEntries; i++){
			idtentry_t *idtentry=(idtentry_t *)((u32)idtbase+ (i*8));
			idtentry->isrLow= (u16)fptr[i];
			idtentry->isrHigh= (u16) ( (u32)fptr[i] >> 16 );
			idtentry->isrSelector = __CS;
			idtentry->count=0x0;
			idtentry->type=0x8E;
			//printf("\n%u -> 0x%08X%08X", i, *(u32 *)((u32)idtbase+ (i*8)+4), *(u32 *)((u32)idtbase+ (i*8)) );
		}
		printf("\nRuntime IDT Setup Done.");
	}

  //setup runtime TSS
	printf("\nSetting up runtime TSS descriptor...");
	{
		TSSENTRY *t;
  	u32 tss_base=(u32)lpb->XtVmmTSSBase;
  	u32 gdt_base= *(u32 *)((u32)lpb->XtVmmGdt+2);

		//fix TSS descriptor, 18h
		t= (TSSENTRY *)((u32)gdt_base + __TRSEL );
	  t->attributes1= 0x89;
	  t->limit16_19attributes2= 0x10;
	  t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
	  t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
	  t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);      
	  t->limit0_15=0x67;
	}
	printf("Done.");	

  //debug
	//printf("\nXtVmmGdt=0x%08X, XtVmmEntryPoint=0x%08X", lpb->XtVmmGdt,
	//		lpb->XtVmmEntryPoint);
	//printf("\nXtVmmStackBase=0x%08X, XtVmmStackSize=0x%08X", 
	//	lpb->XtVmmStackBase, lpb->XtVmmStackSize);

  //transfer control to runtime
	XtLdrTransferControlToRtm(lpb->XtVmmGdt, lpb->XtVmmIdt, lpb->XtVmmEntryPoint, 
			lpb->XtVmmStackBase+lpb->XtVmmStackSize);	
	
	//we should never get here
	__asm__("hlt\r\n");
}
