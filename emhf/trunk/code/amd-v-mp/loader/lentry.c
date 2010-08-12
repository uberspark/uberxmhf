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
	l_cr0 = 0x00000015; // ET, EM, PE
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

  //debug: print grube820list
  {
    u32 i;
  	printf("\nOriginal E820 map follows:\n");
	  for(i=0; i < grube820list_numentries; i++){
      printf("\n0x%08x%08x, size=0x%08x%08x (%u)", 
          grube820list[i].baseaddr_high, grube820list[i].baseaddr_low,
          grube820list[i].length_high, grube820list[i].length_low,
          grube820list[i].type);
    }
  
  }
  
  //traverse e820 list backwards to find an entry with type=0x1 (free)
  //with free amount of memory for runtime
  {
    u32 foundentry=0;
    u32 runtimephysicalbase=0;
    int i;
     
    //#define ADDR_4GB  (0xFFFFFFFFUL)
    for(i= (int)(grube820list_numentries-1); i >=0; i--){
      u32 baseaddr, size;
      baseaddr = grube820list[i].baseaddr_low;
      //size = PAGE_ALIGN_4K(grube820list[i].length_low);  
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
  MPFP *mpfp;
  MPCONFTABLE *mpctable;
  
  mpfp = MP_GetFPStructure();

#ifdef __MP_VERSION__  
  if(!mpfp){
    printf("\nNo MP table, falling back to UP...");
    pcpus[pcpus_numentries].lapic_id = 0x0;
    pcpus[pcpus_numentries].lapic_ver = 0x0;
    pcpus[pcpus_numentries].lapic_base = 0xFEE00000;
    pcpus[pcpus_numentries].isbsp = 1;
    pcpus_numentries++;
    goto fallthrough;
  }
#else
  printf("\nForcing UP...");
  pcpus[pcpus_numentries].lapic_id = 0x0;
  pcpus[pcpus_numentries].lapic_ver = 0x0;
  pcpus[pcpus_numentries].lapic_base = 0xFEE00000;
  pcpus[pcpus_numentries].isbsp = 1;
  pcpus_numentries++;
  goto fallthrough;
#endif
  printf("\nMP table found at: 0x%08x", (u32)mpfp);
  printf("\nMP spec rev=0x%02x", mpfp->spec_rev);
  printf("\nMP feature info1=0x%02x", mpfp->mpfeatureinfo1);
  printf("\nMP feature info2=0x%02x", mpfp->mpfeatureinfo2);
  printf("\nMP Configuration table at 0x%08x", mpfp->paddrpointer);
  
  mpctable = (MPCONFTABLE *)mpfp->paddrpointer;
  ASSERT(mpctable->signature == MPCONFTABLE_SIGNATURE);
  
  {//debug
    int i;
    printf("\nOEM ID: ");
    for(i=0; i < 8; i++)
      printf("%c", mpctable->oemid[i]);
    printf("\nProduct ID: ");
    for(i=0; i < 12; i++)
      printf("%c", mpctable->productid[i]);
  }
  
  printf("\nEntry count=%u", mpctable->entrycount);
  printf("\nLAPIC base=0x%08x", mpctable->lapicaddr);
  
  //now step through CPU entries in the MP-table to determine
  //how many CPUs we have
  {
    int i;
    u32 addrofnextentry= (u32)mpctable + sizeof(MPCONFTABLE);
    
    for(i=0; i < mpctable->entrycount; i++){
      MPENTRYCPU *cpu = (MPENTRYCPU *)addrofnextentry;
      if(cpu->entrytype != 0)
        break;
      
      if(cpu->cpuflags & 0x1){
        printf("\nCPU (0x%08x) #%u: lapic id=0x%02x, ver=0x%02x, cpusig=0x%08x", 
          (u32)cpu, i, cpu->lapicid, cpu->lapicver, cpu->cpusig);
        pcpus[pcpus_numentries].lapic_id = cpu->lapicid;
        pcpus[pcpus_numentries].lapic_ver = cpu->lapicver;
        pcpus[pcpus_numentries].lapic_base = mpctable->lapicaddr;
        pcpus[pcpus_numentries].isbsp = cpu->cpuflags & 0x2;
        pcpus_numentries++;
      }
            
      addrofnextentry += sizeof(MPENTRYCPU);
    }
  }


fallthrough:
  return;  
  //debug
  //{
  //  int i;
  //  printf("\nCPU table:");
  //  for(i=0; i < pcpus_numentries; i++)
  //    printf("\nCPU #%u: bsp=%u, lapic_id=0x%02x", i, pcpus[i].isbsp, pcpus[i].lapic_id);
  //}
 
}

u32 _MPFPComputeChecksum(u32 spaddr, u32 size){
  char *p;
  char checksum=0;
  u32 i;

  p=(char *)spaddr;
  
  for(i=0; i< size; i++)
    checksum+= (char)(*(p+i));
  
  return (u32)checksum;
}


//get the MP FP structure
MPFP *MP_GetFPStructure(void){
  u16 ebdaseg;
  u32 ebdaphys;
  u32 i, found=0;
  MPFP *mpfp;
  
  //get EBDA segment from 040E:0000h in BIOS data area
  ebdaseg= * ((u16 *)0x0000040E);
  //convert it to its 32-bit physical address
  ebdaphys=(u32)(ebdaseg * 16);
  //search first 1KB of ebda for rsdp signature (4 bytes long)
  for(i=0; i < (1024-4); i+=16){
    mpfp=(MPFP *)(ebdaphys+i);
    if(mpfp->signature == MPFP_SIGNATURE){
      if(!_MPFPComputeChecksum((u32)mpfp, 16)){
        found=1;
        break;
      }
    }
  }
  
  if(found)
    return mpfp;
  
  //search within BIOS areas 0xE0000 to 0xFFFFF
  for(i=0xE0000; i < (0xFFFFF-4); i+=16){
    mpfp=(MPFP *)i;
    if(mpfp->signature == MPFP_SIGNATURE){
      if(!_MPFPComputeChecksum((u32)mpfp, 16)){
        found=1;
        break;
      }
    }
  }

  if(found)
    return mpfp;
  
  return (MPFP *)0;  
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

	printf("\nAMD-V-MP: loader initializaing...");
	printf("\ntotal modules:%u", mods_count);
  ASSERT(mods_count == 2);  //runtime and OS boot sector for the time-being

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
  lpb->XtVmmRuntimeSize = runtime_size_bytes;
  
  //store revised E820 map and number of entries
  memcpy((void *)lpb->XtVmmE820Buffer, (void *)grube820list, sizeof(grube820list));
  lpb->XtVmmE820NumEntries = grube820list_numentries; 

 	//setup guest OS boot module info in LPB	
  xsize = mod_array[1].mod_end - mod_array[1].mod_start;   
  printf("\nGuest OS Boot Module: size=%u, start=0x%08X", xsize, (u32)mod_array[1].mod_start);
	lpb->XtGuestOSBootModuleBase=mod_array[1].mod_start;
	lpb->XtGuestOSBootModuleSize=xsize;

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

  //debug
	printf("\nXtVmmGdt=0x%08X, XtVmmEntryPoint=0x%08X", lpb->XtVmmGdt,
			lpb->XtVmmEntryPoint);
	printf("\nXtVmmStackBase=0x%08X, XtVmmStackSize=0x%08X", 
		lpb->XtVmmStackBase, lpb->XtVmmStackSize);

  //transfer control to runtime
	XtLdrTransferControlToRtm(lpb->XtVmmGdt, lpb->XtVmmIdt, lpb->XtVmmEntryPoint, 
			lpb->XtVmmStackBase+lpb->XtVmmStackSize);	
	
	//we should never get here
	__asm__("hlt\r\n");
}
