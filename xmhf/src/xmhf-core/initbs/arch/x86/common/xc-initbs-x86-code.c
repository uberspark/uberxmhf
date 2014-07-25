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

/* 
 * XMHF core initbs (initialization-bootstrap) slab
 * x86 arch. backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-core.h>
#include <xc-x86.h>
#include <xc-x86vmx.h>

#include <xc-initbs.h>

#define __XMHF_SLAB_CALLER_INDEX__	XMHF_SLAB_INITBS_INDEX
#include <xc-coreapi.h>
#undef __XMHF_SLAB_CALLER_INDEX__






//initialize paging
void xmhf_baseplatform_arch_x86_initialize_paging(u32 pgtblbase){
	
	asm volatile(
		"movl	%%cr4, %%eax \r\n"
		"orl	$(0x00000030), %%eax \r\n"	//CR4_PAE | CR4_PSE
		"movl	%%eax, %%cr4 \r\n"
		"movl	%0, %%eax \r\n"				//EDI = page table base address
		"movl	%%eax, %%cr3 \r\n"			
		"movl   %%cr0, %%eax \r\n"
		"orl	$(0x80000015), %%eax \r\n"   // ET, EM, PE, PG
		"movl	%%eax, %%cr0 \r\n"	    	//turn on paging
		: //no outputs
		: "m" (pgtblbase)
		: "eax"
	);
	
}

//----------------------------------------------------------------------
//bplt-x86-smp

//return 1 if the calling CPU is the BSP
bool xmhf_baseplatform_arch_x86_isbsp(void){
  u32 eax, edx;
  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G
  
  if(eax & 0x100)
    return true;
  else
    return false;
}

//wake up APs using the LAPIC by sending the INIT-SIPI-SIPI IPI sequence
void xmhf_baseplatform_arch_x86_wakeupAPs(void){
  u32 eax, edx;
  volatile u32 *icr;
  
  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G

	//construct the command register address (offset 0x300)    
  icr = (u32 *) (((u32)eax & 0xFFFFF000UL) + 0x300);
    
  //our AP boot-strap code is at physical memory location 0x10000.
	//so use 0x10 as the vector (0x10000/0x1000 = 0x10)

  //send INIT
  #ifndef __XMHF_VERIFICATION__
	//TODO: plug in LAPIC h/w model
	*icr = 0x000c4500UL;
  #endif

  xmhf_baseplatform_arch_x86_udelay(10000);

  //wait for command completion
  #ifndef __XMHF_VERIFICATION__
	//TODO: plug in LAPIC h/w model
	  {
	    u32 val;
	    do{
	      val = *icr;
	    }while( (val & 0x1000) );
	  }
  #endif
  
  //send SIPI (twice as per the MP protocol)
  {
    int i;
    for(i=0; i < 2; i++){
      #ifndef __XMHF_VERIFICATION__
	//TODO: plug in LAPIC h/w model
	*icr = 0x000c4610UL;
      #endif
      xmhf_baseplatform_arch_x86_udelay(200);
        //wait for command completion
        #ifndef __XMHF_VERIFICATION__
		//TODO: plug in LAPIC h/w model
		{
		  u32 val;
		  do{
		    val = *icr;
		  }while( (val & 0x1000) );
		}
        #endif
      }
  }    

}


static mtrr_state_t _mtrrs;

void xmhf_baseplatform_arch_x86_savecpumtrrstate(void){
	save_mtrrs(&_mtrrs);
}

void xmhf_baseplatform_arch_x86_restorecpumtrrstate(void){
	restore_mtrrs(&_mtrrs);
}



/*originally within xc-initbs-apihub-x86.c */

extern u8 _slab_shareddata_memregion_start[];
extern u8 _slab_shareddata_memregion_end[];
extern u8 _slab_trampoline_memregion_start[];
extern u8 _slab_trampoline_memregion_end[];

//core PAE page tables
static u64 core_3level_pdpt[PAE_MAXPTRS_PER_PDPT] __attribute__(( aligned(4096) ));
static u64 core_3level_pdt[PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT] __attribute__(( aligned(4096) ));

static struct {
	u64 pdpt[PAE_MAXPTRS_PER_PDPT] __attribute__(( aligned(4096) ));
	u64 pdt[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT] __attribute__(( aligned(4096) ));
} _slab_pagetables[XMHF_SLAB_NUMBEROFSLABS];


#define	_SLAB_SPATYPE_OTHER_SLAB_MASK			(0xF0)

#define	_SLAB_SPATYPE_OTHER_SLAB_CODE			(0xF0)
#define	_SLAB_SPATYPE_OTHER_SLAB_RODATA			(0xF1)
#define _SLAB_SPATYPE_OTHER_SLAB_RWDATA			(0xF2)
#define _SLAB_SPATYPE_OTHER_SLAB_STACK			(0xF3)

#define	_SLAB_SPATYPE_SLAB_CODE					(0x0)
#define	_SLAB_SPATYPE_SLAB_RODATA				(0x1)
#define _SLAB_SPATYPE_SLAB_RWDATA				(0x2)
#define _SLAB_SPATYPE_SLAB_STACK				(0x3)

#define _SLAB_SPATYPE_SLAB_TRAMPOLINE			(0x4)

#define _SLAB_SPATYPE_NOTASLAB					(0xFF00)

static u32 _xcinitbs_slab_getspatype(u32 slab_index, u32 spa){
	u32 i;

	//slab memory regions
	for(i=0; i < XMHF_SLAB_NUMBEROFSLABS; i++){
		u32 mask = (i == slab_index) ? 0 : _SLAB_SPATYPE_OTHER_SLAB_MASK;
		
		if(spa >= _slab_table[i].slab_code.start  && spa < _slab_table[i].slab_code.end)
			return _SLAB_SPATYPE_SLAB_CODE | mask;
		if (spa >= _slab_table[i].slab_rodata.start  && spa < _slab_table[i].slab_rodata.end)
			return _SLAB_SPATYPE_SLAB_RODATA | mask;
		if (spa >= _slab_table[i].slab_rwdata.start  && spa < _slab_table[i].slab_rwdata.end)	
			return _SLAB_SPATYPE_SLAB_RWDATA | mask;
		if (spa >= _slab_table[i].slab_stack.start  && spa < _slab_table[i].slab_stack.end)	
			return _SLAB_SPATYPE_SLAB_STACK | mask;
	}	

	//slab shared data region 
	//TODO: add per shared data variable access policy rather than entire section
	if(spa >= (u32)_slab_shareddata_memregion_start && spa < (u32)_slab_shareddata_memregion_end){
			if (slab_index == XMHF_SLAB_INITBS_INDEX || slab_index == XMHF_SLAB_XCEXHUB_INDEX)
				return _SLAB_SPATYPE_SLAB_RWDATA; //map read-write in initbs (GDT,TSS setup) and xcexhub (IDT setup)
			else
				return _SLAB_SPATYPE_SLAB_RODATA; //map read-only in all other slabs 
	}

	//slab trampoline region
	if(spa >= (u32)_slab_trampoline_memregion_start && spa < (u32)_slab_trampoline_memregion_end){
			return _SLAB_SPATYPE_SLAB_TRAMPOLINE; //map read-only in all slabs 
	}
	

	return _SLAB_SPATYPE_NOTASLAB;
}

static u64 _xcinitbs_slab_getptflagsforspa(u32 slab_index, u32 spa){
	u64 flags;
	u32 spatype = _xcinitbs_slab_getspatype(slab_index, spa);
	//printf("\n%s: slab_index=%u, spa=%08x, spatype = %x\n", __FUNCTION__, slab_index, spa, spatype);
	
	switch(spatype){
		case _SLAB_SPATYPE_OTHER_SLAB_CODE:
		case _SLAB_SPATYPE_OTHER_SLAB_RODATA:
		case _SLAB_SPATYPE_OTHER_SLAB_RWDATA:
			flags = 0;	//not-present
			break;
		case _SLAB_SPATYPE_OTHER_SLAB_STACK:
			//flags = (u64)(_PAGE_PRESENT | _PAGE_PSE | _PAGE_NX); //present | read-only | no execute | pse
			flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_PSE | _PAGE_NX); //present | read-write | no execute | pse
			break;	
		
		case _SLAB_SPATYPE_SLAB_CODE:
			flags = (u64)(_PAGE_PRESENT | _PAGE_PSE); // present | read-only | pse
			break;
		case _SLAB_SPATYPE_SLAB_RODATA:
			flags = (u64)(_PAGE_PRESENT | _PAGE_PSE | _PAGE_NX); //present | read-only | no-execute | pse
			break;
		case _SLAB_SPATYPE_SLAB_RWDATA:
		case _SLAB_SPATYPE_SLAB_STACK:
			flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_NX | _PAGE_PSE); //present | read-write | no-execute | pse
			break;
		
		case _SLAB_SPATYPE_SLAB_TRAMPOLINE:
			flags = (u64)(_PAGE_PRESENT | _PAGE_PSE); //present | read-only | pse;
			break;
	
		default:
			flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_PSE);
			if(spa == 0xfee00000 || spa == 0xfec00000) {
				//map some MMIO regions with Page Cache disabled 
				//0xfed00000 contains Intel TXT config regs & TPM MMIO 
				//0xfee00000 contains LAPIC base 
				flags |= (u64)(_PAGE_PCD);
			}

			break;
	}
	
	return flags;
}


// initialize slab page tables for a given slab index, returns the macm base
static u32 _xcinitbs_slab_populate_pagetables(u32 slab_index){
		u32 i, j;
		u64 default_flags = (u64)(_PAGE_PRESENT);
		
		for(i=0; i < PAE_PTRS_PER_PDPT; i++)
			_slab_pagetables[slab_index].pdpt[i] = pae_make_pdpe(hva2spa(_slab_pagetables[slab_index].pdt[i]), default_flags);

		//init pdts with unity mappings
		for(i=0; i < PAE_PTRS_PER_PDPT; i++){
			for(j=0; j < PAE_PTRS_PER_PDT; j++){
				u32 hva = ((i * PAE_PTRS_PER_PDT) + j) * PAGE_SIZE_2M;
				u64 spa = hva2spa((void*)hva);
				u64 flags = _xcinitbs_slab_getptflagsforspa(slab_index, (u32)spa);
				_slab_pagetables[slab_index].pdt[i][j] = pae_make_pde_big(spa, flags);
			}
		}
	
		return (u32)_slab_pagetables[slab_index].pdpt;
}


// initialization function for the core API interface
void xmhf_apihub_arch_initialize (void){

#ifndef __XMHF_VERIFICATION__

	printf("\n%s: starting...", __FUNCTION__);

	//[debug]
	{
		u32 i;
		for(i=0; i < XMHF_SLAB_NUMBEROFSLABS; i++){
				printf("\nslab %u: pdpt=%08x, pdt[0]=%08x, pdt[1]=%08x", i, (u32)_slab_pagetables[i].pdpt, (u32)_slab_pagetables[i].pdt[0], (u32)_slab_pagetables[i].pdt[1]);
				printf("\n                    pdt[2]=%08x, pdt[3]=%08x", (u32)_slab_pagetables[i].pdt[2], (u32)_slab_pagetables[i].pdt[3]);
		}

	}


	//check for PCID support (if present)
	{
			u32 eax, ebx, ecx, edx;
			
			cpuid(0x1, &eax, &ebx, &ecx, &edx);
			
			if( ecx & (1UL << 17) )
				printf("\n%s: PCID supported", __FUNCTION__);
			else
				printf("\n%s: PCID not supported", __FUNCTION__);
	}

	//turn on WP bit in CR0 register for supervisor mode read-only permission support
	{
		u32 cr0;
		cr0=read_cr0();
		printf("\n%s: CR0=%08x", __FUNCTION__, cr0);
		cr0 |= CR0_WP;
		printf("\n%s: attempting to change CR0 to %08x", __FUNCTION__, cr0);
		write_cr0(cr0);
		cr0 = read_cr0();
		printf("\n%s: CR0 changed to %08x", __FUNCTION__, cr0);
	}

	//turn on NX protections
	{
		u32 eax, edx;
		rdmsr(MSR_EFER, &eax, &edx);
		eax |= (1 << EFER_NXE);
		wrmsr(MSR_EFER, eax, edx);
		printf("\n%s: NX protections enabled: MSR_EFER=%08x%08x", __FUNCTION__, edx, eax);
	}
	
	//setup slab page tables and macm id's
	{
		u32 i;
		for(i=0; i < XMHF_SLAB_NUMBEROFSLABS; i++)
			_slab_table[i].slab_macmid = _xcinitbs_slab_populate_pagetables(i);

		//_slab_table[XMHF_SLAB_INDEX_TEMPLATE].slab_macmid = _xcinitbs_slab_populate_pagetables(XMHF_SLAB_INDEX_TEMPLATE);
		//_slab_table[XMHF_SLAB_INITBS_INDEX].slab_macmid = _xcinitbs_slab_populate_pagetables(XMHF_SLAB_INITBS_INDEX);
		
	}
	
	printf("\n%s: setup slab page tables and macm id's\n", __FUNCTION__);
	
	
	//initialize paging
	xmhf_baseplatform_arch_x86_initialize_paging((u32)_slab_table[XMHF_SLAB_INITBS_INDEX].slab_macmid);
	printf("\n%s: setup slab paging\n", __FUNCTION__);

	
#endif //__XMHF_VERIFICATION__
}


	


