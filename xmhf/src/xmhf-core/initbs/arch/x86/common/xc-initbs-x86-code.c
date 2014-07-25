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



//initialize CPU state
void xmhf_baseplatform_arch_x86_cpuinitialize(void){
	//u32 cpu_vendor = xmhf_baseplatform_arch_getcpuvendor();

	//set OSXSAVE bit in CR4 to enable us to pass-thru XSETBV intercepts
	//when the CPU supports XSAVE feature
	if(xmhf_baseplatform_arch_x86_cpuhasxsavefeature()){
		u32 t_cr4;
		t_cr4 = read_cr4();
		t_cr4 |= CR4_OSXSAVE;	
		write_cr4(t_cr4);
	}

	//turn on NX protections via MSR EFER
	//note: on BSP NX protections are turned on much before we get here, but on APs this is the place we
	//set NX protections on
	{
		u32 eax, edx;
		rdmsr(MSR_EFER, &eax, &edx);
		eax |= (1 << EFER_NXE);
		wrmsr(MSR_EFER, eax, edx);
		printf("\n%s: NX protections enabled: MSR_EFER=%08x%08x", __FUNCTION__, edx, eax);
	}	

}


//initialize GDT
void xmhf_baseplatform_arch_x86_initializeGDT(void){
	
	asm volatile(
		"lgdt  %0 \r\n"
		"pushl	%1 \r\n"				// far jump to runtime entry point
		"pushl	$reloadsegs \r\n"
		"lret \r\n"
		"reloadsegs: \r\n"
		"movw	%2, %%ax \r\n"
		"movw	%%ax, %%ds \r\n"	
		"movw	%%ax, %%es \r\n"
		"movw	%%ax, %%fs \r\n"
		"movw	%%ax, %%gs \r\n"
		"movw  %%ax, %%ss \r\n"
		: //no outputs
		: "m" (_gdt), "i" (__CS_CPL0), "i" (__DS_CPL0)
		: //no clobber
	);

	
}

//initialize IO privilege level
void xmhf_baseplatform_arch_x86_initializeIOPL(void){
	
	asm volatile(
		"pushl	$0x3000 \r\n"					// clear flags, but set IOPL=3 (CPL-3)
		"popf \r\n"
		: //no outputs
		: //no inputs
		: //no clobber
	);
	
	
}

//initialize TR/TSS
void xmhf_baseplatform_arch_x86_initializeTSS(void){
		u32 i;
		u32 tss_base=(u32)&_tss;
		TSSENTRY *t;
		tss_t *tss= (tss_t *)_tss;
		
		tss->ss0 = __DS_CPL0;
		tss->esp0 = (u32)_slab_table[XMHF_SLAB_XCEXHUB_INDEX].slab_tos;

		printf("\nfixing TSS descriptor (TSS base=%x)...", tss_base);
		t= (TSSENTRY *)(u32)&_gdt_start[(__TRSEL/sizeof(u64))];
		t->attributes1= 0xE9;
		t->limit16_19attributes2= 0x0;
		t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
		t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
		t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);      
		t->limit0_15=0x67;
		printf("\nTSS descriptor fixed.");

}

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


//--------------------------------------------------------------------------------------
//bootstrap exception handling without SMP support
//only designed until real SMP exception handler slab (xcexhub) can take control

__attribute__((section(".libxmhfdebugdata"))) __attribute__(( aligned(4096) )) static u8 _xcinitbs_exception_stack[PAGE_SIZE_4K];
__attribute__((section(".libxmhfdebugdata"))) __attribute__(( aligned(4096) )) static u32 _xcinitbs_exception_stack_index = &_xcinitbs_exception_stack + PAGE_SIZE_4K;

#define XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(vector) 												\
	__attribute__(( section(".slab_trampoline") )) static void __xcinitbs_exception_handler_##vector(void) __attribute__((naked)) { 					\
		asm volatile(												\
						"xchg   %0, %%esp \r\n"						\
						"pushal \r\n"								\
						"pushl %%esp \r\n"							\
						"pushl  %0 \r\n"							\
						"movl %%cr3, %%ebx \r\n"					\
						"pushl %%ebx		\r\n"					\
						"movl	%1, %%ebx\r\n"						\
						"movl	%%ebx, %%cr3\r\n"					\
						"pushl	%2\r\n" 							\
						"call	xmhf_xcinitbs_xcphandler_arch_hub\r\n"		\
						"addl $4, %%esp \r\n"						\
						"popl %%ebx \r\n"							\
						"movl  %%ebx, %%cr3 \r\n"					\
						"addl $8, %%esp \r\n"						\
						"popal \r\n"								\
						"xchg	%0, %%esp \r\n"						\
						"iretl \r\n"								\
					:												\
					:	"m" (_xcinitbs_exception_stack_index), "m" (_slab_table[XMHF_SLAB_INITBS_INDEX].slab_macmid), "i" (vector)				\
		);															\
	}\


#define XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(vector) &__xcinitbs_exception_handler_##vector

XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(0)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(1)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(2)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(3)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(4)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(5)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(6)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(7)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(8)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(9)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(10)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(11)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(12)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(13)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(14)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(15)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(16)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(17)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(18)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(19)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(20)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(21)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(22)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(23)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(24)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(25)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(26)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(27)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(28)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(29)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(30)
XMHF_INITBS_EXCEPTION_HANDLER_DEFINE(31)
	
static u32 __xcinitbs_exceptionstubs[] = { 	XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(0),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(1),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(2),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(3),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(4),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(5),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(6),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(7),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(8),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(9),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(10),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(11),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(12),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(13),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(14),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(15),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(16),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(17),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(18),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(19),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(20),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(21),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(22),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(23),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(24),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(25),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(26),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(27),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(28),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(29),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(30),
							XMHF_INITBS_EXCEPTION_HANDLER_ADDROF(31),
};


//initialize basic exception handling
void xcinitbs_initialize_exceptionhandling(void){
	u32 *pexceptionstubs;
	u32 i;

	for(i=0; i < EMHF_XCPHANDLER_MAXEXCEPTIONS; i++){
		idtentry_t *idtentry=(idtentry_t *)((u32)&_idt_start+ (i*8));
		idtentry->isrLow= (u16)__xcinitbs_exceptionstubs[i];
		idtentry->isrHigh= (u16) ( (u32)__xcinitbs_exceptionstubs[i] >> 16 );
		idtentry->isrSelector = __CS_CPL0;
		idtentry->count=0x0;
		idtentry->type=0xEE;	//32-bit interrupt gate
								//present=1, DPL=11b, system=0, type=1110b
	}

	//load IDT
	asm volatile(
		"lidt  %0 \r\n"
		: //no outputs
		: "m" (_idt)
		: //no clobber
	);
}
					

__attribute__(( section(".slab_trampoline") )) static void xmhf_xcinitbs_xcphandler_arch_unhandled(u32 vector, u32 orig_cr3, u32 orig_esp, struct regs *r){
	u32 exception_cs, exception_eip, exception_eflags, errorcode=0;

	if(vector == CPU_EXCEPTION_DF ||
		vector == CPU_EXCEPTION_TS ||
		vector == CPU_EXCEPTION_NP ||
		vector == CPU_EXCEPTION_SS ||
		vector == CPU_EXCEPTION_GP ||
		vector == CPU_EXCEPTION_PF ||
		vector == CPU_EXCEPTION_AC){
		errorcode = *(uint32_t *)(orig_esp+0);
		orig_esp += sizeof(uint32_t);	//skip error code on stack if applicable
	}

	exception_eip = *(uint32_t *)(orig_esp+0);
	exception_cs = *(uint32_t *)(orig_esp+sizeof(uint32_t));
	exception_eflags = *(uint32_t *)(orig_esp+(2*sizeof(uint32_t)));

	printf("\nunhandled exception %x, halting!", vector);
	printf("\nstate dump follows...");
	//things to dump
	printf("\nCS:EIP 0x%04x:0x%08x with EFLAGS=0x%08x, errorcode=%08x", (u16)exception_cs, exception_eip, exception_eflags, errorcode);
	printf("\nCR0=%08x, CR2=%08x, CR3=%08x, CR4=%08x", read_cr0(), read_cr2(), orig_cr3, read_cr4());
	printf("\nEAX=0x%08x EBX=0x%08x ECX=0x%08x EDX=0x%08x", r->eax, r->ebx, r->ecx, r->edx);
	printf("\nESI=0x%08x EDI=0x%08x EBP=0x%08x ESP=0x%08x", r->esi, r->edi, r->ebp, orig_esp);
	printf("\nCS=0x%04x, DS=0x%04x, ES=0x%04x, SS=0x%04x", (u16)read_segreg_cs(), (u16)read_segreg_ds(), (u16)read_segreg_es(), (u16)read_segreg_ss());
	printf("\nFS=0x%04x, GS=0x%04x", (u16)read_segreg_fs(), (u16)read_segreg_gs());
	printf("\nTR=0x%04x", (u16)read_tr_sel());

	//do a stack dump in the hopes of getting more info.
	{
		uint32_t i;
		uint32_t stack_start = orig_esp;
		printf("\n-----stack dump (16 entries)-----");
		for(i=stack_start; i < stack_start+(16*sizeof(uint32_t)); i+=sizeof(uint32_t)){
			printf("\nStack(0x%08x) -> 0x%08x", i, *(uint32_t *)i);
		}
		printf("\n-----end------------");
	}
}

//exception handler hub
__attribute__(( section(".slab_trampoline") )) void xmhf_xcinitbs_xcphandler_arch_hub(u32 vector, u32 orig_cr3, u32 orig_esp, struct regs *r){
	
	switch(vector){
		case 0x3:
			xmhf_xcinitbs_xcphandler_arch_unhandled(vector, orig_cr3, orig_esp, r);
			printf("Int3 dbgprint -- continue\n");
			break;
		
		default:
			xmhf_xcinitbs_xcphandler_arch_unhandled(vector, orig_cr3, orig_esp, r);
			printf("\nHalting System!\n");
			HALT();
	}
	
}
	


