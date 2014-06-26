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


/* originally within xc-baseplatform-x86.c */

//----------------------------------------------------------------------
// local variables

//core IDT
static u64 _idt_start[EMHF_XCPHANDLER_MAXEXCEPTIONS] __attribute__(( aligned(16) ));

//core IDT descriptor
arch_x86_idtdesc_t _idt __attribute__(( aligned(16) )) = {
	.size=sizeof(_idt_start)-1,
	.base=(u32)&_idt_start,
};

//runtime TSS
u8 _tss[PAGE_SIZE_4K] = { 0 };

//exclusive exception handling stack, we switch to this stack if there
//are any exceptions during hypapp execution
static u8 _exceptionstack[PAGE_SIZE_4K] __attribute__((section(".stack")));




//----------------------------------------------------------------------
// functions

//get CPU vendor
u32 xmhf_baseplatform_arch_x86_getcpuvendor(void){
	u32 vendor_dword1, vendor_dword2, vendor_dword3;
	u32 cpu_vendor;
	asm(	"xor	%%eax, %%eax \n"
				  "cpuid \n"		
				  "mov	%%ebx, %0 \n"
				  "mov	%%edx, %1 \n"
				  "mov	%%ecx, %2 \n"
			     :	//no inputs
					 : "m"(vendor_dword1), "m"(vendor_dword2), "m"(vendor_dword3)
					 : "eax", "ebx", "ecx", "edx" );

	if(vendor_dword1 == AMD_STRING_DWORD1 && vendor_dword2 == AMD_STRING_DWORD2
			&& vendor_dword3 == AMD_STRING_DWORD3)
		cpu_vendor = CPU_VENDOR_AMD;
	else if(vendor_dword1 == INTEL_STRING_DWORD1 && vendor_dword2 == INTEL_STRING_DWORD2
			&& vendor_dword3 == INTEL_STRING_DWORD3)
		cpu_vendor = CPU_VENDOR_INTEL;
	else{
		printf("\n%s: unrecognized x86 CPU (0x%08x:0x%08x:0x%08x). HALT!",
			__FUNCTION__, vendor_dword1, vendor_dword2, vendor_dword3);
		HALT();
	}   	 	

	return cpu_vendor;
}

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

//----------------------------------------------------------------------

//initialize CR0
void xmhf_baseplatform_arch_x86_initializeCR0(){
	
	
}



// GDT
static u64 _gdt_start[] __attribute__(( aligned(16) )) = {
	0x0000000000000000ULL,	//NULL descriptor
	0x00cf9b000000ffffULL,	//CPL-0 code descriptor (CS)
	0x00cf93000000ffffULL,	//CPL-0 data descriptor (DS/SS/ES/FS/GS)
	0x00cffb000000ffffULL,	//CPL-3 code descriptor (CS)
	0x00cff3000000ffffULL,	//CPL-3 data descriptor (DS/SS/ES/FS/GS)
	0x0000000000000000ULL	
};

// GDT descriptor
arch_x86_gdtdesc_t _gdt __attribute__(( aligned(16) )) = {
	.size=sizeof(_gdt_start)-1,
	.base=(u32)&_gdt_start,
};

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
//----------------------------------------------------------------------


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

//initialize IDT
void xmhf_baseplatform_arch_x86_initializeIDT(void){

	asm volatile(
		"lidt  %0 \r\n"
		: //no outputs
		: "m" (_idt)
		: //no clobber
	);
	
}


//initialize TR/TSS
void xmhf_baseplatform_arch_x86_initializeTSS(void){

	{
		u32 i;
		//u32 tss_base=(u32)&g_runtime_TSS;
		u32 tss_base=(u32)&_tss;
		TSSENTRY *t;
		tss_t *tss= (tss_t *)_tss;
		
		//extern u64 x_gdt_start[];
	
		//memset((void *)_tss, 0, sizeof(_tss));
		tss->ss0 = __DS_CPL0;
		tss->esp0 = (u32)&_exceptionstack + (u32)sizeof(_exceptionstack);
		
	
		printf("\ndumping GDT...");
		for(i=0; i < 6; i++)
			printf("\n    entry %u -> %016llx", i, _gdt_start[i]);
		printf("\nGDT dumped.");

		printf("\nfixing TSS descriptor (TSS base=%x)...", tss_base);
		t= (TSSENTRY *)(u32)&_gdt_start[(__TRSEL/sizeof(u64))];
		t->attributes1= 0xE9;
		t->limit16_19attributes2= 0x0;
		t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
		t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
		t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);      
		t->limit0_15=0x67;
		printf("\nTSS descriptor fixed.");

		printf("\ndumping GDT...");
		for(i=0; i < 6; i++)
			printf("\n    entry %u -> %016llx", i, _gdt_start[i]);
		printf("\nGDT dumped.");

		/*printf("\nsetting TR...");
		  __asm__ __volatile__("movw %0, %%ax\r\n"
			"ltr %%ax\r\n"				//load TR
			 : 
			 : "g"(__TRSEL)
			 : "eax"
		  );
		printf("\nTR set successfully");*/
		
	}

}

//initialize paging
void xmhf_baseplatform_arch_x86_initialize_paging(u32 pgtblbase){
	
	asm volatile(
		"movl	$(0x00000030), %%eax \r\n"	//CR4_PAE | CR4_PSE
		"movl	%%eax, %%cr4 \r\n"
		"movl	%0, %%eax \r\n"				//EDI = page table base address
		"movl	%%eax, %%cr3 \r\n"			
		"movl	$(0x80000015), %%eax \r\n"   // ET, EM, PE, PG
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
#define _SLAB_SPATYPE_OTHER_SLAB_TRAMPOLINE		(0xF4)

#define	_SLAB_SPATYPE_SLAB_CODE					(0x0)
#define	_SLAB_SPATYPE_SLAB_RODATA				(0x1)
#define _SLAB_SPATYPE_SLAB_RWDATA				(0x2)
#define _SLAB_SPATYPE_SLAB_STACK				(0x3)
#define _SLAB_SPATYPE_SLAB_TRAMPOLINE			(0x4)

#define _SLAB_SPATYPE_NOTASLAB					(0xFF00)

static u32 _xcinitbs_slab_getspatype(u32 slab_index, u32 spa){
	u32 i;

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
		if (spa >= _slab_table[i].slab_trampoline.start  && spa < _slab_table[i].slab_trampoline.end)	
			return _SLAB_SPATYPE_SLAB_TRAMPOLINE | mask;
	}	

	return _SLAB_SPATYPE_NOTASLAB;
}

static u64 _xcinitbs_slab_getptflagsforspa(u32 slab_index, u32 spa){
	u64 flags;
	u32 spatype = _xcinitbs_slab_getspatype(slab_index, spa);
	
	switch(spatype){
		case _SLAB_SPATYPE_OTHER_SLAB_CODE:
		case _SLAB_SPATYPE_OTHER_SLAB_RODATA:
		case _SLAB_SPATYPE_OTHER_SLAB_RWDATA:
			flags = 0;	//not-present
			break;
		case _SLAB_SPATYPE_OTHER_SLAB_STACK:
			flags = (u64)(_PAGE_PRESENT | _PAGE_PSE | _PAGE_NX); //present | read-only | no execute | pse
			break;	
		case _SLAB_SPATYPE_OTHER_SLAB_TRAMPOLINE:
			flags = (u64)(_PAGE_PRESENT | _PAGE_PSE);	//present | read-only | pse
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
	
	//setup slab page tables and macm id's
	{
		u32 i;
		for(i=0; i < XMHF_SLAB_NUMBEROFSLABS; i++)
			_slab_table[i].slab_macmid = _xcinitbs_slab_populate_pagetables(i);
	}
	
/*	
	for(i=0; i < numofslabs; i++){
			//for each slab with index i
			_xcinitbs_slab_populate_pagetables(i);
	}
	
	_xcinitbs_slab_populate_pagetables{
		for(i=0; i < PAE_PTRS_PER_PDPT; i++)
			_slab_pagetables[slab_index].pdpt[i] = pae_make_pdpe(hva2spa(_slab_pagetables[slab_index].pdt[i]), default_flags);

		//init pdts with unity mappings
		for(i=0; i < PAE_PTRS_PER_PDPT; i++){
			for(j=0; j < PAE_PTRS_PER_PDT; j++){
				u32 hva = ((i * PAE_PTRS_PER_PDT) + j) * PAGE_SIZE_2M;
				u64 spa = hva2spa((void*)hva);
				u64 flags = getflagsforspa(spa);
						
				_slab_pagetables[slab_index].pdt[i][j] = pae_make_pde_big(spa, flags);
			}
		}
		
	}

	getflagsforspa(spa){
					switch(spa){
					case OTHER_SLAB_CODE:
					case OTHER_SLAB_RODATA:
					case OTHER_SLAB_RWDATA:
						default_flags = 0;
					case OTHER_SLAB_TRAMPOLINE:
						default_flags = present | read-only | pse;
					case OTHER_SLAB_STACK:
						default_flags = present | read-only | no execute | pse;
						
					case MY_SLAB_CODE:
						default_flags = present | read-only | pse;
					case MY_SLAB_RODATA:
						default_flags = present | read-only | no-execute | pse;
					case MY_SLAB_RWDATA:
					case MY_SLAB_STACK:
						default_flags = present | read-write | no-execute | pse;
					case MY_SLAB_TRAMPOLINE:
						default_flags = present | read-only | pse;
						
					case SHARED_SLAB_RODATA:
						default_flags = present | read-only | no-execute | pse;
					case OTHER
						default_flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_PSE | _PAGE_USER);
				}
	}
*/		
	
		
	//initialize paging
	xmhf_baseplatform_arch_x86_initialize_paging((u32)_slab_pagetables[0].pdpt);
	

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

#endif //__XMHF_VERIFICATION__
}





/* originally within xc-xcphandler-x86.c */

#define XMHF_EXCEPTION_HANDLER_DEFINE(vector) 												\
	static void __xmhf_exception_handler_##vector(void) __attribute__((naked)) { 					\
		asm volatile(	"pushal	\r\n"								\
						"movw	%0, %%ax\r\n"						\
						"movw	%%ax, %%ds\r\n"						\
						"movl 	%%esp, %%eax\r\n"					\
						"pushl 	%%eax\r\n"							\
						"pushl	%1\r\n" 							\
						"call	xmhf_xcphandler_arch_hub\r\n"			\
						"addl  	$0x08, %%esp\r\n"					\
						"popal	 \r\n"								\
						"iretl\r\n"									\
					:												\
					:	"i" (__DS_CPL0), "i" (vector)				\
		);															\
	}\

#define XMHF_EXCEPTION_HANDLER_ADDROF(vector) &__xmhf_exception_handler_##vector

XMHF_EXCEPTION_HANDLER_DEFINE(0)
XMHF_EXCEPTION_HANDLER_DEFINE(1)
XMHF_EXCEPTION_HANDLER_DEFINE(2)
XMHF_EXCEPTION_HANDLER_DEFINE(3)
XMHF_EXCEPTION_HANDLER_DEFINE(4)
XMHF_EXCEPTION_HANDLER_DEFINE(5)
XMHF_EXCEPTION_HANDLER_DEFINE(6)
XMHF_EXCEPTION_HANDLER_DEFINE(7)
XMHF_EXCEPTION_HANDLER_DEFINE(8)
XMHF_EXCEPTION_HANDLER_DEFINE(9)
XMHF_EXCEPTION_HANDLER_DEFINE(10)
XMHF_EXCEPTION_HANDLER_DEFINE(11)
XMHF_EXCEPTION_HANDLER_DEFINE(12)
XMHF_EXCEPTION_HANDLER_DEFINE(13)
XMHF_EXCEPTION_HANDLER_DEFINE(14)
XMHF_EXCEPTION_HANDLER_DEFINE(15)
XMHF_EXCEPTION_HANDLER_DEFINE(16)
XMHF_EXCEPTION_HANDLER_DEFINE(17)
XMHF_EXCEPTION_HANDLER_DEFINE(18)
XMHF_EXCEPTION_HANDLER_DEFINE(19)
XMHF_EXCEPTION_HANDLER_DEFINE(20)
XMHF_EXCEPTION_HANDLER_DEFINE(21)
XMHF_EXCEPTION_HANDLER_DEFINE(22)
XMHF_EXCEPTION_HANDLER_DEFINE(23)
XMHF_EXCEPTION_HANDLER_DEFINE(24)
XMHF_EXCEPTION_HANDLER_DEFINE(25)
XMHF_EXCEPTION_HANDLER_DEFINE(26)
XMHF_EXCEPTION_HANDLER_DEFINE(27)
XMHF_EXCEPTION_HANDLER_DEFINE(28)
XMHF_EXCEPTION_HANDLER_DEFINE(29)
XMHF_EXCEPTION_HANDLER_DEFINE(30)
XMHF_EXCEPTION_HANDLER_DEFINE(31)
	
static u32 exceptionstubs[] = { 	XMHF_EXCEPTION_HANDLER_ADDROF(0),
							XMHF_EXCEPTION_HANDLER_ADDROF(1),
							XMHF_EXCEPTION_HANDLER_ADDROF(2),
							XMHF_EXCEPTION_HANDLER_ADDROF(3),
							XMHF_EXCEPTION_HANDLER_ADDROF(4),
							XMHF_EXCEPTION_HANDLER_ADDROF(5),
							XMHF_EXCEPTION_HANDLER_ADDROF(6),
							XMHF_EXCEPTION_HANDLER_ADDROF(7),
							XMHF_EXCEPTION_HANDLER_ADDROF(8),
							XMHF_EXCEPTION_HANDLER_ADDROF(9),
							XMHF_EXCEPTION_HANDLER_ADDROF(10),
							XMHF_EXCEPTION_HANDLER_ADDROF(11),
							XMHF_EXCEPTION_HANDLER_ADDROF(12),
							XMHF_EXCEPTION_HANDLER_ADDROF(13),
							XMHF_EXCEPTION_HANDLER_ADDROF(14),
							XMHF_EXCEPTION_HANDLER_ADDROF(15),
							XMHF_EXCEPTION_HANDLER_ADDROF(16),
							XMHF_EXCEPTION_HANDLER_ADDROF(17),
							XMHF_EXCEPTION_HANDLER_ADDROF(18),
							XMHF_EXCEPTION_HANDLER_ADDROF(19),
							XMHF_EXCEPTION_HANDLER_ADDROF(20),
							XMHF_EXCEPTION_HANDLER_ADDROF(21),
							XMHF_EXCEPTION_HANDLER_ADDROF(22),
							XMHF_EXCEPTION_HANDLER_ADDROF(23),
							XMHF_EXCEPTION_HANDLER_ADDROF(24),
							XMHF_EXCEPTION_HANDLER_ADDROF(25),
							XMHF_EXCEPTION_HANDLER_ADDROF(26),
							XMHF_EXCEPTION_HANDLER_ADDROF(27),
							XMHF_EXCEPTION_HANDLER_ADDROF(28),
							XMHF_EXCEPTION_HANDLER_ADDROF(29),
							XMHF_EXCEPTION_HANDLER_ADDROF(30),
							XMHF_EXCEPTION_HANDLER_ADDROF(31),
};
						

//initialize EMHF core exception handlers
void xmhf_xcphandler_arch_initialize(void){
	u32 *pexceptionstubs;
	u32 i;

	printf("\n%s: setting up runtime IDT...", __FUNCTION__);
	
	for(i=0; i < EMHF_XCPHANDLER_MAXEXCEPTIONS; i++){
		idtentry_t *idtentry=(idtentry_t *)((u32)xmhf_baseplatform_arch_x86_getidtbase()+ (i*8));
		idtentry->isrLow= (u16)exceptionstubs[i];
		idtentry->isrHigh= (u16) ( (u32)exceptionstubs[i] >> 16 );
		idtentry->isrSelector = __CS_CPL0;
		idtentry->count=0x0;
		idtentry->type=0xEE;	//32-bit interrupt gate
								//present=1, DPL=11b, system=0, type=1110b
	}
	
	printf("\n%s: IDT setup done.", __FUNCTION__);
}


/* originally in xc-ihub-xcphandler-x86.c */

static void xmhf_xcphandler_arch_unhandled(u32 vector, struct regs *r){
	u32 exception_cs, exception_eip, exception_eflags, errorcode=0;

	if(vector == CPU_EXCEPTION_DF ||
		vector == CPU_EXCEPTION_TS ||
		vector == CPU_EXCEPTION_NP ||
		vector == CPU_EXCEPTION_SS ||
		vector == CPU_EXCEPTION_GP ||
		vector == CPU_EXCEPTION_PF ||
		vector == CPU_EXCEPTION_AC){
		errorcode = *(uint32_t *)(r->esp+0);
		r->esp += sizeof(uint32_t);	//skip error code on stack if applicable
	}

	exception_eip = *(uint32_t *)(r->esp+0);
	exception_cs = *(uint32_t *)(r->esp+sizeof(uint32_t));
	exception_eflags = *(uint32_t *)(r->esp+(2*sizeof(uint32_t)));

	printf("\nunhandled exception %x, halting!", vector);
	printf("\nstate dump follows...");
	//things to dump
	printf("\nCS:EIP 0x%04x:0x%08x with EFLAGS=0x%08x, errorcode=%08x", (u16)exception_cs, exception_eip, exception_eflags, errorcode);
	printf("\nCR0=%08x, CR2=%08x, CR3=%08x, CR4=%08x", read_cr0(), read_cr2(), read_cr3(), read_cr4());
	printf("\nEAX=0x%08x EBX=0x%08x ECX=0x%08x EDX=0x%08x", r->eax, r->ebx, r->ecx, r->edx);
	printf("\nESI=0x%08x EDI=0x%08x EBP=0x%08x ESP=0x%08x", r->esi, r->edi, r->ebp, r->esp);
	printf("\nCS=0x%04x, DS=0x%04x, ES=0x%04x, SS=0x%04x", (u16)read_segreg_cs(), (u16)read_segreg_ds(), (u16)read_segreg_es(), (u16)read_segreg_ss());
	printf("\nFS=0x%04x, GS=0x%04x", (u16)read_segreg_fs(), (u16)read_segreg_gs());
	printf("\nTR=0x%04x", (u16)read_tr_sel());

	//do a stack dump in the hopes of getting more info.
	{
		uint32_t i;
		uint32_t stack_start = r->esp;
		printf("\n-----stack dump (16 entries)-----");
		for(i=stack_start; i < stack_start+(16*sizeof(uint32_t)); i+=sizeof(uint32_t)){
			printf("\nStack(0x%08x) -> 0x%08x", i, *(uint32_t *)i);
		}
		printf("\n-----end------------");
	}
	HALT();
}

//exception handler hub
void xmhf_xcphandler_arch_hub(u32 vector, struct regs *r){
	switch(vector){
			case CPU_EXCEPTION_NMI:{
				xc_coreapi_arch_eventhandler_nmiexception(r);
				}
				break;

			default:{
				xmhf_xcphandler_arch_unhandled(vector, r);
				//we will never get here
			}
	}
}
