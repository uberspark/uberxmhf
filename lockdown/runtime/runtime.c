//------------------------------------------------------------------------------
// runtime.c
//
// intel vt-x hypervisor runtime
//
// author: amit vasudevan (amitvasudevan@acm.org)

#include <types.h>
#include <target.h>
#include <print.h>
#include <processor.h>
#include <msr.h>
#include <vtx.h>
#include <paging.h>
#include <io.h>
#include <str.h>
#include <machine.h>
#include <error.h>
#include "acpi.h"
#include <disk.h>




void runtime_printnum(unsigned long num){
	printf("\nnum=0x%08lx", num);
}

void runtime_idtexceptionhandler(unsigned long vector, unsigned long *stack){
	printf("\nruntime exception 0x%08lx (ESP=0x%08lx)", vector, 
		(unsigned long)stack);
	HALT();
}




void setupenvironment(void){
	//setup IDT
	printf("\nSetting up Runtime IDT...");
	{
		u32 *fptr, idtbase, i;
		fptr=(u32 *)__runtimeidt_functionpointers;
		idtbase= (u32)__runtimeidt_start;
		for(i=0; i < 32; i++){
			idtentry_t *idtentry=(idtentry_t *)((u32)idtbase+ (i*8));
			
				idtentry->isrLow= (u16)fptr[i];
				idtentry->isrHigh= (u16) ( (u32)fptr[i] >> 16 );
				idtentry->isrSelector = __CS;
				idtentry->count=0x0;
				idtentry->type=0x8E;
		}
	}		
	__asm__ __volatile__ ("lidt __runtimeidt\r\n");
	printf("Done.");

	//setup TSS descriptor and TR
	printf("\nSetting up runtime TSS descriptor and TR...");
	{
		TSSENTRY *t;
  	u32 tss_base=(u32)__runtimetss;

		//fix TSS descriptor, 18h
		t= (TSSENTRY *)((u32)__runtimegdt_start + __TRSEL );
	  t->attributes1= 0x89;
	  t->limit16_19attributes2= 0x10;
	  t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
	  t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
	  t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);      
	  t->limit0_15=0x67;

		__asm__ __volatile__("movw %0, %%ax\r\n"
				"ltr %%ax\r\n"
			: //none
			:"i"(__TRSEL)
		);
	}
	printf("Done.");	

	//setup paging (PAE)
	printf("\nsetting up PAE paging...");
	{
		pdpt_t pdpt;
		pdt_t  pdt;
		u32 paddr=0, i, j, y;
		u32 l_cr0, l_cr3, l_cr4;
		u64 flags;
	
		pdpt=(pdpt_t)__runtime_pdpt;
		pdt=(pdt_t)__runtime_pdts;
	
  	flags = (u64)(_PAGE_PRESENT);
  	//init pdpt
  	memset(__runtime_pdpt, 0, PAGE_SIZE_4K);
		for(i = 0; i < PAE_PTRS_PER_PDPT; i++){
	    y = (u32)(u32)pdt + (i << PAGE_SHIFT_4K);
    	pdpt[i] = pae_make_pdpe((u64)y, flags);
  	}
 
 		//init pdts with unity mappings
  	j  = ADDR_4GB >> (PAE_PDT_SHIFT);
  	flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_PSE);
  	for(i = 0, paddr = 0; i < j; i ++, paddr += PAGE_SIZE_2M)
    	pdt[i] = pae_make_pde_big((u64)paddr, flags);
		
		//load cr0, cr3 and cr4 with appropriate settings
	  l_cr4 = CR4_PSE | CR4_PAE;
  	l_cr0 = 0x80000021; // ET, EM, PE
	  l_cr3 = (u32)pdpt;
		write_cr3(l_cr3);
		write_cr4(l_cr4);
    write_cr0(l_cr0);
	}
	printf("Done.");

}




void cstartup(unsigned long bootmodule_start, unsigned long bootmodule_size, unsigned long bootmodule1_start, unsigned long bootmodule1_size);
void cstartup(unsigned long bootmodule_start, unsigned long bootmodule_size, unsigned long bootmodule1_start, unsigned long bootmodule1_size){
	//setup debugging	
#ifdef __DEBUG_SERIAL__	
	init_uart();
#endif

#ifdef __DEBUG_VGA__	
	vgamem_clrscr();
#endif

	printf("\nruntime:");
	printf("\ninitializing operating environment...");
	setupenvironment();
	printf("\noperating environment initialized!");

	//ACPI initialization
	ACPIInitializeRegisters();
	
	printf("\ninitializing VT...");
	if(!runtime_initVT()){
		printf("\nHALT: error initializing VT!");
		HALT();
	}
	printf("\nVT initialized!");

	
	/*printf("\nSetting up HOST...");
	runtime_setup_host();
	printf("\nHOST setup done!");

	printf("\nSetting up GUEST...");
	printf("\nCopying bootmodule(from 0x%08lx, size=0x%08lx",
		bootmodule_start, bootmodule_size);
	memcpy((void *)0x7c00, (void *)bootmodule_start, bootmodule_size);
	runtime_setup_guest();
	printf("\nGUEST setup done!");*/

#if defined(__CONF_SHADOW_PAGING__) && defined(__CONF_SHADOW_PAGING_NPAE_ALG0__)
	printf("\nInitializing shadow page tables for ALG0...");
	shadow_alg0_initialize();
#endif


#if !defined(__CONF_GUESTOS_LINUX__) 
	//switch to appropriate DBR depending on trusted and untrusted
	//bootmodule_start/size => untrusted
	//bootmodule1_start/size => trusted
	
	{
		extern u32 operatingmode;
		u8 destopmode;
		ata_resetdrives();
		printf("\ngetting current operating mode..");
		if(!DiskGetIndicator(1, &destopmode)){
			printf("\nfatal, unable to get operating mode");
			HALT();
		}
		
		//if(!DiskSetIndicator(1, __LDN_MODE_UNTRUSTED)){
		//	printf("\nfatal, unable to set mode back to default!");
		//	HALT();
		//}
		//printf("\nOPERATING MODE: %s", ("TRUSTED" ? (destopmode==__LDN_MODE_TRUSTED) : "UNTRUSTED"));
		operatingmode=destopmode;
		
		if( (operatingmode != __LDN_MODE_TRUSTED) && (operatingmode != __LDN_MODE_UNTRUSTED) ){
			printf("\nForcing Untrusted mode on bootup...");
			operatingmode = __LDN_MODE_UNTRUSTED;
		}
		
	}

	
	
	printf("\nCopying bootmodule(from 0x%08lx, size=0x%08lx",
		bootmodule_start, bootmodule_size);
	memcpy((void *)0x7c00, (void *)bootmodule_start, bootmodule_size);


#endif

	
	printf("\nPreparing VMCS for launch...");
	guest_currentstate=GSTATE_DEAD;
	guest_nextstate=GSTATE_REALMODE;
	guest_currentstate=isl_prepareVMCS(guest_currentstate, guest_nextstate);
	printf("\nDone.");


	printf("\nLaunching GUEST...");
	runtime_launch_guest();
	
	printf("\nHALT: runtime, we must never get here!");
	HALT();
}