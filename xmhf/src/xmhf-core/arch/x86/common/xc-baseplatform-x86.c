/*
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
 * XMHF base platform component (x86 common arch. backend)
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf-core.h>
#include <xc-x86.h>

//----------------------------------------------------------------------
// local variables

//core IDT
static u64 _idt_start[EMHF_XCPHANDLER_MAXEXCEPTIONS] __attribute__(( section(".data"), aligned(16) ));

//core IDT descriptor
static arch_x86_idtdesc_t _idt __attribute__(( section(".data"), aligned(16) )) = {
	.size=sizeof(_idt_start)-1,
	.base=(u32)&_idt_start,
};

//runtime TSS
u8 _tss[PAGE_SIZE_4K] __attribute__(( section(".data") )) = { 0 };

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
	u32 cpu_vendor = xmhf_baseplatform_arch_getcpuvendor();

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
static arch_x86_gdtdesc_t _gdt __attribute__(( aligned(16) )) = {
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
void xmhf_baseplatform_arch_x86_initializeTR(void){

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

		printf("\nsetting TR...");
		  __asm__ __volatile__("movw %0, %%ax\r\n"
			"ltr %%ax\r\n"				//load TR
			 : 
			 : "g"(__TRSEL)
			 : "eax"
		  );
		printf("\nTR set successfully");
		
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
u32 xmhf_baseplatform_arch_x86_isbsp(void){
  u32 eax, edx;
  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G
  
  if(eax & 0x100)
    return 1;
  else
    return 0;
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

u32 xmhf_baseplatform_arch_x86_getcpulapicid(void){
  u32 eax, edx, *lapic_reg;
  u32 lapic_id;
  
  //read LAPIC id of this core
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G
  eax &= (u32)0xFFFFF000UL;
  lapic_reg = (u32 *)((u32)eax+ (u32)LAPIC_ID);
  lapic_id = xmhfhw_sysmemaccess_readu32((u32)lapic_reg);
  lapic_id = lapic_id >> 24;
	
  return lapic_id;
}

//void xmhf_baseplatform_arch_x86_smpinitialize_commonstart(u32 index_cpudata){
//
//	printf("\n%s: index_cpudata=%u, top of stack=%08x, Halting!", __FUNCTION__, index_cpudata, read_esp());
//	HALT();
//}


//common function which is entered by all CPUs upon SMP initialization
//note: this is specific to the x86 architecture backend
//void xmhf_baseplatform_arch_x86_smpinitialize_commonstart(VCPU *vcpu){
void xmhf_baseplatform_arch_x86_smpinitialize_commonstart(u32 index_cpudata){
	context_desc_t context_desc;
	VCPU *vcpu = &g_bplt_vcpu[index_cpudata];

	vcpu->idx = index_cpudata;

	if(xmhf_baseplatform_arch_x86_isbsp()){
		vcpu->isbsp = 1;	//this core is a BSP
	}else{
		vcpu->isbsp = 0; // this core is a AP
	}	

	//replicate common MTRR state on this CPU
	xmhf_baseplatform_arch_x86_restorecpumtrrstate();
  	
	context_desc.partition_desc.id = 0;
	context_desc.cpu_desc.id = vcpu->idx;
	context_desc.cpu_desc.isbsp = vcpu->isbsp;

	xmhf_runtime_main(context_desc);
}

//----------------------------------------------------------------------
/*
 * XMHF base platform SMP protected mode trampoline
 * this is where all CPUs enter in protected mode
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

//extern arch_x86_gdtdesc_t x_gdt;

/*void _ap_pmode_entry_with_paging(void) __attribute__((naked)){

    asm volatile(	"lgdt %0\r\n"
					"lidt %1\r\n"
					"mov %2, %%ecx\r\n"
					"rdmsr\r\n"
					"andl $0xFFFFF000, %%eax\r\n"
					"addl $0x20, %%eax\r\n"
					"movl (%%eax), %%eax\r\n"
					"shr $24, %%eax\r\n"
					"movl %3, %%edx\r\n"
					"movl %4, %%ebx\r\n"
					"xorl %%ecx, %%ecx\r\n"
					"getvcpuloop:\r\n"
					"movl 0x0(%%ebx, %%ecx, 8), %%ebp\r\n"  	//ebp contains the lapic id
					"cmpl %%eax, %%ebp\r\n"
					"jz gotvcpu\r\n"
					"incl %%ecx\r\n"
					"cmpl %%edx, %%ecx\r\n"
					"jb getvcpuloop\r\n"
					"hlt\r\n"								//we should never get here, if so just halt
					"gotvcpu:\r\n"
					"movl 0x4(%%ebx, %%ecx, 8), %%esi\r\n"	 	//esi contains vcpu pointer
					"movl 0x0(%%esi), %%esp\r\n"     			//load stack for this CPU
					"pushl %%esi\r\n"
					"call xmhf_baseplatform_arch_x86_smpinitialize_commonstart\r\n"
					"hlt\r\n"								//we should never get here, if so just halt
					:
					: "m" (_gdt), "m" (_idt), "i" (MSR_APIC_BASE), "m" (g_midtable_numentries), "i" (&g_midtable)
	);

	
}*/

void _ap_pmode_entry_with_paging(void) __attribute__((naked)){

    asm volatile(	"lgdt %0\r\n"
					"lidt %1\r\n"
					"mov %2, %%ecx\r\n"
					"rdmsr\r\n"
					"andl $0xFFFFF000, %%eax\r\n"
					"addl $0x20, %%eax\r\n"
					"movl (%%eax), %%eax\r\n"
					"shr $24, %%eax\r\n"
					"movl %3, %%edx\r\n"
					"movl %4, %%ebx\r\n"
					"xorl %%ecx, %%ecx\r\n"
					"xorl %%edi, %%edi\r\n"
					"getidxloop:\r\n"
					"movl 0x0(%%ebx, %%edi), %%ebp\r\n"  	//ebp contains the lapic id
					"cmpl %%eax, %%ebp\r\n"
					"jz gotidx\r\n"
					"incl %%ecx\r\n"
					"addl %5, %%edi\r\n"
					"cmpl %%edx, %%ecx\r\n"
					"jb getidxloop\r\n"
					"hlt\r\n"								//we should never get here, if so just halt
					"gotidx:\r\n"
					"movl 0x4(%%ebx, %%edi), %%esi\r\n"	 	//esi contains index_cpudata
					"movl %6, %%ebx \r\n"					//ebx = &g_xc_cpustack
					"movl %7, %%eax \r\n"					//eax = sizeof(g_xc_cpustack[0])
					"mull %%ecx \r\n"						//ecx = index_cpudata, edx:eax = index_cpudata * sizeof(g_xc_cpustack[0])
					"addl %%eax, %%ebx \r\n"				//ebx = &g_xc_cpustack[index_cpudata]
					"addl %7, %%ebx \r\n"					//ebx = &g_xc_cpustack[index_cpudata] + sizeof(g_xc_cpustack[0]) 
					"movl %%ebx, %%esp \r\n"				//esp = ebx (stack for the cpu with index_cpudata)
					"pushl %%esi\r\n"						//index_cpudata
					"call xmhf_baseplatform_arch_x86_smpinitialize_commonstart\r\n"
					"hlt\r\n"								//we should never get here, if so just halt
					:
					: "m" (_gdt), "m" (_idt), "i" (MSR_APIC_BASE), "m" (g_xc_cpu_count), "i" (&g_xc_cputable), "i" (sizeof(MIDTAB)), "i" (&g_xc_cpustack), "i" (sizeof(g_xc_cpustack[0]))
	);

	
}



u32 xmhf_baseplatform_arch_x86_getgdtbase(void){
		return (u32)&_gdt_start;
}

u32 xmhf_baseplatform_arch_x86_getidtbase(void){
		return (u32)&_idt_start;
}

u32 xmhf_baseplatform_arch_x86_gettssbase(void){
		return (u32)&_tss;
}
