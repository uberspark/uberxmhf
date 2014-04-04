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

/*//[REFACTOR]
//move this into bplt-x86-vmx.c
//initialize basic platform elements
void xmhf_baseplatform_arch_initialize(void){
	//initialize PCI subsystem
	xmhf_baseplatform_arch_x86_pci_initialize();
	
	//check ACPI subsystem
	{
		ACPI_RSDP rsdp;
		#ifndef __XMHF_VERIFICATION__
			//TODO: plug in a BIOS data area map/model
			if(!xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp)){
				printf("\n%s: ACPI RSDP not found, Halting!", __FUNCTION__);
				HALT();
			}
		#endif //__XMHF_VERIFICATION__
	}

}*/

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

//initialize TR/TSS
void xmhf_baseplatform_arch_x86_initializeTR(void){

	{
		u32 i;
		u32 tss_base=(u32)&g_runtime_TSS;
		TSSENTRY *t;
		extern u64 x_gdt_start[];
		
		printf("\ndumping GDT...");
		for(i=0; i < 6; i++)
			printf("\n    entry %u -> %016llx", i, x_gdt_start[i]);
		printf("\nGDT dumped.");

		printf("\nfixing TSS descriptor (TSS base=%x)...", tss_base);
		t= (TSSENTRY *)(u32)&x_gdt_start[(__TRSEL/sizeof(u64))];
		t->attributes1= 0xE9;
		t->limit16_19attributes2= 0x0;
		t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
		t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
		t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);      
		t->limit0_15=0x67;
		printf("\nTSS descriptor fixed.");

		printf("\ndumping GDT...");
		for(i=0; i < 6; i++)
			printf("\n    entry %u -> %016llx", i, x_gdt_start[i]);
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

/*//[REFACTOR]
//move this into bplt-x86-vmx-smp.c
//initialize SMP
void xmhf_baseplatform_arch_smpinitialize(void){
  u32 cpu_vendor;
  
  //grab CPU vendor
  cpu_vendor = xmhf_baseplatform_arch_getcpuvendor();
  HALT_ON_ERRORCOND(cpu_vendor == CPU_VENDOR_AMD || cpu_vendor == CPU_VENDOR_INTEL);

  
  //setup Master-ID Table (MIDTABLE)
  {
    int i;
	#ifndef __XMHF_VERIFICATION__
		for(i=0; i < (int)rpb->XtVmmMPCpuinfoNumEntries; i++){
			g_midtable[g_midtable_numentries].cpu_lapic_id = g_cpumap[i].lapic_id;
			g_midtable[g_midtable_numentries].vcpu_vaddr_ptr = 0;
			g_midtable_numentries++;
		}
	#else
	//verification is always done in the context of a single core and vcpu/midtable is 
	//populated by the verification driver
	//TODO: incorporate some sort of BIOS data area within the verification harness that will
	//allow us to populate these tables during verification
	#endif
    
    	
    
    
  }


  //allocate and setup VCPU structure on each CPU
  if(cpu_vendor == CPU_VENDOR_AMD)
	xmhf_baseplatform_arch_x86svm_allocandsetupvcpus(cpu_vendor);
  else //CPU_VENDOR_INTEL
	xmhf_baseplatform_arch_x86vmx_allocandsetupvcpus(cpu_vendor);

	//signal that basic base platform data structure initialization is complete 
	//(used by the exception handler component)
	g_bplt_initiatialized = true;

  //wake up APS
  if(g_midtable_numentries > 1){
    if(cpu_vendor == CPU_VENDOR_AMD)
	  xmhf_baseplatform_arch_x86svm_wakeupAPs();
    else //CPU_VENDOR_INTEL
	  xmhf_baseplatform_arch_x86vmx_wakeupAPs();
  }


  //fall through to common code  
  {
	 void _ap_pmode_entry_with_paging(void);
   printf("\nRelinquishing BSP thread and moving to common...");
   // Do some low-level init and then call allcpus_common_start() below
   _ap_pmode_entry_with_paging(); 
   printf("\nBSP must never get here. HALT!");
   HALT();
  }
}
*/

static mtrr_state_t g_mtrrs;


//common function which is entered by all CPUs upon SMP initialization
//note: this is specific to the x86 architecture backend
void xmhf_baseplatform_arch_x86_smpinitialize_commonstart(VCPU *vcpu){
	  //step:1 rally all APs up, make sure all of them started, this is
  //a task for the BSP
  if(xmhf_baseplatform_arch_x86_isbsp()){
    vcpu->isbsp = 1;	//this core is a BSP
    
	printf("\nBSP rallying APs...");
    printf("\nBSP(0x%02x): My ESP is 0x%08x", vcpu->id, vcpu->esp);

	save_mtrrs(&g_mtrrs);
	printf("\nBSP MTRRs");
	print_mtrrs(&g_mtrrs);

    //increment a CPU to account for the BSP
    spin_lock(&g_lock_cpus_active);
    g_cpus_active++;
    spin_unlock(&g_lock_cpus_active);

    //wait for g_cpus_active to become g_midtable_numentries -1 to indicate
    //that all APs have been successfully started
    while(g_cpus_active < g_midtable_numentries);
    
    printf("\nAPs all awake...Setting them free...");
    spin_lock(&g_lock_ap_go_signal);
    g_ap_go_signal=1;
    spin_unlock(&g_lock_ap_go_signal);

  
  }else{
    //we are an AP, so we need to simply update the AP startup counter
    //and wait until we are told to proceed
    //increment active CPUs
	vcpu->isbsp=0;	//this core is a AP

    spin_lock(&g_lock_cpus_active);
    g_cpus_active++;
    spin_unlock(&g_lock_cpus_active);

    while(!g_ap_go_signal); //Just wait for the BSP to tell us all is well.
 
    printf("\nAP(0x%02x): My ESP is 0x%08x, proceeding...", vcpu->id, vcpu->esp);
  
	restore_mtrrs(&g_mtrrs);
	printf("\nAP(0x%02x): MTRRs synced with BSP", vcpu->id);
  }
	
  //invoke EMHF runtime component main function for this CPU
  //[x] TODO: don't reference rpb->isEarlyInit directly
  //xmhf_runtime_main(vcpu, rpb->isEarlyInit);	
  {
	//partition_desc_t partdesc;
	//cpu_desc_t cpudesc;
	context_desc_t context_desc;
	
	context_desc.partition_desc.id = 0;
	context_desc.cpu_desc.id = vcpu->idx;
	context_desc.cpu_desc.isbsp = vcpu->isbsp;
		
	//partdesc.id = 0;
	//cpudesc.id = vcpu->idx;
	//cpudesc.isbsp = vcpu->isbsp;
	  
	//xmhf_runtime_main(partdesc, cpudesc);  
	xmhf_runtime_main(context_desc);
  }
}

//----------------------------------------------------------------------
/*
 * XMHF base platform SMP protected mode trampoline
 * this is where all CPUs enter in protected mode
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

extern arch_x86_gdtdesc_t x_gdt;

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
					: "m" (x_gdt), "m" (xmhf_xcphandler_idt), "i" (MSR_APIC_BASE), "m" (g_midtable_numentries), "i" (&g_midtable)
	);

	
}

