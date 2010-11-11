// runtime.c
// author: amit vasudevan (amitvasudevan@acm.org)

//---includes-------------------------------------------------------------------
#include <target.h>


//---forward declarations-------------------------------------------------------
void cstartup(void);
u32 isbsp(void);


//---globals referenced by this module------------------------------------------
extern u8 __midtable[];
extern u8 __grube820buffer[];
extern u8 __mp_cpuinfo[];	
extern PXTLPB	lpb;
extern GRUBE820 *grube820list;
extern PCPU *pcpus;
extern MIDTAB *midtable;
extern u32 midtable_numentries;
extern APP_PARAM_BLOCK appParamBlock;
extern u8 bufferOptionalModule[];

extern u8 memregion_vcpubuffers[];
extern u8 memregion_cpustacks[];
extern u8 memregion_vmx_vmxon_buffers[];
extern u8 memregion_vmx_vmcs_buffers[];
extern u8 memregion_vmx_iobitmap[];
extern u8 memregion_vmx_msr_area_host[];
extern u8 memregion_vmx_msr_area_guest[];
extern u8 memregion_vmx_msrbitmaps[];
extern u8 memregion_vmx_ept_pml4_table[];
extern u8 memregion_vmx_ept_pdp_table[];
extern u8 memregion_vmx_ept_pd_tables[];
extern u8 memregion_vmx_ept_p_tables[];

extern u8 memregion_v86m_pagedir[];
extern u8 memregion_v86m_pagetables[];
extern u8 memregion_v86m_idt[];
extern u8 memregion_v86m_gdt[];
extern u8 memregion_v86m_ldt[];
extern u8 memregion_v86m_tss[];
extern u8 memregion_v86m_ring0stack[];
extern u8 memregion_limbo_gdt[];
extern u8 memregion_limbo_tss[];


extern u32 appmain_success_counter;
extern u32 lock_appmain_success_counter;


//---function to obtain the vcpu of the currently executing core----------------
//note: this always returns a valid VCPU pointer
VCPU *getvcpu(void){
  int i;
  u32 eax, edx, *lapic_reg;
  u32 lapic_id;
  
  //read LAPIC id of this core
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  ASSERT( edx == 0 ); //APIC is below 4G
  eax &= (u32)0xFFFFF000UL;
  lapic_reg = (u32 *)((u32)eax+ (u32)LAPIC_ID);
  lapic_id = *lapic_reg;
  //printf("\n%s: lapic base=0x%08x, id reg=0x%08x", __FUNCTION__, eax, lapic_id);
  lapic_id = lapic_id >> 24;
  //printf("\n%s: lapic_id of core=0x%02x", __FUNCTION__, lapic_id);
  
  for(i=0; i < (int)midtable_numentries; i++){
    if(midtable[i].cpu_lapic_id == lapic_id)
        return( (VCPU *)midtable[i].vcpu_vaddr_ptr );
  }

  printf("\n%s: fatal, unable to retrieve vcpu for id=0x%02x", __FUNCTION__, lapic_id);
  HALT();
}



//---microsecond delay----------------------------------------------------------
void udelay(u32 usecs){
  u8 val;
  u32 latchregval;  

  //enable 8254 ch-2 counter
  val = inb(0x61);
  val &= 0x0d; //turn PC speaker off
  val |= 0x01; //turn on ch-2
  outb(val, 0x61);
  
  //program ch-2 as one-shot
  outb(0xB0, 0x43);
  
  //compute appropriate latch register value depending on usecs
  latchregval = (1193182 * usecs) / 1000000;

  //write latch register to ch-2
  val = (u8)latchregval;
  outb(val, 0x42);
  val = (u8)((u32)latchregval >> (u32)8);
  outb(val , 0x42);
  
  //wait for countdown
  while(!(inb(0x61) & 0x20));
  
  //disable ch-2 counter
  val = inb(0x61);
  val &= 0x0c;
  outb(val, 0x61);
}

//---wakeupAPs------------------------------------------------------------------
void wakeupAPs(void){
  u32 eax, edx;
  volatile u32 *icr;
  
  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  ASSERT( edx == 0 ); //APIC is below 4G
  printf("\nLAPIC base and status=0x%08x", eax);
    
  icr = (u32 *) (((u32)eax & 0xFFFFF000UL) + 0x300);
    
  {
    //extern u32 ap_code_start[], ap_code_end[];
    //memcpy(0x10000, (void *)ap_code_start, (u32)ap_code_end - (u32)ap_code_start + 1);
    extern u32 _ap_bootstrap_start[], _ap_bootstrap_end[];
    extern u32 _ap_cr3_value, _ap_cr4_value;
    _ap_cr3_value = read_cr3();
    _ap_cr4_value = read_cr4();
    memcpy((void *)0x10000, (void *)_ap_bootstrap_start, (u32)_ap_bootstrap_end - (u32)_ap_bootstrap_start + 1);
  
  }

  //our test code is at 1000:0000, we need to send 10 as vector
  //send INIT
  printf("\nSending INIT...");
  *icr = 0x000c4500UL;
  udelay(10000);
  //wait for command completion
  {
    u32 val;
    do{
      val = *icr;
    }while( (val & 0x1000) );
  }
  printf("\nINIT IPI sent successfully.");

  //send SIPI (twice as per the MP protocol)
  {
    int i;
    for(i=0; i < 2; i++){
      printf("\nSending SIPI-%u...", i);
      *icr = 0x000c4610UL;
      udelay(200);
        //wait for command completion
        {
          u32 val;
          do{
            val = *icr;
          }while( (val & 0x1000) );
        }
        printf("\nSIPI-%u IPI sent successfully.", i);
      }
  }    
    
  printf("\nAPs should be awake!");
}


//---setup vcpu structures for all the cores including BSP----------------------
void setupvcpus(MIDTAB *midtable, u32 midtable_numentries){
  u32 i;
  VCPU *vcpu;
  
	//ASSERT(midtable_numentries == 1);
	
  for(i=0; i < midtable_numentries; i++){
    //allocate VCPU structure
		vcpu = (VCPU *)((u32)memregion_vcpubuffers + (u32)(i * SIZE_STRUCT_VCPU));
    memset((void *)vcpu, 0, sizeof(VCPU));
    
    //allocate runtime stack
    vcpu->esp = ((u32)memregion_cpustacks + (i * RUNTIME_STACK_SIZE)) + RUNTIME_STACK_SIZE;    

    //allocate VMXON memory region
    vcpu->vmxonregion_vaddr = ((u32)memregion_vmx_vmxon_buffers + (i * PAGE_SIZE_4K)) ;
    memset((void *)vcpu->vmxonregion_vaddr, 0, PAGE_SIZE_4K);
    
		//allocate VMCS memory region
		vcpu->vmcs_vaddr = ((u32)memregion_vmx_vmcs_buffers + (i * PAGE_SIZE_4K)) ;
    memset((void *)vcpu->vmcs_vaddr, 0, PAGE_SIZE_4K);
		
		//allocate VMX IO bitmap region
		vcpu->vmx_vaddr_iobitmap = ((u32)memregion_vmx_iobitmap + (i * (2*PAGE_SIZE_4K))) ; 
		memset( (void *)vcpu->vmx_vaddr_iobitmap, 0, (2*PAGE_SIZE_4K));
		
		//allocate VMX guest and host MSR save areas
		vcpu->vmx_vaddr_msr_area_host = ((u32)memregion_vmx_msr_area_host + (i * (2*PAGE_SIZE_4K))) ; 
		memset( (void *)vcpu->vmx_vaddr_msr_area_host, 0, (2*PAGE_SIZE_4K));
		vcpu->vmx_vaddr_msr_area_guest = ((u32)memregion_vmx_msr_area_guest + (i * (2*PAGE_SIZE_4K))) ; 
		memset( (void *)vcpu->vmx_vaddr_msr_area_guest, 0, (2*PAGE_SIZE_4K));

		//allocate VMX MSR bitmap region
		vcpu->vmx_vaddr_msrbitmaps = ((u32)memregion_vmx_msrbitmaps + (i * PAGE_SIZE_4K)) ; 
		memset( (void *)vcpu->vmx_vaddr_msrbitmaps, 0, PAGE_SIZE_4K);
		
		//allocate EPT paging structures
		#ifdef __NESTED_PAGING__		
		{
			vcpu->vmx_vaddr_ept_pml4_table = ((u32)memregion_vmx_ept_pml4_table + (i * PAGE_SIZE_4K));
			vcpu->vmx_vaddr_ept_pdp_table = ((u32)memregion_vmx_ept_pdp_table + (i * PAGE_SIZE_4K));  
			vcpu->vmx_vaddr_ept_pd_tables = ((u32)memregion_vmx_ept_pd_tables + (i * (PAGE_SIZE_4K*4))); 		
			vcpu->vmx_vaddr_ept_p_tables = ((u32)memregion_vmx_ept_p_tables + (i * (PAGE_SIZE_4K*2048))); 
		}
		#endif

		//allocate v86 monitor paging structures, GDT, IDT, LDT and TSS and stack
		vcpu->v86m.vaddr_pagedir= ((u32)memregion_v86m_pagedir + (i * PAGE_SIZE_4K));
		vcpu->v86m.vaddr_pagetables= ((u32)memregion_v86m_pagetables + (i * (1024*PAGE_SIZE_4K)));
		vcpu->v86m.vaddr_idt=((u32)memregion_v86m_idt + (i * PAGE_SIZE_4K));
		vcpu->v86m.vaddr_gdt=((u32)memregion_v86m_gdt+ (i * PAGE_SIZE_4K));
		vcpu->v86m.vaddr_ldt=((u32)memregion_v86m_ldt + (i * PAGE_SIZE_4K));
		vcpu->v86m.vaddr_tss=((u32)memregion_v86m_tss + (i * (4 * PAGE_SIZE_4K)));
		vcpu->vaddr_v86m_ring0stack=((u32)memregion_v86m_ring0stack + (i * (4*PAGE_SIZE_4K)));		 

		//allocate limbo gdt and tss
		vcpu->v86m.vaddr_limbo_gdt=((u32)memregion_limbo_gdt + (i * LIMBO_GDT_SIZE));
		vcpu->v86m.vaddr_limbo_tss=((u32)memregion_limbo_tss + (i * LIMBO_TSS_SIZE));
		
		    

    //other VCPU data such as LAPIC id, SIPI vector and receive indication
    vcpu->id = midtable[i].cpu_lapic_id;
    vcpu->sipivector = 0;
    vcpu->sipireceived = 0;

    midtable[i].vcpu_vaddr_ptr = (u32)vcpu;	//map LAPIC to VCPU in midtable
    
		//printf("\nCPU #%u: vcpu_vaddr_ptr=0x%08x, esp=0x%08x", i, midtable[i].vcpu_vaddr_ptr,
    //  vcpu->esp);
  }
}



//---runtime main---------------------------------------------------------------
void cstartup(void){
	//setup debugging	
#ifdef __DEBUG_SERIAL__	
	init_uart();
#endif
	printf("\nruntime initializing...");

  //debug, dump E820 and MP table
 	printf("\nNumber of E820 entries = %u", lpb->XtVmmE820NumEntries);
  {
    int i;
    for(i=0; i < (int)lpb->XtVmmE820NumEntries; i++){
      printf("\n0x%08x%08x, size=0x%08x%08x (%u)", 
          grube820list[i].baseaddr_high, grube820list[i].baseaddr_low,
          grube820list[i].length_high, grube820list[i].length_low,
          grube820list[i].type);
    }
  
  }
  printf("\nNumber of MP entries = %u", lpb->XtVmmMPCpuinfoNumEntries);
  {
    int i;
    for(i=0; i < (int)lpb->XtVmmMPCpuinfoNumEntries; i++)
      printf("\nCPU #%u: bsp=%u, lapic_id=0x%02x", i, pcpus[i].isbsp, pcpus[i].lapic_id);
  }

  //setup Master-ID Table (MIDTABLE)
  {
    int i;
    midtable_numentries=0;
		for(i=0; i < (int)lpb->XtVmmMPCpuinfoNumEntries; i++){
       midtable[midtable_numentries].cpu_lapic_id = pcpus[i].lapic_id;
       midtable[midtable_numentries].vcpu_vaddr_ptr = 0;
       midtable_numentries++;
    }
  }

  //setup vcpus
  setupvcpus(midtable, midtable_numentries);

	//debug dump midtable
	{
		u32 i;
		printf("\nMIDTABLE dump:");
		for(i=0; i < midtable_numentries; i++){
			printf("\nCPU #0x%02x: lapicid=0x%02x, vcpu vaddr=0x%08x",
				i, midtable[i].cpu_lapic_id, midtable[i].vcpu_vaddr_ptr);
		}
	}

#if 1
  //copy bootsector to default BIOS location
  printf("\nBSP: copying boot-module to BIOS default 0000:7C00");
	memcpy((void *)__GUESTOSBOOTMODULE_BASE, (void *)lpb->XtGuestOSBootModuleBase, lpb->XtGuestOSBootModuleSize);

  //if there is an optional module, copy its contents into our local buffer
  //this is needed as app_main is invoked within the context of every CPU
  //if we leave this optional buffer at the default GRUB location, there are
  //chances that the buffer can be overwritten by an already started CPU
  //when app_main gets control on another CPU. this may be undesirable if
  //this optional module is used as a source of parameter-passing to app_main
  //note: this should not apply to the boot-sector as that should normally
  //be preserved by the guest OS bootup code.
  if(lpb->XtGuestOSBootModuleSizeSup1){
    printf("\nBSP: copying option boot-module to runtime buffer");
	  memcpy((void *)&bufferOptionalModule, (void *)lpb->XtGuestOSBootModuleBaseSup1, lpb->XtGuestOSBootModuleSizeSup1);
  } 
#endif

  //initialize application parameter block
  appParamBlock.bootsector_ptr = (u32)lpb->XtGuestOSBootModuleBase;
  appParamBlock.bootsector_size = (u32)lpb->XtGuestOSBootModuleSize;
  appParamBlock.optionalmodule_ptr = (u32)lpb->XtGuestOSBootModuleBaseSup1;
  appParamBlock.optionalmodule_size = (u32)lpb->XtGuestOSBootModuleSizeSup1;
 	appParamBlock.runtimephysmembase = (u32)lpb->XtVmmRuntimePhysBase;  

  //wake up APS
  if(midtable_numentries > 1)
   wakeupAPs();

  //fall through to common code  
  {
	 void _ap_pmode_entry_with_paging(void);
   printf("\nRelinquishing BSP thread and moving to common...");
   _ap_pmode_entry_with_paging();
   printf("\nBSP must never get here. HALT!");
   HALT();
  }
}


//---isbsp----------------------------------------------------------------------
//returns 1 if the calling CPU is the BSP, else 0
u32 isbsp(void){
  u32 eax, edx;
  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  ASSERT( edx == 0 ); //APIC is below 4G
  
  if(eax & 0x100)
    return 1;
  else
    return 0;
}

u32 cpus_active=0; //number of CPUs that are awake, should be equal to
                  //midtable_numentries -1 if all went well with the
                  //MP startup protocol
u32 lock_cpus_active=1; //spinlock to access the above

u32 ap_go_signal=0; //go signal becomes 1 after BSP finishes rallying
u32 lock_ap_go_signal=1; //spunlock to access the above



//---allcpus_common_start-------------------------------------------------------
void allcpus_common_start(VCPU *vcpu){
  //we start here with all CPUs executing common code, we 
  //will make BSP distinction based on isbsp macro which basically
  //reads the LAPIC MSR to see if it is the BSP
 
  
  //step:1 rally all APs up, make sure all of them started, this is
  //a task for the BSP
  if(isbsp()){
    vcpu->isbsp=1;
    
		printf("\nCPU(0x%02x): BSP, rallying APs...", vcpu->id);
    printf("\nCPU(0x%02x): My ESP is 0x%08x", vcpu->id, vcpu->esp);

    //increment a CPU to account for the BSP
    spin_lock(&lock_cpus_active);
    cpus_active++;
    spin_unlock(&lock_cpus_active);

    //wait for cpus_active to become midtable_numentries -1 to indicate
    //that all APs have been successfully started
    while(cpus_active < midtable_numentries);
    
    printf("\nCPU(0x%02x): APs all awake...Setting them free...", vcpu->id);
    spin_lock(&lock_ap_go_signal);
    ap_go_signal=1;
    spin_unlock(&lock_ap_go_signal);

  
  }else{
    //we are an AP, so we need to simply update the AP startup counter
    //and wait until we are told to proceed
    //increment active CPUs
    vcpu->isbsp = 0;
    
		printf("\nCPU(0x%02x): AP, My ESP is 0x%08x, waiting for BSP rally...", vcpu->id, vcpu->esp);

		//update CR0 for VMX compatibility, CR4 is automatically updated by
		//AP boot-up code
		{
			u32 bcr0, acr0;
			bcr0 = read_cr0();
			bcr0 |= 0x20;
			write_cr0(bcr0);
			acr0 = read_cr0();
			printf("\nCPU(0x%02x): AP, CR0 before=0x%08x, after=0x%08x",
				vcpu->id, bcr0, acr0);
		
		}

		spin_lock(&lock_cpus_active);
    cpus_active++;
    spin_unlock(&lock_cpus_active);

    while(!ap_go_signal);
 
    printf("\nCPU(0x%02x): AP, BSP rally done. proceeding...", vcpu->id, vcpu->esp);

  }

  
	//isolation layer initialization
	printf("\nCPU(0x%02x): initializing isolation layer...", vcpu->id);
	isl_initialize(vcpu);
	printf("\nCPU(0x%02x): isolation layer initialized.", vcpu->id);
 
	//currently runtime protection in EPT is only for unrestricted guest caps.
	if(vcpu->guest_unrestricted){
		//protect runtime memory region from guest 
		printf("\nCPU(0x%02x): runtime physical base=0x%08x, size=0x%08x bytes",
			vcpu->id, (u32)lpb->XtVmmRuntimePhysBase, (u32)lpb->XtVmmRuntimeSize); 
		{
			u32 i;
			for(i=0; i < (u32)lpb->XtVmmRuntimeSize; i+=PAGE_SIZE_4K)
				emhf_hwpgtbl_setprot(vcpu, ((u32)lpb->XtVmmRuntimePhysBase+i), 0x0);
			emhf_hwpgtbl_flushall(vcpu);
		}
		printf("\nCPU(0x%02x): Setup runtime protection within EPTs", vcpu->id);
	}
	
  //call app main
  if(emhf_app_main(vcpu, &appParamBlock)){
    printf("\nCPU(0x%02x): Application failed to initialize. HALT!", vcpu->id);
    HALT();
  }

	//increment app main success counter
	spin_lock(&lock_appmain_success_counter);
  appmain_success_counter++;
  spin_unlock(&lock_appmain_success_counter);
	
	//wait for all cores to go through app main
	if(isbsp()){
		printf("\nCPU(0x%02x): Waiting for all cores to cycle through appmain...", vcpu->id);
		while(appmain_success_counter < midtable_numentries);	
		printf("\nCPU(0x%02x): All cores have successfully been through appmain.", vcpu->id);
	}

#if defined (__MP_VERSION__)  
	//if we are the BSP setup SIPI intercept
  if(isbsp()){
    #if 1
		//quiesce testing when all cores are in hypervisor mode
		printf("\nCPU(0x%02x): Testing quiescing...", vcpu->id);
		do_quiesce(vcpu);
		printf("\nCPU(0x%02x): Quiesce test done.", vcpu->id);
		#endif
		
    apic_setup(vcpu);

  }else{ //else, we are an AP and wait for SIPI signal
    printf("\nCPU(0x%02x): waiting for SIPI signal...", vcpu->id);
    while(!vcpu->sipireceived);
    printf("\nCPU(0x%02x): SIPI signal received, vector=0x%02x", vcpu->id, vcpu->sipivector);
		//update VMCS with startup CS:IP
 		vcpu->vmcs.guest_RIP = 0x0ULL;
		vcpu->vmcs.guest_CS_selector = (vcpu->sipivector * PAGE_SIZE_4K) >> 4;
		vcpu->vmcs.guest_CS_base = (vcpu->sipivector * PAGE_SIZE_4K);
	}
#endif
	
  //start HVM
  {
    void startHVM(VCPU *vcpu, u32 vmcs_phys_addr);
    printf("\nCPU(0x%02x): Starting HVM...", vcpu->id);
    startHVM(vcpu, __hva2spa__(vcpu->vmcs_vaddr));
    printf("\nCPU(0x%02x): FATAL, should not be here. HALTING!", vcpu->id);
    HALT();
  }
}