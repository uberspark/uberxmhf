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
 * EMHF base platform component interface, x86 backend
 * implements SMP functionality
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>

//return 1 if the calling CPU is the BSP
u32 emhf_baseplatform_arch_x86_isbsp(void){
  u32 eax, edx;
  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  ASSERT( edx == 0 ); //APIC is below 4G
  
  if(eax & 0x100)
    return 1;
  else
    return 0;
}

//wake up APs using the LAPIC by sending the INIT-SIPI-SIPI IPI sequence
void emhf_baseplatform_arch_x86_wakeupAPs(void){
  u32 eax, edx;
  volatile u32 *icr;
  
  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  ASSERT( edx == 0 ); //APIC is below 4G

	//construct the command register address (offset 0x300)    
  icr = (u32 *) (((u32)eax & 0xFFFFF000UL) + 0x300);
    
  //our AP boot-strap code is at physical memory location 0x10000.
	//so use 0x10 as the vector (0x10000/0x1000 = 0x10)

  //send INIT
  *icr = 0x000c4500UL;
  emhf_baseplatform_arch_x86_udelay(10000);
  //wait for command completion
  {
    u32 val;
    do{
      val = *icr;
    }while( (val & 0x1000) );
  }

  //send SIPI (twice as per the MP protocol)
  {
    int i;
    for(i=0; i < 2; i++){
      *icr = 0x000c4610UL;
      emhf_baseplatform_arch_x86_udelay(200);
        //wait for command completion
        {
          u32 val;
          do{
            val = *icr;
          }while( (val & 0x1000) );
        }
      }
  }    
}


//initialize SMP
void emhf_baseplatform_arch_smpinitialize(void){
  u32 cpu_vendor;
  
  //grab CPU vendor
  cpu_vendor = emhf_baseplatform_arch_getcpuvendor();
  ASSERT(cpu_vendor == CPU_VENDOR_AMD || cpu_vendor == CPU_VENDOR_INTEL);
  
  //setup Master-ID Table (MIDTABLE)
  {
    int i;
    for(i=0; i < (int)rpb->XtVmmMPCpuinfoNumEntries; i++){
       g_midtable[g_midtable_numentries].cpu_lapic_id = g_cpumap[i].lapic_id;
       g_midtable[g_midtable_numentries].vcpu_vaddr_ptr = 0;
       g_midtable_numentries++;
    }
  }

  //allocate and setup VCPU structure on each CPU
  if(cpu_vendor == CPU_VENDOR_AMD)
	emhf_baseplatform_arch_x86svm_allocandsetupvcpus(cpu_vendor);
  else //CPU_VENDOR_INTEL
	emhf_baseplatform_arch_x86vmx_allocandsetupvcpus(cpu_vendor);
	
  
  //wake up APS
  if(g_midtable_numentries > 1){
    if(cpu_vendor == CPU_VENDOR_AMD)
	  emhf_baseplatform_arch_x86svm_wakeupAPs();
    else //CPU_VENDOR_INTEL
	  emhf_baseplatform_arch_x86vmx_wakeupAPs();
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


//common function which is entered by all CPUs upon SMP initialization
//note: this is specific to the x86 architecture backend
void emhf_baseplatform_arch_x86_smpinitialize_commonstart(VCPU *vcpu){
	  //step:1 rally all APs up, make sure all of them started, this is
  //a task for the BSP
  if(emhf_baseplatform_arch_x86_isbsp()){
    vcpu->isbsp = 1;	//this core is a BSP
    
	printf("\nBSP rallying APs...");
    printf("\nBSP(0x%02x): My ESP is 0x%08x", vcpu->id, vcpu->esp);

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
  }
	
  //invoke EMHF runtime component main function for this CPU
  //TODO: don't reference rpb->isEarlyInit directly
  emhf_runtime_main(vcpu, rpb->isEarlyInit);	
}
