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

// runtime.c
// author: amit vasudevan (amitvasudevan@acm.org)

//---includes-------------------------------------------------------------------
#include <target.h>
#include <processor.h>
#include <globals.h>

//---runtime main---------------------------------------------------------------
void cstartup(void){
	u32 cpu_vendor;

	//initialize global runtime variables
	runtime_globals_init();

	//setup debugging	
#ifdef __DEBUG_SERIAL__	
	init_uart();
#endif
	printf("\nruntime initializing...");

	//check CPU type (Intel vs AMD)
  {
    u32 vendor_dword1, vendor_dword2, vendor_dword3;
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
			printf("\nRuntime: Fatal error, unrecognized CPU! 0x%08x:0x%08x:0x%08x",
				vendor_dword1, vendor_dword2, vendor_dword3);
			HALT();
		}   	 	
  }

  //debug, dump E820 and MP table
 	printf("\nNumber of E820 entries = %u", rpb->XtVmmE820NumEntries);
  {
    int i;
    for(i=0; i < (int)rpb->XtVmmE820NumEntries; i++){
      printf("\n0x%08x%08x, size=0x%08x%08x (%u)", 
          g_e820map[i].baseaddr_high, g_e820map[i].baseaddr_low,
          g_e820map[i].length_high, g_e820map[i].length_low,
          g_e820map[i].type);
    }
  
  }
  printf("\nNumber of MP entries = %u", rpb->XtVmmMPCpuinfoNumEntries);
  {
    int i;
    for(i=0; i < (int)rpb->XtVmmMPCpuinfoNumEntries; i++)
      printf("\nCPU #%u: bsp=%u, lapic_id=0x%02x", i, g_cpumap[i].isbsp, g_cpumap[i].lapic_id);
  }

  //setup Master-ID Table (MIDTABLE)
  {
    int i;
    for(i=0; i < (int)rpb->XtVmmMPCpuinfoNumEntries; i++){
       g_midtable[g_midtable_numentries].cpu_lapic_id = g_cpumap[i].lapic_id;
       g_midtable[g_midtable_numentries].vcpu_vaddr_ptr = 0;
       g_midtable_numentries++;
    }
  }

  //setup vcpus 
  setupvcpus(cpu_vendor, g_midtable, g_midtable_numentries);

  //wake up APS
  if(g_midtable_numentries > 1)
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


//---allcpus_common_start-------------------------------------------------------
void allcpus_common_start(VCPU *vcpu){
  //we start here with all CPUs executing common code, we 
  //will make BSP distinction based on isbsp macro which basically
  //reads the LAPIC MSR to see if it is the BSP. 
	
  //step:1 rally all APs up, make sure all of them started, this is
  //a task for the BSP
  if(isbsp()){
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
    spin_lock(&g_lock_cpus_active);
    g_cpus_active++;
    spin_unlock(&g_lock_cpus_active);

    while(!g_ap_go_signal); //Just wait for the BSP to tell us all is well.
 
    printf("\nAP(0x%02x): My ESP is 0x%08x, Waiting for SIPI...", vcpu->id, vcpu->esp);

    while(!vcpu->sipireceived);
    printf("\nAP(0x%02x): SIPI signal received, vector=0x%02x", vcpu->id, vcpu->sipivector);
  }
  
  
  //point to diffrentiate Intel vs AMD
  
	//outline of steps
	//1. initialize isolation layer (initSVM and initVMCB in case of AMD)
	//2. call app main (common to AMD and Intel)
	//3. wait for all cores to cycle through app main (common to AMD and Intel)
	//4. if BSP setup sipi (different for Intel and AMD)
	//5. if AP wait for sipi (different for Intel and AMD)
	//6. enter HVM (different for BSP and AP but common for Intel and AMD)
	
	if(vcpu->cpu_vendor == CPU_VENDOR_INTEL){
		printf("\nCPU(0x%02x): Intel integration still WiP, HALT!", vcpu->id);
		HALT();
	}
  
  //initialize SVM
  initSVM(vcpu);
 
  //initiaize VMCB
  initVMCB(vcpu); 

  //call app main
  if(emhf_app_main(vcpu)){
    printf("\nCPU(0x%02x): Application failed to initialize. HALT!", vcpu->id);
    HALT();
  }


#ifdef __NESTED_PAGING__
    //if we are the BSP setup SIPI intercept
    if(isbsp() && (g_midtable_numentries > 1) )
      apic_setup(vcpu);
 
#endif
    
  //start HVM
  {
    struct vmcb_struct *vmcb;
    void startHVM(VCPU *vcpu, u32 vmcb_phys_addr);
    printf("\nCPU(0x%02x): Starting HVM...", vcpu->id);
    vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;
    printf("\n  CS:EIP=0x%04x:0x%08x", (u16)vmcb->cs.sel, (u32)vmcb->rip);
    startHVM(vcpu, __hva2spa__(vcpu->vmcb_vaddr_ptr));
    printf("\nCPU(0x%02x): FATAL, should not be here. HALTING!", vcpu->id);
    HALT();
  }

}
