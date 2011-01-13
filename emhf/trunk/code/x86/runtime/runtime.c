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

	//initialize isolation layer and EMHF library interface abstraction
  if(cpu_vendor == CPU_VENDOR_INTEL){
  	g_isl = &g_isolation_layer_vmx;
		g_libemhf = &g_emhf_library_vmx;
	}else{
		g_isl = &g_isolation_layer_svm; 
		g_libemhf = &g_emhf_library_vmx;
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
  //svm_setupvcpus(cpu_vendor);
  g_isl->setupvcpus(cpu_vendor);

  //wake up APS
  if(g_midtable_numentries > 1)
    g_isl->wakeup_aps();

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

    if(vcpu->cpu_vendor == CPU_VENDOR_INTEL) {
        //set bit 5 (EM) of CR0 to be VMX compatible in case of Intel cores
		u32 bcr0;
		bcr0 = read_cr0();
		bcr0 |= 0x20;
		write_cr0(bcr0);

/*         if(txt_is_launched()) { // did we run SENTER? TODO: ASSERT(txt_is_launched()); */
/*             txt_validate_and_reload_mtrrs(); */
/*         } */
	}
    
  //step:1 rally all APs up, make sure all of them started, this is
  //a task for the BSP
  if(g_isl->isbsp()){
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
  
  //initialize isolation layer
	g_isl->initialize(vcpu);

  //initialize application parameter block and call app main
  {
  	APP_PARAM_BLOCK appParamBlock;
  	
		appParamBlock.bootsector_ptr = (u32)rpb->XtGuestOSBootModuleBase;
  	appParamBlock.bootsector_size = (u32)rpb->XtGuestOSBootModuleSize;
  	appParamBlock.optionalmodule_ptr = (u32)rpb->XtGuestOSBootModuleBaseSup1;
  	appParamBlock.optionalmodule_size = (u32)rpb->XtGuestOSBootModuleSizeSup1;
 		appParamBlock.runtimephysmembase = (u32)rpb->XtVmmRuntimePhysBase;  

  	//call app main
  	if(emhf_app_main(vcpu, &appParamBlock)){
    	printf("\nCPU(0x%02x): EMHF app. failed to initialize. HALT!", vcpu->id);
    	HALT();
  	}
	}   	

 	//increment app main success counter
	spin_lock(&g_lock_appmain_success_counter);
  g_appmain_success_counter++;
  spin_unlock(&g_lock_appmain_success_counter);
	
	//if BSP, wait for all cores to go through app main successfully
	if(vcpu->isbsp && (g_midtable_numentries > 1)){
		printf("\nCPU(0x%02x): Waiting for all cores to cycle through appmain...", vcpu->id);
		while(g_appmain_success_counter < g_midtable_numentries);	
		printf("\nCPU(0x%02x): All cores have successfully been through appmain.", vcpu->id);
	}


#if defined (__MP_VERSION__)  
	//if we are the BSP setup SIPI intercept
  if(vcpu->isbsp){
    g_isl->hvm_apic_setup(vcpu);
		printf("\nCPU(0x%02x): BSP, setup SIPI interception.", vcpu->id);
  }else{ //else, we are an AP and wait for SIPI signal
    printf("\nCPU(0x%02x): AP, waiting for SIPI signal...", vcpu->id);
    while(!vcpu->sipireceived);
    printf("\nCPU(0x%02x): SIPI signal received, vector=0x%02x", vcpu->id, vcpu->sipivector);

	
		g_isl->hvm_initialize_csrip(vcpu, ((vcpu->sipivector * PAGE_SIZE_4K) >> 4),
					 (vcpu->sipivector * PAGE_SIZE_4K), 0x0ULL);
	}
#endif


  //start HVM
  g_isl->hvm_start(vcpu);

  printf("\nCPU(0x%02x): FATAL, should not be here. HALTING!", vcpu->id);
  HALT();
}

//---runtime exception handler--------------------------------------------------
void runtime_exception_handler(u32 vector, struct regs *r){
	//we just let the isolation layer handle it
	//TODO: assert g_isl is valid
	g_isl->runtime_exception_handler(vector, r);
}

