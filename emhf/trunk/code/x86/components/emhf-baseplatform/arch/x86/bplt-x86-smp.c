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

/*
 * EMHF base platform component interface, x86 backend
 * implements SMP functionality
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <emhf.h>


//initialize SMP
void emhf_arch_baseplatform_smpinitialize(void){
  u32 cpu_vendor;
  ASSERT((u32)g_isl != 	0);
  
  //grab CPU vendor
  cpu_vendor = emhf_baseplatform_getcpuvendor();
  
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
  g_isl->setupvcpus(cpu_vendor);

  //wake up APS
  if(g_midtable_numentries > 1)
		g_isl->wakeup_aps();


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
void emhf_arch_x86_baseplatform_smpinitialize_commonstart(VCPU *vcpu){
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
	
   	
  //invoke EMHF runtime component main function for this CPU
  //TODO: don't reference rpb->isEarlyInit directly
  emhf_runtime_main(vcpu, rpb->isEarlyInit);	
}

