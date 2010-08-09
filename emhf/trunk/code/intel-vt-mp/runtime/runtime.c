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

//---globals and externs--------------------------------------------------------
extern u32 _xtlpb[];

u8 __midtable[SIZE_STRUCT_MIDTAB * MAX_MIDTAB_ENTRIES] __attribute__ (( section(".data") )) ;

//runtime stacks for individual CPUs
u8 __cpustacks[RUNTIME_STACK_SIZE * MAX_PCPU_ENTRIES] __attribute__ (( section(".stack") )) ;

u8 __vcpubuffers[SIZE_STRUCT_VCPU * MAX_VCPU_ENTRIES] __attribute__ (( section(".data") )) ;

u8 xtrac_3level_pdpt[PAGE_SIZE_4K] __attribute__ (( section(".vtdata") )) ;
u8 xtrac_3level_pdt[PAE_PTRS_PER_PDPT * PAGE_SIZE_4K] __attribute__ (( section(".vtdata") ));
u8 vt_vmxon_buffers[MAX_PCPU_ENTRIES * PAGE_SIZE_4K] __attribute__ (( section(".vtdata") )) ;
u8 vmx_vmcs_buffers[MAX_PCPU_ENTRIES * PAGE_SIZE_4K] __attribute__ (( section(".vtdata") )) ;



u8 __grube820buffer[SIZE_STRUCT_GRUBE820 * MAX_E820_ENTRIES] __attribute__ (( section(".data") )) ;
u8 __mp_cpuinfo[SIZE_STRUCT_PCPU * MAX_PCPU_ENTRIES]__attribute__ (( section(".data") )) ;	


PXTLPB	lpb=(PXTLPB)_xtlpb;
GRUBE820 *grube820list = (GRUBE820 *)__grube820buffer;
PCPU *pcpus= (PCPU *)__mp_cpuinfo;

MIDTAB *midtable = (MIDTAB *)__midtable;
u32 midtable_numentries=0;
	 

//---forward declarations-------------------------------------------------------
void cstartup(void);
u32 isbsp(void);


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
  printf("Done.");

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
        printf("Done.");
      }
  }    
    
  printf("\nAPs should be awake!");
}

/*#ifdef __NESTED_PAGING__
//---npt initialize-------------------------------------------------------------
void nptinitialize(u32 npt_pdpt_base, u32 npt_pdts_base, u32 npt_pts_base){
	pdpt_t pdpt;
	pdt_t pdts, pdt;
	pt_t pt;
	u32 paddr=0, i, j, k, y, z;
	u64 flags;
	
	printf("\n%s: pdpt=0x%08x, pdts=0x%08x, pts=0x%08x",
    __FUNCTION__, npt_pdpt_base, npt_pdts_base, npt_pts_base);
	
	pdpt=(pdpt_t)npt_pdpt_base;

  for(i = 0; i < PAE_PTRS_PER_PDPT; i++){
    y = (u32)__hva2spa__((u32)npt_pdts_base + (i << PAGE_SHIFT_4K));
    flags = (u64)(_PAGE_PRESENT);
		pdpt[i] = pae_make_pdpe((u64)y, flags);
    pdt=(pdt_t)((u32)npt_pdts_base + (i << PAGE_SHIFT_4K));
	       	
		for(j=0; j < PAE_PTRS_PER_PDT; j++){
			z=(u32)__hva2spa__((u32)npt_pts_base + ((i * PAE_PTRS_PER_PDT + j) << (PAGE_SHIFT_4K)));
		  flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER);
			pdt[j] = pae_make_pde((u64)z, flags);
			pt=(pt_t)((u32)npt_pts_base + ((i * PAE_PTRS_PER_PDT + j) << (PAGE_SHIFT_4K)));
			
			for(k=0; k < PAE_PTRS_PER_PT; k++){
        flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER);
        pt[k] = pae_make_pte((u64)paddr, flags);
				paddr+= PAGE_SIZE_4K;
			}
		}
  }
}
#endif
*/

//---setup vcpu structures for all the cores including BSP----------------------
void setupvcpus(MIDTAB *midtable, u32 midtable_numentries){
  u32 i;
  
  
//#ifdef __NESTED_PAGING__
//  u32 npt_current_asid=ASID_GUEST_KERNEL;
//#endif
  
  VCPU *vcpu;
  
  printf("\n%s: __cpustacks range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (u32)__cpustacks, (u32)__cpustacks + (RUNTIME_STACK_SIZE * MAX_VCPU_ENTRIES),
        RUNTIME_STACK_SIZE);
  printf("\n%s: __vcpubuffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (u32)__vcpubuffers, (u32)__vcpubuffers + (SIZE_STRUCT_VCPU * MAX_VCPU_ENTRIES),
        SIZE_STRUCT_VCPU);
  printf("\n%s: vt_vmxon_buffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (u32)vt_vmxon_buffers, (u32)vt_vmxon_buffers + (4096 * MAX_VCPU_ENTRIES),
        4096);
  printf("\n%s: vmx_vmcs_buffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (u32)vmx_vmcs_buffers, (u32)vmx_vmcs_buffers + (4096 * MAX_VCPU_ENTRIES),
        4096);

//#ifdef __NESTED_PAGING__
//    printf("\n%s: svm_npt_pdpt_buffers range 0x%08x-0x%08x in 0x%08x chunks",
//      __FUNCTION__, (u32)svm_npt_pdpt_buffers, (u32)svm_npt_pdpt_buffers + (4096 * MAX_VCPU_ENTRIES),
//          4096);
//    printf("\n%s: svm_npt_pdts_buffers range 0x%08x-0x%08x in 0x%08x chunks",
//      __FUNCTION__, (u32)svm_npt_pdts_buffers, (u32)svm_npt_pdts_buffers + (16384 * MAX_VCPU_ENTRIES),
//          16384);
//    printf("\n%s: svm_npt_pts_buffers range 0x%08x-0x%08x in 0x%08x chunks",
//      __FUNCTION__, (u32)svm_npt_pts_buffers, (u32)svm_npt_pts_buffers + ((2048*4096) * MAX_VCPU_ENTRIES),
//          (2048*4096));
//#endif
          
  for(i=0; i < midtable_numentries; i++){
    vcpu = (VCPU *)((u32)__vcpubuffers + (u32)(i * SIZE_STRUCT_VCPU));
    memset((void *)vcpu, 0, sizeof(VCPU));
    
    vcpu->esp = ((u32)__cpustacks + (i * RUNTIME_STACK_SIZE)) + RUNTIME_STACK_SIZE;    

    vcpu->vmxonregion_vaddr = ((u32)vt_vmxon_buffers + (i * 4096)) ;
    memset((void *)vcpu->vmxonregion_vaddr, 0, PAGE_SIZE_4K);
    vcpu->vmcs_vaddr = ((u32)vmx_vmcs_buffers + (i * 4096)) ;
    memset((void *)vcpu->vmcs_vaddr, 0, PAGE_SIZE_4K);



//#ifdef __NESTED_PAGING__
//    {
//      u32 npt_pdpt_base, npt_pdts_base, npt_pts_base;
//      npt_pdpt_base = ((u32)svm_npt_pdpt_buffers + (i * 4096)); 
//      npt_pdts_base = ((u32)svm_npt_pdts_buffers + (i * 16384));
//      npt_pts_base = ((u32)svm_npt_pts_buffers + (i * (2048*4096)));
//      nptinitialize(npt_pdpt_base, npt_pdts_base, npt_pts_base);
//      vcpu->npt_vaddr_ptr = npt_pdpt_base;
//      vcpu->npt_vaddr_pts = npt_pts_base;
//      vcpu->npt_asid = npt_current_asid;
//      npt_current_asid++;
//    }
//#endif
    
    vcpu->id = midtable[i].cpu_lapic_id;
    vcpu->sipivector = 0;
    vcpu->sipireceived = 0;

    midtable[i].vcpu_vaddr_ptr = (u32)vcpu;
    printf("\nCPU #%u: vcpu_vaddr_ptr=0x%08x, esp=0x%08x", i, midtable[i].vcpu_vaddr_ptr,
      vcpu->esp);
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
    for(i=0; i < (int)lpb->XtVmmMPCpuinfoNumEntries; i++){
       midtable[midtable_numentries].cpu_lapic_id = pcpus[i].lapic_id;
       midtable[midtable_numentries].vcpu_vaddr_ptr = 0;
       midtable_numentries++;
    }
  }

  //setup vcpus
  setupvcpus(midtable, midtable_numentries);

  printf("\nBSP: copying boot-module to BIOS default 0000:7C00");
	memcpy((void *)__GUESTOSBOOTMODULE_BASE, (void *)lpb->XtGuestOSBootModuleBase, lpb->XtGuestOSBootModuleSize);
  //{
  //  u8 *code = (u8 *)__GUESTOSBOOTMODULE_BASE;
  //  code[0]=0xEB; code[1]=0xFE;
  //
  //}

  //initialize v86 monitor
  v86monitor_initialize();

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

//---initVT: initializes CPU VT-------------------------------------------------
void initVT(VCPU *vcpu){
  //step-1: check if intel CPU
  {
    u8 cpu_oemid[12];
	  asm(	"xor	%%eax, %%eax \n"
				  "cpuid \n"		
				  "mov	%%ebx, %0 \n"
				  "mov	%%edx, %1 \n"
				  "mov	%%ecx, %2 \n"
			     :: "m"(cpu_oemid[0]), "m"(cpu_oemid[4]), "m"(cpu_oemid[8]): "eax", "ebx", "ecx", "edx" );

   	if ( strncmp( cpu_oemid, (u8 *)"GenuineIntel", 12 ) ){
   	  printf("\nCPU(0x%02x) is not an Intel CPU. Halting!", vcpu->id);
   	  HALT();
   	}
  }
  
  //step-2: check VT support
  {
  	u32	cpu_features;
    asm("mov	$1, %%eax \n"
				"cpuid \n"
				"mov	%%ecx, %0	\n"
				::"m"(cpu_features): "eax", "ebx", "ecx", "edx" );
		if ( ( cpu_features & (1<<5) ) == 0 ){
			printf("CPU(0x%02x) does not support VT. Halting!", vcpu->id);
      HALT();
		}
  }

  //step-3: save contents of VMX MSRs as well as MSR EFER and EFCR 
  //into vcpu
  {
    u32 i;
    u32 eax, edx;
    for(i=0; i < IA32_VMX_MSRCOUNT; i++){
        rdmsr( (IA32_VMX_BASIC_MSR + i), &eax, &edx);
        vcpu->vmx_msrs[i] = (u64)edx << 32 | (u64) eax;        
    }
  
    rdmsr(MSR_EFER, &eax, &edx);
    vcpu->msr_efer = (u64)edx << 32 | (u64) eax;
    rdmsr(MSR_EFCR, &eax, &edx);
    vcpu->msr_efcr = (u64)edx << 32 | (u64) eax;
  
    //[debug: dump contents of MSRs]
    for(i=0; i < IA32_VMX_MSRCOUNT; i++)
       printf("\nCPU(0x%02x): VMX MSR 0x%08x = 0x%08x%08x", vcpu->id, IA32_VMX_BASIC_MSR+i, 
          (u32)((u64)vcpu->vmx_msrs[i] >> 32), (u32)vcpu->vmx_msrs[i]);
    printf("\nCPU(0x%02x): MSR_EFER=0x%08x%08x", (u32)((u64)vcpu->msr_efer >> 32), 
          (u32)vcpu->msr_efer);
    printf("\nCPU(0x%02x): MSR_EFCR=0x%08x%08x", (u32)((u64)vcpu->msr_efcr >> 32), 
          (u32)vcpu->msr_efcr);
  
  }

  //step-4: enable VMX by setting CR4
	asm(	" mov  %%cr4, %%eax	\n"\
		" bts  $13, %%eax	\n"\
		" mov  %%eax, %%cr4	" ::: "eax" );
  printf("\nCPU(0x%02x): enabled VMX", vcpu->id);

  //step-5:enter VMX root operation using VMXON
  {
  	u32 retval=0;
  	u64 vmxonregion_paddr = __hva2spa__(vcpu->vmxonregion_vaddr);
    //set VMCS rev id
  	*((u32 *)vcpu->vmxonregion_vaddr) = (u32)vcpu->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];
    
   	asm( "vmxon %1 \n"
			 "jbe vmfail \n"
			 "movl $0x1, %%eax \n" 
			 "movl %%eax, %0 \n"
			 "jmp vmsuccess \n"
			 "vmfail: \n"
			 "movl $0x0, %%eax \n"
			 "movl %%eax, %0 \n"
			 "vmsuccess: \n" 
       : "=m" (retval)
       : "m"(vmxonregion_paddr) 
       : "eax");
	
    if(!retval){
      printf("\nCPU(0x%02x): Fatal, unable to enter VMX root operation", vcpu->id);
      HALT();
    }  
  
    printf("\nCPU(0x%02x): Entered VMX root operation", vcpu->id);
  }
}


//---allcpus_common_start-------------------------------------------------------
void allcpus_common_start(VCPU *vcpu){
  //we start here with all CPUs executing common code, we 
  //will make BSP distinction based on isbsp macro which basically
  //reads the LAPIC MSR to see if it is the BSP
 
  
  //step:1 rally all APs up, make sure all of them started, this is
  //a task for the BSP
  if(isbsp()){
    printf("\nBSP rallying APs...");
    printf("\nBSP(0x%02x): My ESP is 0x%08x", vcpu->id, vcpu->esp);

    //increment a CPU to account for the BSP
    spin_lock(&lock_cpus_active);
    cpus_active++;
    spin_unlock(&lock_cpus_active);

    //wait for cpus_active to become midtable_numentries -1 to indicate
    //that all APs have been successfully started
    while(cpus_active < midtable_numentries);
    
    printf("\nAPs all awake...Setting them free...");
    spin_lock(&lock_ap_go_signal);
    ap_go_signal=1;
    spin_unlock(&lock_ap_go_signal);

  
  }else{
    //we are an AP, so we need to simply update the AP startup counter
    //and wait until we are told to proceed
    //increment active CPUs
    spin_lock(&lock_cpus_active);
    cpus_active++;
    spin_unlock(&lock_cpus_active);

    while(!ap_go_signal);
 
    printf("\nAP(0x%02x): My ESP is 0x%08x, Waiting for SIPI...", vcpu->id, vcpu->esp);

    while(!vcpu->sipireceived);
    printf("\nAP(0x%02x): SIPI signal received, vector=0x%02x", vcpu->id, vcpu->sipivector);
  }

  
  //initialize VT
  initVT(vcpu);

  //initiaize VMCS
  initVMCS(vcpu); 

  //call app main
  if(sechyp_app_main(vcpu)){
    printf("\nCPU(0x%02x): Application failed to initialize. HALT!", vcpu->id);
    HALT();
  }
  
/*
#ifdef __NESTED_PAGING__
  //if we are the BSP setup SIPI intercept
  //if(isbsp())
  //  apic_setup(vcpu);
#endif
*/    
  //start HVM
  {
    void startHVM(VCPU *vcpu, u32 vmcs_phys_addr);
    printf("\nCPU(0x%02x): Starting HVM...", vcpu->id);
    startHVM(vcpu, __hva2spa__(vcpu->vmcs_vaddr));
    printf("\nCPU(0x%02x): FATAL, should not be here. HALTING!", vcpu->id);
    HALT();
  }

}