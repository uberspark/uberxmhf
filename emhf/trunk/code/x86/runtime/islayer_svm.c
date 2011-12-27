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

// islayer_svm.c - SVM isolation layer implementation
// author: amit vasudevan (amitvasudevan@acm.org) and ning qu (qning@cmu.edu)
// modified extensively for EMHF by amit vasudevan
#include <emhf.h> 

//---notes
// CLGI/STGI
// GIF is set to 1 always when reset and SVM first enabled
// if you send an NMI when GIF=0, it is held pending until GIF=1 again

// so we set GIF=1 on all cores and NMI intercept as well
// when we get the VMEXIT_NMI, we do a simple trick
// CLGI followed by STGI this will make GIF=0 and then GIF=1 which will
// deliver the pending NMI to the current IDT whichi will xfer control
// to the exception handler within the hypervisor where we quiesce.
// upon resuming the hypervisor or guest resumes normally!


//generic globals used by the svm islayer
//g_midtable
//g_midtable_numentries
//_ap_bootstrap_start
//_ap_bootstrap_end
//_ap_cr3_value;
//_ap_cr4_value;


//static (local) function list
/*static u8 _svm_guest_readcode_byte(struct vmcb_struct *vmcb, u32 addr);
static VCPU *_svm_getvcpu(void);
static void _svm_processNMI(VCPU *vcpu, struct vmcb_struct *vmcb, struct regs *r);
static void _svm_send_quiesce_signal(VCPU *vcpu, struct vmcb_struct *vmcb)
static void _svm_nptinitialize(u32 npt_pdpt_base, u32 npt_pdts_base, u32 npt_pts_base);

static void _svm_handle_swint(struct vmcb_struct *vmcb, struct regs *r);
static void _svm_handle_npf(VCPU *vcpu, struct regs *r);
static void _svm_handle_nmi(VCPU *vcpu, struct vmcb_struct *vmcb, struct regs *r);
static void _svm_handle_ioio(VCPU *vcpu, struct vmcb_struct *vmcb, struct regs *r);
static void _svm_handle_msr(VCPU *vcpu, struct vmcb_struct *vmcb, struct regs *r);

static void _svm_initSVM(VCPU *vcpu);
static void _svm_initVMCB(VCPU *vcpu);*/
u8 * _svm_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr);

//==============================================================================
//static (local) function definitions
//==============================================================================

//------------------------------------------------------------------------------
static u8 __attribute__((unused)) _svm_guest_readcode_byte(struct vmcb_struct *vmcb, u32 addr) {
	u32 paddr;
	
	if((u32)vmcb->cr0 & CR0_PG)
		paddr=svm_kernel_pt_walker(vmcb, addr); //paging enabled in guest, so addr is virtual
	else
		paddr=vmcb->cs.base + addr; //paging is not enabled, we use CS base and offset of addr	

	return ( *(u8 *)paddr );
}


//---function to obtain the vcpu of the currently executing core----------------
//note: this always returns a valid VCPU pointer
VCPU *_svm_getvcpu(void){
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
  
  for(i=0; i < (int)g_midtable_numentries; i++){
    if(g_midtable[i].cpu_lapic_id == lapic_id)
        return( (VCPU *)g_midtable[i].vcpu_vaddr_ptr );
  }

  printf("\n%s: fatal, unable to retrieve vcpu for id=0x%02x", __FUNCTION__, lapic_id);
  HALT(); return NULL; /* will never return presently */
}

/*
//---NMI processing routine-----------------------------------------------------
static void _svm_processNMI(VCPU *vcpu, struct vmcb_struct *vmcb, struct regs __attribute__((unused)) *r){
  if( (!vcpu->nmiinhvm) && (!g_svm_quiesce) ){
    printf("\nCPU(0x%02x): warning, ignoring spurious NMI within hypervisor!", vcpu->id);
    return;
  }

  if(g_svm_quiesce){
    //ok this NMI is because of g_svm_quiesce. note: g_svm_quiesce can be 1 and
    //this could be a NMI for the guest. we have no way of distinguising
    //this. however, since g_svm_quiesce=1, we can handle this NMI as a g_svm_quiesce NMI
    //and rely on the platform h/w to reissue the NMI later
    printf("\nCPU(0x%02x): NMI for core g_svm_quiesce", vcpu->id);
    printf("\nCPU(0x%02x): CS:EIP=0x%04x:0x%08x", vcpu->id, (u16)vmcb->cs.sel, (u32)vmcb->rip);
  
    printf("\nCPU(0x%02x): quiesced, updating counter. awaiting EOQ...", vcpu->id);
    spin_lock(&g_svm_lock_quiesce_counter);
    g_svm_quiesce_counter++;
    spin_unlock(&g_svm_lock_quiesce_counter);
    
    while(!g_svm_quiesce_resume_signal);
    printf("\nCPU(0x%02x): EOQ received, resuming...", vcpu->id);
    
    spin_lock(&g_svm_lock_quiesce_resume_counter);
    g_svm_quiesce_resume_counter++;
    spin_unlock(&g_svm_lock_quiesce_resume_counter);
    
    //printf("\nCPU(0x%08x): Halting!", vcpu->id);
    //HALT();
    
  }else{
    //we are not in quiesce, so simply inject this NMI back to guest
    ASSERT( vcpu->nmiinhvm == 1 );
    printf("\nCPU(0x%02x): Regular NMI, injecting back to guest...", vcpu->id);
    vmcb->eventinj.fields.vector=0;
    vmcb->eventinj.fields.type = EVENTTYPE_NMI;
    vmcb->eventinj.fields.ev=0;
    vmcb->eventinj.fields.v=1;
    vmcb->eventinj.fields.errorcode=0;
  }
  
  vcpu->nmiinhvm=0;
}*/

//---quiescing implementation---------------------------------------------------
/*static void _svm_send_quiesce_signal(VCPU *vcpu, struct vmcb_struct __attribute__((unused)) *vmcb){
  volatile u32 *icr_low = (u32 *)(0xFEE00000 + 0x300);
  volatile u32 *icr_high = (u32 *)(0xFEE00000 + 0x310);
  u32 icr_high_value= 0xFFUL << 24;
  u32 prev_icr_high_value;

	//printf("\n%s: starting...", __FUNCTION__);    
  prev_icr_high_value = *icr_high;
  //printf("\n%s: prev_icr_high_value=%08x", __FUNCTION__, prev_icr_high_value);
  
  //printf("\n%s: sending ICR high...", __FUNCTION__);
  *icr_high = icr_high_value;    //send to all but self
  //printf("\ndone.");

  //printf("\n%s: sending ICR low...", __FUNCTION__);
  *icr_low = 0x000C0400UL;      //send NMI        
  
  //restore icr high
  *icr_high = prev_icr_high_value;
    
  printf("\nCPU(0x%02x): NMIs fired!", vcpu->id);
}*/

/*

//---npt initialize-------------------------------------------------------------
void _svm_nptinitialize(u32 npt_pdpt_base, u32 npt_pdts_base, u32 npt_pts_base){
	pdpt_t pdpt;
	pdt_t pdt;
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
				//the EMHF memory region includes the secure loader +
				//the runtime (core + app). this runs from 
				//(rpb->XtVmmRuntimePhysBase - PAGE_SIZE_2M) with a size
				//of (rpb->XtVmmRuntimeSize+PAGE_SIZE_2M)
				//make EMHF physical pages inaccessible
				if( (paddr >= (rpb->XtVmmRuntimePhysBase - PAGE_SIZE_2M)) &&
					(paddr < (rpb->XtVmmRuntimePhysBase + rpb->XtVmmRuntimeSize)) )
					flags = 0;	//not-present
				else
					flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER);	//present
				pt[k] = pae_make_pte((u64)paddr, flags);
				paddr+= PAGE_SIZE_4K;
			}
		}
	}
	
} */


//---svm int 15 hook enabling function------------------------------------------
static void	_svm_int15_initializehook(VCPU *vcpu){
	//we should only be called from the BSP
	ASSERT(vcpu->isbsp);
	
	{
		u8 *bdamemory = (u8 *)0x4AC;				//use BDA reserved memory at 0040:00AC
		
		u16 *ivt_int15 = (u16 *)(0x54);			//32-bit CS:IP for IVT INT 15 handler
		
		//printf("\nCPU(0x%02x): original BDA dump: %02x %02x %02x %02x %02x %02x %02x %02x", vcpu->id,
		//	bdamemory[0], bdamemory[1], bdamemory[2], bdamemory[3], bdamemory[4],
		//		bdamemory[5], bdamemory[6], bdamemory[7]);
		
		printf("\nCPU(0x%02x): original INT 15h handler at 0x%04x:0x%04x", vcpu->id,
			ivt_int15[1], ivt_int15[0]);

		//we need 8 bytes (4 for the VMCALL followed by IRET and 4 for he original 
		//IVT INT 15h handler address, zero them to start off
		memset(bdamemory, 0x0, 8);		

		//printf("\nCPU(0x%02x): BDA dump after clear: %02x %02x %02x %02x %02x %02x %02x %02x", vcpu->id,
		//	bdamemory[0], bdamemory[1], bdamemory[2], bdamemory[3], bdamemory[4],
		//		bdamemory[5], bdamemory[6], bdamemory[7]);

		//implant VMMCALL followed by IRET at 0040:04AC
		bdamemory[0]= 0x0f;	//VMMCALL						
		bdamemory[1]= 0x01;
		bdamemory[2]= 0xd9;																	
		bdamemory[3]= 0xcf;	//IRET
		
		//store original INT 15h handler CS:IP following VMCALL and IRET
		*((u16 *)(&bdamemory[4])) = ivt_int15[0];	//original INT 15h IP
		*((u16 *)(&bdamemory[6])) = ivt_int15[1];	//original INT 15h CS

		//printf("\nCPU(0x%02x): BDA dump after hook implant: %02x %02x %02x %02x %02x %02x %02x %02x", vcpu->id,
		//	bdamemory[0], bdamemory[1], bdamemory[2], bdamemory[3], bdamemory[4],
		//		bdamemory[5], bdamemory[6], bdamemory[7]);

		//point IVT INT15 handler to the VMCALL instruction
		ivt_int15[0]=0x00AC;
		ivt_int15[1]=0x0040;					
	}
}


/*
//------------------------------------------------------------------------------
//handle_swint - software INTn intercept handling
static void _svm_handle_swint(VCPU *vcpu, struct vmcb_struct *vmcb, struct regs *r){
	u8 op1, op2;

	//the way to get the vector is to look into the guest code
	//vmcb->rip points to the SWINT instruction
	op1=_svm_guest_readcode_byte(vmcb, vmcb->rip);
	op2=_svm_guest_readcode_byte(vmcb, vmcb->rip+1);


	//we only handle SWINT 15h, E820 requests 
	if(op1 == 0xCD && op2 == 0x15 && ((u16)vmcb->rax == 0xE820) ){
		
		//only handle INT 15 h if either in real-mode or in protected
		//mode with paging and EFLAGS.VM bit set (virtual-8086 mode)
		if( !(vmcb->cr0 & CR0_PE)  ||
					( (vmcb->cr0 & CR0_PE) && (vmcb->cr0 & CR0_PG) &&
						(vmcb->rflags & EFLAGS_VM)  ) ){

			printf("\nCPU(0x%02x): INT 15(e820): AX=0x%04x, EDX=0x%08x, EBX=0x%08x, ECX=0x%08x, ES=0x%04x, DI=0x%04x", vcpu->id, 
			(u16)vmcb->rax, r->edx, r->ebx, r->ecx, (u16)vmcb->es.sel, (u16)r->edi);
			
			ASSERT(r->edx == 0x534D4150UL);  //'SMAP' should be specified by guest
			ASSERT(r->ebx < rpb->XtVmmE820NumEntries); //invalid continuation value specified by guest!
				
			//copy the e820 descriptor and return its size in ECX
			memcpy((void *)((u32)((vmcb->es.base)+(u16)r->edi)), (void *)&g_e820map[r->ebx],
						sizeof(GRUBE820));
			r->ecx=20;
	
			//set EAX to 'SMAP' as required by the service call				
			vmcb->rax=r->edx;

 			//increment e820 descriptor continuation value
			r->ebx=r->ebx+1;

 			if(r->ebx > (rpb->XtVmmE820NumEntries-1) ){
				//we have reached the last record, so set CF and make EBX=0
				r->ebx=0;
				vmcb->rflags |= ((u64)0x1);
			}else{
				//we still have more records, so clear CF
				vmcb->rflags &= ~((u64)0x1);
			}

      //swallow this interrupt as we have handled it
			vmcb->eventinj.bytes=0;
			vmcb->rip+=2;
		
			return;	//end of INT 15h handling
		}

	}


	//ok, either this is not a INT 15 or a INT 15 in protected mode
	//so simply chain by injecting it back into the guest
	vmcb->eventinj.fields.vector= op2;
	vmcb->eventinj.fields.type=0x4;
	vmcb->eventinj.fields.ev=0;
	vmcb->eventinj.fields.v=1;
	vmcb->rip+=2;
	
	return;
}*/	




  

//---init SVM-------------------------------------------------------------------
static void _svm_initSVM(VCPU *vcpu){
  u32 eax, edx, ecx, ebx;
  u64 hsave_pa;

  //check if CPU supports SVM extensions 
  cpuid(0x80000001, &eax, &ebx, &ecx, &edx);
  if( !(ecx & (1<<ECX_SVM)) ){
   printf("\nCPU(0x%02x): no SVM extensions. HALT!", vcpu->id);
   HALT();
  }
  
  //check if SVM extensions are disabled by the BIOS 
  rdmsr(VM_CR_MSR, &eax, &edx);
  if( eax & (1<<VM_CR_SVME_DISABLE) ){
    printf("\nCPU(0x%02x): SVM extensions disabled in the BIOS. HALT!", vcpu->id);
    HALT();
  }

  // check for nested paging support and number of ASIDs 
	cpuid(0x8000000A, &eax, &ebx, &ecx, &edx);
  if(!(edx & 0x1)){
      printf("\nCPU(0x%02x): No support for Nested Paging, HALTING!", vcpu->id);
		HALT();
	}
	
  printf("\nCPU(0x%02x): Nested paging support present", vcpu->id);
	if( (ebx-1) < 2 ){
		printf("\nCPU(0x%02x): Total number of ASID is too low, HALTING!", vcpu->id);
		HALT();
	}
	
	printf("\nCPU(0x%02x): Total ASID is valid", vcpu->id);

  // enable SVM and debugging support (if required)   
  rdmsr((u32)VM_CR_MSR, &eax, &edx);
  eax &= (~(1<<VM_CR_DPD));
  wrmsr((u32)VM_CR_MSR, eax, edx);
  printf("\nCPU(0x%02x): HDT debugging enabled", vcpu->id);

  rdmsr((u32)MSR_EFER, &eax, &edx);
  eax |= (1<<EFER_SVME);
  wrmsr((u32)MSR_EFER, eax, edx);
  printf("\nCPU(0x%02x): SVM extensions enabled", vcpu->id);

  // Initialize the HSA 
  //printf("\nHSAVE area=0x%08X", vcpu->hsave_vaddr_ptr);
  hsave_pa = __hva2spa__((void*)vcpu->hsave_vaddr_ptr);
  //printf("\nHSAVE physaddr=0x%08x", hsave_pa);
  eax = (u32)hsave_pa;
  edx = (u32)(hsave_pa >> 32);
  wrmsr((u32)VM_HSAVE_PA, eax, edx);
  printf("\nCPU(0x%02x): SVM HSAVE initialized", vcpu->id);

  // enable NX protections 
  rdmsr(MSR_EFER, &eax, &edx);
  eax |= (1 << EFER_NXE);
  wrmsr(MSR_EFER, eax, edx);
  printf("\nCPU(0x%02x): NX protection enabled", vcpu->id);

  return;
}


//---setup VMCB-----------------------------------------------------------------
static void _svm_initVMCB(VCPU *vcpu){
  
  struct vmcb_struct *vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;
  
  printf("\nCPU(0x%02x): VMCB at 0x%08x", vcpu->id, (u32)vmcb);
  memset(vmcb, 0, sizeof(struct vmcb_struct));
  
  // set up CS descr 
  vmcb->cs.sel = 0x0;
  vmcb->cs.base = 0x0;
  vmcb->cs.limit = 0x0ffff; // 64K limit since g=0 
  vmcb->cs.attr.bytes = 0x009b;
  
  // set up DS descr 
  vmcb->ds.sel = 0x0;
  vmcb->ds.base = 0x0;
  vmcb->ds.limit = 0x0ffff; // 64K limit since g=0 
  vmcb->ds.attr.bytes = 0x0093; // read/write 
  
  // set up ES descr 
  vmcb->es.sel = 0x0;
  vmcb->es.base = 0x0;
  vmcb->es.limit = 0x0ffff; // 64K limit since g=0 
  vmcb->es.attr.bytes = 0x0093; // read/write 

  // set up FS descr 
  vmcb->fs.sel = 0x0;
  vmcb->fs.base = 0x0;
  vmcb->fs.limit = 0x0ffff; // 64K limit since g=0 
  vmcb->fs.attr.bytes = 0x0093; // read/write 

  // set up GS descr 
  vmcb->gs.sel = 0x0;
  vmcb->gs.base = 0x0;
  vmcb->gs.limit = 0x0ffff; // 64K limit since g=0 
  vmcb->gs.attr.bytes = 0x0093; // read/write 

  // set up SS descr 
  vmcb->ss.sel = 0x0;
  vmcb->ss.base = 0x0;
  vmcb->ss.limit = 0x0ffff; // 64K limit since g=0 
  vmcb->ss.attr.bytes = 0x0093; // read/write 

  vmcb->idtr.limit = 0x03ff;

  // SVME needs to be set in EFER for vmrun to execute 
  vmcb->efer |= (1 << EFER_SVME);
   
  // set guest PAT to state at reset. 
  vmcb->g_pat = 0x0007040600070406ULL;

  // other-non general purpose registers/state 
  vmcb->guest_asid = 1; // ASID 0 reserved for host 
  vmcb->cpl = 0; // set cpl to 0 for real mode 

  // general purpose registers 
  vmcb->rax= 0x0ULL;
  vmcb->rsp= 0x0ULL;

  if(svm_isbsp()){
    printf("\nBSP(0x%02x): copying boot-module to boot guest", vcpu->id);
  	memcpy((void *)__GUESTOSBOOTMODULE_BASE, (void *)rpb->XtGuestOSBootModuleBase, rpb->XtGuestOSBootModuleSize);
    vmcb->rip = 0x7c00ULL;
  }else{

#ifdef __NESTED_PAGING__
      vmcb->cs.sel = (vcpu->sipivector * PAGE_SIZE_4K) >> 4;
      vmcb->cs.base = (vcpu->sipivector * PAGE_SIZE_4K);
      vmcb->rip = 0x0ULL;
#else
      //poke a spin loop at 0040:00AC BDA-reserved loc
      u8 *code = (u8 *)0x4AC;
      printf("\nCPU(0x%02x): poking spin loop to start guest", vcpu->id);
      code[0]=0xEB; code[1]=0xFE;
      vmcb->rip = 0xACULL;
      vmcb->cs.sel = 0x0040;
      vmcb->cs.base = 0x400;
#endif

  }
  vmcb->rflags = 0x0ULL;
  
  vmcb->cr0 = 0x00000010ULL;
  vmcb->cr2 = 0ULL;
  vmcb->cr3 = 0x0ULL;
  vmcb->cr4 = 0ULL;
  
  vmcb->dr6 = 0xffff0ff0ULL;
  vmcb->dr7 = 0x00000400ULL;
 
  vmcb->cr_intercepts = 0;
  vmcb->dr_intercepts = 0;
  
  // intercept all SVM instructions 
  vmcb->general2_intercepts |= (u32)(GENERAL2_INTERCEPT_VMRUN |
					  GENERAL2_INTERCEPT_VMMCALL |
					  GENERAL2_INTERCEPT_VMLOAD |
					  GENERAL2_INTERCEPT_VMSAVE |
					  GENERAL2_INTERCEPT_STGI |
					  GENERAL2_INTERCEPT_CLGI |
					  GENERAL2_INTERCEPT_SKINIT |
					  GENERAL2_INTERCEPT_ICEBP);

/*
	//extracted --> memory protection component
	vmcb->h_cr3 = __hva2spa__(vcpu->npt_vaddr_ptr);
  vmcb->np_enable |= (1ULL << NP_ENABLE);
	vmcb->guest_asid = vcpu->npt_asid;
	printf("\nCPU(0x%02x): Activated NPTs.", vcpu->id);
*/

	//INT 15h E820 hook enablement for VMX unrestricted guest mode
	//note: this only happens for the BSP
	if(vcpu->isbsp){
		printf("\nCPU(0x%02x, BSP): initializing INT 15 hook...", vcpu->id);
		_svm_int15_initializehook(vcpu);
	}


  //intercept NMIs, required for core quiescing support
  vmcb->general1_intercepts |= (u32) GENERAL1_INTERCEPT_NMI;

  //setup IO interception
  memset((void *)g_svm_iopm, 0, SIZEOF_IOPM_BITMAP);   //clear bitmap buffer
  vmcb->iopm_base_pa = __hva2spa__(g_svm_iopm);   //setup vmcb iopm
  vmcb->general1_intercepts |= (u32) GENERAL1_INTERCEPT_IOIO_PROT;

  //setup MSR interception
  memset((void *)g_svm_msrpm, 0, SIZEOF_MSRPM_BITMAP);   //clear bitmap buffer
  vmcb->msrpm_base_pa = __hva2spa__(g_svm_msrpm);   //setup vmcb msrpm
  vmcb->general1_intercepts |= (u32) GENERAL1_INTERCEPT_MSR_PROT;


  return;
}




//==============================================================================
//global function definitions
//==============================================================================

//---svm_isbsp----------------------------------------------------------------------
//returns 1 if the calling CPU is the BSP, else 0
u32 svm_isbsp(void){
  u32 eax, edx;
  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  ASSERT( edx == 0 ); //APIC is below 4G
  
  if(eax & 0x100)
    return 1;
  else
    return 0;
}


/*//---generic exception handler--------------------------------------------------
void svm_runtime_exception_handler(u32 vector, struct regs *r){
	VCPU *vcpu = _svm_getvcpu();
  // INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE *noecode_sf= (INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE *)((u32)r->esp + (u32)0x0C); 
  // INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE *ecode_sf= (INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE *)((u32)r->esp + (u32)0x0C); 

  printf("\nCPU(0x%02x): XtRtmExceptionHandler: Exception=0x%08X", vcpu->id, vector);
  printf("\nCPU(0x%02x): ESP=0x%08x", vcpu->id, r->esp);
  if(vector == 0x2){
    //_svm_processNMI(vcpu, (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr, r);
    emhf_smpguest_eventhandler_nmiexception(vcpu, r);
    return;
  }	
}*/

/*//---quiesce interface to halt all cores----------------------------------------
void svm_do_quiesce(VCPU *vcpu){
        struct vmcb_struct *vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;
        
				printf("\nCPU(0x%02x): got quiesce signal...", vcpu->id);
        //grab hold of quiesce lock
        spin_lock(&g_svm_lock_quiesce);
        printf("\nCPU(0x%02x): grabbed quiesce lock.", vcpu->id);

        spin_lock(&g_svm_lock_quiesce_counter);
        g_svm_quiesce_counter=0;
        spin_unlock(&g_svm_lock_quiesce_counter);
        
        //send all the other CPUs the quiesce signal
        g_svm_quiesce=1;  //we are now processing quiesce
        _svm_send_quiesce_signal(vcpu, vmcb);
        
        //wait for all the remaining CPUs to quiesce
        printf("\nCPU(0x%02x): waiting for other CPUs to respond...", vcpu->id);
        while(g_svm_quiesce_counter < (g_midtable_numentries-1) );
        printf("\nCPU(0x%02x): all CPUs quiesced successfully.", vcpu->id);
}*/

static void svm_do_quiesce(VCPU *vcpu){
		printf("\n%s: REFACTORED, WE SHOULD NEVER BE HERE", __FUNCTION__);
		HALT();
}

static void svm_do_wakeup(VCPU *vcpu){
		printf("\n%s: REFACTORED, WE SHOULD NEVER BE HERE", __FUNCTION__);
		HALT();
}

/* do_quiesce and do_wakeup should be called in pairs
 * the operations between do_quiesce and do_wakeup won't be influenced by other CPUs */
/*void svm_do_wakeup(VCPU *vcpu){
        //set resume signal to resume the cores that are quiesced
        //Note: we do not need a spinlock for this since we are in any
        //case the only core active until this point
        g_svm_quiesce_resume_counter=0;
        printf("\nCPU(0x%02x): waiting for other CPUs to resume...", vcpu->id);
        g_svm_quiesce_resume_signal=1;
        
        while(g_svm_quiesce_resume_counter < (g_midtable_numentries-1) );

        g_svm_quiesce=0;  // we are out of quiesce at this point

        printf("\nCPU(0x%02x): all CPUs resumed successfully.", vcpu->id);
        
        //reset resume signal
        spin_lock(&g_svm_lock_quiesce_resume_signal);
        g_svm_quiesce_resume_signal=0;
        spin_unlock(&g_svm_lock_quiesce_resume_signal);
                
        //release quiesce lock
        printf("\nCPU(0x%02x): releasing quiesce lock.", vcpu->id);
        spin_unlock(&g_svm_lock_quiesce);
        
        //printf("\nCPU(0x%02x): Halting!", vcpu->id);
        //HALT();
}*/

//---guest kernel page-table walker---------------------------------------------
u32 svm_kernel_pt_walker(struct vmcb_struct *vmcb, u32 vaddr){
  if((u32)vmcb->cr4 & CR4_PAE ){
    //PAE paging used by guest
    u32 kcr3 = (u32)vmcb->cr3;
    u32 pdpt_index, pd_index, pt_index, offset;
    u64 paddr;
    pdpt_t kpdpt;
    pdt_t kpd; 
    pt_t kpt; 
    u32 pdpt_entry, pd_entry, pt_entry;
    u32 tmp;

    // get fields from virtual addr 
    pdpt_index = pae_get_pdpt_index(vaddr);
    pd_index = pae_get_pdt_index(vaddr);
    pt_index = pae_get_pt_index(vaddr);
    offset = pae_get_offset_4K_page(vaddr);  

    //grab pdpt entry
    tmp = pae_get_addr_from_32bit_cr3(kcr3);
    kpdpt = (pdpt_t)((u32)tmp); 
    pdpt_entry = kpdpt[pdpt_index];
  
    //grab pd entry
    tmp = pae_get_addr_from_pdpe(pdpt_entry);
    kpd = (pdt_t)((u32)tmp); 
    pd_entry = kpd[pd_index];

    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (u32)pae_get_addr_from_pde(pd_entry);
      kpt = (pt_t)((u32)tmp);  
      pt_entry  = kpt[pt_index];
      
      // find physical page base addr from page table entry 
      paddr = (u64)pae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 2MB page 
      offset = pae_get_offset_big(vaddr);
      paddr = (u64)pae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }
  
    return paddr;
    
  }else{
    //non-PAE 2 level paging used by guest
    u32 kcr3 = (u32)vmcb->cr3;
    u32 pd_index, pt_index, offset;
    u64 paddr;
    npdt_t kpd; 
    npt_t kpt; 
    u32 pd_entry, pt_entry;
    u32 tmp;

    // get fields from virtual addr 
    pd_index = npae_get_pdt_index(vaddr);
    pt_index = npae_get_pt_index(vaddr);
    offset = npae_get_offset_4K_page(vaddr);  
  
    // grab pd entry
    tmp = npae_get_addr_from_32bit_cr3(kcr3);
    kpd = (npdt_t)((u32)tmp); 
    pd_entry = kpd[pd_index];
  
    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (u32)npae_get_addr_from_pde(pd_entry);
      kpt = (npt_t)((u32)tmp);  
      pt_entry  = kpt[pt_index];
      
      // find physical page base addr from page table entry 
      paddr = (u64)npae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 4MB page 
      offset = npae_get_offset_big(vaddr);
      paddr = (u64)npae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }
  
    return (u32)paddr;
  }
}




/*
//---setup vcpu structures for all the cores including BSP----------------------
void svm_setupvcpus(u32 cpu_vendor){
  u32 i;
  u32 npt_current_asid=ASID_GUEST_KERNEL;
  VCPU *vcpu;
  
  printf("\n%s: g_cpustacks range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (u32)g_cpustacks, (u32)g_cpustacks + (RUNTIME_STACK_SIZE * MAX_VCPU_ENTRIES),
        RUNTIME_STACK_SIZE);
  printf("\n%s: g_vcpubuffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (u32)g_vcpubuffers, (u32)g_vcpubuffers + (SIZE_STRUCT_VCPU * MAX_VCPU_ENTRIES),
        SIZE_STRUCT_VCPU);
  printf("\n%s: g_svm_hsave_buffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (u32)g_svm_hsave_buffers, (u32)g_svm_hsave_buffers + (8192 * MAX_VCPU_ENTRIES),
        8192);
  printf("\n%s: g_svm_vmcb_buffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (u32)g_svm_vmcb_buffers, (u32)g_svm_vmcb_buffers + (8192 * MAX_VCPU_ENTRIES),
        8192);
  printf("\n%s: g_svm_npt_pdpt_buffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (u32)g_svm_npt_pdpt_buffers, (u32)g_svm_npt_pdpt_buffers + (4096 * MAX_VCPU_ENTRIES),
        4096);
  printf("\n%s: g_svm_npt_pdts_buffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (u32)g_svm_npt_pdts_buffers, (u32)g_svm_npt_pdts_buffers + (16384 * MAX_VCPU_ENTRIES),
        16384);
  printf("\n%s: g_svm_npt_pts_buffers range 0x%08x-0x%08x in 0x%08x chunks",
    __FUNCTION__, (u32)g_svm_npt_pts_buffers, (u32)g_svm_npt_pts_buffers + ((2048*4096) * MAX_VCPU_ENTRIES),
        (2048*4096));
          
  for(i=0; i < g_midtable_numentries; i++){
    vcpu = (VCPU *)((u32)g_vcpubuffers + (u32)(i * SIZE_STRUCT_VCPU));
    memset((void *)vcpu, 0, sizeof(VCPU));
    
    vcpu->cpu_vendor = cpu_vendor;
    
    vcpu->esp = ((u32)g_cpustacks + (i * RUNTIME_STACK_SIZE)) + RUNTIME_STACK_SIZE;    
    vcpu->hsave_vaddr_ptr = ((u32)g_svm_hsave_buffers + (i * 8192));
    vcpu->vmcb_vaddr_ptr = ((u32)g_svm_vmcb_buffers + (i * 8192));

    {
      u32 npt_pdpt_base, npt_pdts_base, npt_pts_base;
      npt_pdpt_base = ((u32)g_svm_npt_pdpt_buffers + (i * 4096)); 
      npt_pdts_base = ((u32)g_svm_npt_pdts_buffers + (i * 16384));
      npt_pts_base = ((u32)g_svm_npt_pts_buffers + (i * (2048*4096)));
      //extracted --> memory protection component
      //_svm_nptinitialize(npt_pdpt_base, npt_pdts_base, npt_pts_base);
      vcpu->npt_vaddr_ptr = npt_pdpt_base;
      vcpu->npt_vaddr_pdts = npt_pdts_base;
      vcpu->npt_vaddr_pts = npt_pts_base;
      vcpu->npt_asid = npt_current_asid;
      npt_current_asid++;
    }
    
    vcpu->id = g_midtable[i].cpu_lapic_id;
    vcpu->idx = i;
    vcpu->sipivector = 0;
    vcpu->sipireceived = 0;

    g_midtable[i].vcpu_vaddr_ptr = (u32)vcpu;
    printf("\nCPU #%u: vcpu_vaddr_ptr=0x%08x, esp=0x%08x", i, g_midtable[i].vcpu_vaddr_ptr,
      vcpu->esp);
    printf("\n  hsave_vaddr_ptr=0x%08x, vmcb_vaddr_ptr=0x%08x", vcpu->hsave_vaddr_ptr,
          vcpu->vmcb_vaddr_ptr);
  }
}*/


//---wakeupAPs------------------------------------------------------------------
//wake up application processors (cores) in the system
void svm_wakeup_aps(void){
	//step-1: setup AP boot-strap code at in the desired physical memory location 
	//note that we need an address < 1MB since the APs are woken up in real-mode
	//we choose 0x10000 physical or 0x1000:0x0000 logical
  {
    _ap_cr3_value = read_cr3();
    _ap_cr4_value = read_cr4();
    memcpy((void *)0x10000, (void *)_ap_bootstrap_start, (u32)_ap_bootstrap_end - (u32)_ap_bootstrap_start + 1);
  }
	
	//step-2: wake up the APs sending the INIT-SIPI-SIPI sequence as per the
	//MP protocol. Use the APIC for IPI purposes.	
  printf("\nBSP: Using APIC to awaken APs...");
  emhf_arch_x86_baseplatform_wakeupAPs();
  printf("\nBSP: APs should be awake.");
}

//------------------------------------------------------------------------------
//svm_initialize
//initialize SVM on the core
void svm_initialize(VCPU *vcpu){
  //initialize SVM
  _svm_initSVM(vcpu);
 
  //initiaize VMCB
  _svm_initVMCB(vcpu); 
}

//------------------------------------------------------------------------------
//svm_initialize_vmcb_csrip
//initialize CS and RIP fields in the VMCB of the core
void svm_initialize_vmcb_csrip(VCPU *vcpu, u16 cs_selector, u32 cs_base,
		u64 rip){
	struct vmcb_struct *vmcb;
  vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr; 
	
	vmcb->rip = rip;
	vmcb->cs.sel = cs_selector; 
	vmcb->cs.base = cs_base; 
}

//------------------------------------------------------------------------------
//svm_start_hvm
//start a HVM on the core
void svm_start_hvm(VCPU *vcpu){
    struct vmcb_struct *vmcb;
    vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;
    printf("\nCPU(0x%02x): Starting HVM using CS:EIP=0x%04x:0x%08x...", vcpu->id,
			(u16)vmcb->cs.sel, (u32)vmcb->rip);
    __svm_start_hvm(vcpu, __hva2spa__((void*)vcpu->vmcb_vaddr_ptr));
 		//we never get here, if we do, we just return and our caller is responsible
 		//for halting the core as something really bad happened!
}

/*static void svm_apic_setup(VCPU *vcpu){
		printf("\nREFACTORED COMPONENT, SHOULD NEVER BE HERE");
		HALT();
	
}*/



//------------------------------------------------------------------------------
struct isolation_layer g_isolation_layer_svm = {
	.initialize =	svm_initialize,
	//.runtime_exception_handler = svm_runtime_exception_handler,
	.isbsp = svm_isbsp,
	.wakeup_aps = svm_wakeup_aps,
	.hvm_initialize_csrip = svm_initialize_vmcb_csrip,
	//.hvm_apic_setup = svm_apic_setup,
	.hvm_start = svm_start_hvm,
	//.hvm_intercept_handler = emhf_parteventhub_intercept_handler_x86svm,
	//.do_quiesce = svm_do_quiesce,
	//.do_wakeup = svm_do_wakeup,
	//.setupvcpus = svm_setupvcpus,
};


//==============================================================================
//SVM EMHF library interface implementation


//---IOPM Bitmap interface------------------------------------------------------
static void _svm_lib_iopm_set_write(VCPU __attribute__((unused)) *vcpu, u32 __attribute__((unused)) port, u32 __attribute__((unused)) size){
	printf("\n%s: not implemented, halting!", __FUNCTION__);
	HALT();
}

//---MSRPM Bitmap interface------------------------------------------------------
static void _svm_lib_msrpm_set_write(VCPU __attribute__((unused)) *vcpu, u32 __attribute__((unused)) msr){
	printf("\n%s: not implemented, halting!", __FUNCTION__);
	HALT();
}

//---hardware pagetable flush-all routine---------------------------------------
static void _svm_lib_hwpgtbl_flushall(VCPU *vcpu){
	((struct vmcb_struct *)(vcpu->vmcb_vaddr_ptr))->tlb_control=TLB_CONTROL_FLUSHALL;
}

//---hardware pagetable protection manipulation routine-------------------------
static void _svm_lib_hwpgtbl_setprot(VCPU __attribute__((unused)) *vcpu, u64 __attribute__((unused)) gpa, u64 __attribute__((unused)) flags){
	printf("\n%s: not implemented, halting!", __FUNCTION__);
	HALT();
}

static void __attribute__((unused)) _svm_lib_hwpgtbl_setentry(VCPU __attribute__((unused)) *vcpu, u64 __attribute__((unused)) gpa, u64 __attribute__((unused)) value){
	printf("\n%s: not implemented, halting!", __FUNCTION__);
	HALT();
}

static u64 _svm_lib_hwpgtbl_getprot(VCPU __attribute__((unused)) *vcpu, u64 __attribute__((unused)) gpa){
	printf("\n%s: not implemented, halting!", __FUNCTION__);
	HALT(); return 0; /* dummy return; appeases compiler */
}

//---guest page-table walker, returns guest physical address--------------------
//note: returns 0xFFFFFFFF if there is no mapping
u8 * _svm_lib_guestpgtbl_walk(VCPU *vcpu, u32 vaddr){
	struct vmcb_struct *vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;

  if((u32)vmcb->cr4 & CR4_PAE ){
    //PAE paging used by guest
    u32 kcr3 = (u32)vmcb->cr3;
    u32 pdpt_index, pd_index, pt_index, offset;
    u64 paddr;
    pdpt_t kpdpt;
    pdt_t kpd; 
    pt_t kpt; 
    u32 pdpt_entry, pd_entry, pt_entry;
    u32 tmp;

    // get fields from virtual addr 
    pdpt_index = pae_get_pdpt_index(vaddr);
    pd_index = pae_get_pdt_index(vaddr);
    pt_index = pae_get_pt_index(vaddr);
    offset = pae_get_offset_4K_page(vaddr);  

    //grab pdpt entry
    tmp = pae_get_addr_from_32bit_cr3(kcr3);
    kpdpt = (pdpt_t)((u32)tmp); 
    pdpt_entry = kpdpt[pdpt_index];
  
    //grab pd entry
    tmp = pae_get_addr_from_pdpe(pdpt_entry);
    kpd = (pdt_t)((u32)tmp); 
    pd_entry = kpd[pd_index];

    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (u32)pae_get_addr_from_pde(pd_entry);
      kpt = (pt_t)((u32)tmp);  
      pt_entry  = kpt[pt_index];
      
      // find physical page base addr from page table entry 
      paddr = (u64)pae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 2MB page 
      offset = pae_get_offset_big(vaddr);
      paddr = (u64)pae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }
  
    return (u8 *)(u32)paddr;
    
  }else{
    //non-PAE 2 level paging used by guest
    u32 kcr3 = (u32)vmcb->cr3;
    u32 pd_index, pt_index, offset;
    u64 paddr;
    npdt_t kpd; 
    npt_t kpt; 
    u32 pd_entry, pt_entry;
    u32 tmp;

    // get fields from virtual addr 
    pd_index = npae_get_pdt_index(vaddr);
    pt_index = npae_get_pt_index(vaddr);
    offset = npae_get_offset_4K_page(vaddr);  
  
    // grab pd entry
    tmp = npae_get_addr_from_32bit_cr3(kcr3);
    kpd = (npdt_t)((u32)tmp); 
    pd_entry = kpd[pd_index];
  
    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (u32)npae_get_addr_from_pde(pd_entry);
      kpt = (npt_t)((u32)tmp);  
      pt_entry  = kpt[pt_index];
      
      // find physical page base addr from page table entry 
      paddr = (u64)npae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 4MB page 
      offset = npae_get_offset_big(vaddr);
      paddr = (u64)npae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }
  
    return (u8 *)(u32)paddr;
  }
}


//---reboot functionality-------------------------------------------------------
static void _svm_lib_reboot(VCPU __attribute__((unused)) *vcpu){
	printf("\n%s: not implemented, halting!", __FUNCTION__);
	HALT();
}


struct emhf_library g_emhf_library_svm = {
	.emhf_iopm_set_write = _svm_lib_iopm_set_write,
	.emhf_msrpm_set_write = _svm_lib_msrpm_set_write,
	.emhf_hwpgtbl_flushall = _svm_lib_hwpgtbl_flushall,
	.emhf_hwpgtbl_setprot = _svm_lib_hwpgtbl_setprot,
	.emhf_hwpgtbl_getprot = _svm_lib_hwpgtbl_getprot,
	.emhf_guestpgtbl_walk = _svm_lib_guestpgtbl_walk,
	.emhf_reboot = _svm_lib_reboot,
};



