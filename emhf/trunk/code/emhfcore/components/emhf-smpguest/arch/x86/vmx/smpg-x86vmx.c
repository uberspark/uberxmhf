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

// smpg-x86vmx - EMHF SMP guest component x86 (VMX) backend
// implementation
// author: amit vasudevan (amitvasudevan@acm.org)
#include <emhf.h> 

//the LAPIC register that is being accessed during emulation
static u32 g_vmx_lapic_reg __attribute__(( section(".data") )) = 0;

//the LAPIC operation that is being performed during emulation
static u32 g_vmx_lapic_op __attribute__(( section(".data") )) = LAPIC_OP_RSVD;

//guest TF and IF bit values during LAPIC emulation
static u32 g_vmx_lapic_guest_eflags_tfifmask __attribute__(( section(".data") )) = 0;	 



//---hardware pagetable flush-all routine---------------------------------------
static void vmx_apic_hwpgtbl_flushall(VCPU *vcpu){
  __vmx_invept(VMX_EPT_SINGLE_CONTEXT, 
          (u64)vcpu->vmcs.control_EPT_pointer_full, 
          0);
  __vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);

}

//---hardware pagetable protection manipulation routine-------------------------
static void vmx_apic_hwpgtbl_setprot(VCPU *vcpu, u64 gpa, u64 flags){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
  pt[pfn] &= ~(u64)7; //clear all previous flags
  pt[pfn] |= flags; //set new flags
  //flush the EPT mappings for new protections to take effect
  vmx_apic_hwpgtbl_flushall(vcpu);
}

static void vmx_apic_hwpgtbl_setentry(VCPU *vcpu, u64 gpa, u64 value){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
  pt[pfn] = value; //set new value
  //flush the EPT mappings for new protections to take effect
  vmx_apic_hwpgtbl_flushall(vcpu);
}


static u64 __attribute__((unused)) vmx_apic_hwpgtbl_getprot(VCPU *vcpu, u64 gpa){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
  return (pt[pfn] & (u64)7) ;
}


//---checks if all logical cores have received SIPI
//returns 1 if yes, 0 if no
static u32 have_all_cores_recievedSIPI(void){
  u32 i;
  VCPU *vcpu;
  
	//iterate through all logical processors in master-id table
	for(i=0; i < g_midtable_numentries; i++){
  	vcpu = (VCPU *)g_midtable[i].vcpu_vaddr_ptr;
		if(vcpu->isbsp)
			continue;	//BSP does not receive SIPI
		
		if(!vcpu->sipireceived)
			return 0;	//one or more logical cores have not received SIPI
  }
  
  return 1;	//all logical cores have received SIPI
}

//---SIPI processing logic------------------------------------------------------
//return 1 if lapic interception has to be discontinued, typically after
//all aps have received their SIPI, else 0
static u32 processSIPI(VCPU *vcpu, u32 icr_low_value, u32 icr_high_value){
  //we assume that destination is always physical and 
  //specified via top 8 bits of icr_high_value
  u32 dest_lapic_id;
  VCPU *dest_vcpu = (VCPU *)0;
  
  ASSERT( (icr_low_value & 0x000C0000) == 0x0 );
  
  dest_lapic_id= icr_high_value >> 24;
  
  printf("\nCPU(0x%02x): %s, dest_lapic_id is 0x%02x", 
		vcpu->id, __FUNCTION__, dest_lapic_id);
  
  //find the vcpu entry of the core with dest_lapic_id
  {
    int i;
    for(i=0; i < (int)g_midtable_numentries; i++){
      if(g_midtable[i].cpu_lapic_id == dest_lapic_id){
        dest_vcpu = (VCPU *)g_midtable[i].vcpu_vaddr_ptr;
        ASSERT( dest_vcpu->id == dest_lapic_id );
        break;        
      }
    }
    
    ASSERT( dest_vcpu != (VCPU *)0 );
  }

  printf("\nCPU(0x%02x): found AP to pass SIPI; id=0x%02x, vcpu=0x%08x",
      vcpu->id, dest_vcpu->id, (u32)dest_vcpu);  
  
  
  //send the sipireceived flag to trigger the AP to start the HVM
  if(dest_vcpu->sipireceived){
    printf("\nCPU(0x%02x): destination CPU #0x%02x has already received SIPI, ignoring", vcpu->id, dest_vcpu->id);
  }else{
		dest_vcpu->sipivector = (u8)icr_low_value;
  	dest_vcpu->sipireceived = 1;
  	printf("\nCPU(0x%02x): Sent SIPI command to AP, should awaken it!",
               vcpu->id);
  }

	if(have_all_cores_recievedSIPI())
		return 1;	//all cores have received SIPI, we can discontinue LAPIC interception
	else
		return 0;	//some cores are still to receive SIPI, continue LAPIC interception  
}


static void _vmx_send_quiesce_signal(VCPU *vcpu){
  volatile u32 *icr_low = (u32 *)(0xFEE00000 + 0x300);
  volatile u32 *icr_high = (u32 *)(0xFEE00000 + 0x310);
  u32 icr_high_value= 0xFFUL << 24;
  u32 prev_icr_high_value;
  u32 delivered;
    
  prev_icr_high_value = *icr_high;
  
  *icr_high = icr_high_value;    //send to all but self
  *icr_low = 0x000C0400UL;      //send NMI        
  
  //check if IPI has been delivered successfully
  printf("\n%s: CPU(0x%02x): firing NMIs...", __FUNCTION__, vcpu->id);
  do{
	delivered = *icr_high;
	delivered &= 0x00001000;
  }while(delivered);
  
  //restore icr high
  *icr_high = prev_icr_high_value;
    
  printf("\n%s: CPU(0x%02x): NMIs fired!", __FUNCTION__, vcpu->id);
}


//---VMX APIC setup-------------------------------------------------------------
//this function sets up the EPT for the vcpu core to intercept LAPIC
//accesses.
//NOTE: this function MUST be called only from the BSP and the vcpu
//passed in should also be that of the BSP
void emhf_smpguest_arch_x86vmx_initialize(VCPU *vcpu){
  u32 eax, edx;

	//we should only be called from the BSP
	ASSERT( vcpu->isbsp == 1 );	
  
  //clear virtual LAPIC page
  memset((void *)&g_vmx_virtual_LAPIC_base, 0, PAGE_SIZE_4K);
  
  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  ASSERT( edx == 0 ); //APIC should be below 4G
  g_vmx_lapic_base = eax & 0xFFFFF000UL;
  //printf("\nBSP(0x%02x): LAPIC base=0x%08x", vcpu->id, g_vmx_lapic_base);
  
  //set physical 4K page of LAPIC base address to not-present
  //this will cause EPT violation which is then
  //handled by vmx_lapic_access_handler
	vmx_apic_hwpgtbl_setprot(vcpu, g_vmx_lapic_base, 0);
}


//------------------------------------------------------------------------------
//if there is a read request, store the register accessed
//store request as READ
//map npt entry of the physical LAPIC page with lapic_base and single-step
//if there is a write request, map npt entry of physical LAPIC
//page with physical address of virtual_LAPIC page, store the
//register accessed, store request as WRITE and single-step
//XXX TODO: return value currently meaningless
u32 emhf_smpguest_arch_x86vmx_eventhandler_hwpgtblviolation(VCPU *vcpu, u32 paddr, u32 errorcode){
	//printf("\nCPU(0x%02x): LAPIC: p=0x%08x, ecode=0x%08x", vcpu->id,
	//		paddr, errorcode);

  //get LAPIC register being accessed
  g_vmx_lapic_reg = (paddr - g_vmx_lapic_base);

  if(errorcode & EPT_ERRORCODE_WRITE){
    //printf("\nCPU(0x%02x): LAPIC[WRITE] reg=0x%08x", vcpu->id,
		//	g_vmx_lapic_reg);

		if(g_vmx_lapic_reg == LAPIC_ICR_LOW || g_vmx_lapic_reg == LAPIC_ICR_HIGH ){
      g_vmx_lapic_op = LAPIC_OP_WRITE;

      //change LAPIC physical address in EPT to point to physical address 
			//of memregion_virtual_LAPIC
			vmx_apic_hwpgtbl_setentry(vcpu, g_vmx_lapic_base, 
					(u64)hva2spa(&g_vmx_virtual_LAPIC_base) | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			

    }else{
      g_vmx_lapic_op = LAPIC_OP_RSVD;

      //change LAPIC physical address in EPT to point to physical LAPIC
      vmx_apic_hwpgtbl_setentry(vcpu, g_vmx_lapic_base, 
					(u64)g_vmx_lapic_base | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			
    }    
  }else{
    //printf("\nCPU(0x%02x): LAPIC[READ] reg=0x%08x", vcpu->id,
		//	g_vmx_lapic_reg);

    if(g_vmx_lapic_reg == LAPIC_ICR_LOW || g_vmx_lapic_reg == LAPIC_ICR_HIGH ){
      g_vmx_lapic_op = LAPIC_OP_READ;

      //change LAPIC physical address in EPT to point to physical address 
			//of memregion_virtual_LAPIC
			vmx_apic_hwpgtbl_setentry(vcpu, g_vmx_lapic_base, 
					(u64)hva2spa(&g_vmx_virtual_LAPIC_base) | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			

    }else{
      g_vmx_lapic_op = LAPIC_OP_RSVD;

      //change LAPIC physical address in EPT to point to physical LAPIC
      vmx_apic_hwpgtbl_setentry(vcpu, g_vmx_lapic_base, 
					(u64)g_vmx_lapic_base | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			
    }  
  }

  //setup #DB intercept 
	vcpu->vmcs.control_exception_bitmap |= (1UL << 1); //enable INT 1 intercept (#DB fault)
  
	//save guest IF and TF masks
  g_vmx_lapic_guest_eflags_tfifmask = (u32)vcpu->vmcs.guest_RFLAGS & ((u32)EFLAGS_IF | (u32)EFLAGS_TF);	

  //set guest TF
	vcpu->vmcs.guest_RFLAGS |= EFLAGS_TF;
	
  //disable interrupts by clearing guest IF on this CPU until we get 
	//control in lapic_access_dbexception after a DB exception
	vcpu->vmcs.guest_RFLAGS &= ~(EFLAGS_IF);

    return 0; /* dummy; currently meaningless */
}


//------------------------------------------------------------------------------
//within single-step
//if request was READ, we can get the value read by reading from
//the LAPIC register 
//if request was WRITE, we get the value from reading virtual_LAPIC_vaddr
//to propagate we just write to the physical LAPIC

void emhf_smpguest_arch_x86vmx_eventhandler_dbexception(VCPU *vcpu, struct regs *r){
  u32 delink_lapic_interception=0;
  
  if(g_vmx_lapic_op == LAPIC_OP_WRITE){
    u32 src_registeraddress, dst_registeraddress;
    u32 value_tobe_written;
    
    ASSERT( (g_vmx_lapic_reg == LAPIC_ICR_LOW) || (g_vmx_lapic_reg == LAPIC_ICR_HIGH) );
   
    src_registeraddress = (u32)&g_vmx_virtual_LAPIC_base + g_vmx_lapic_reg;
    dst_registeraddress = (u32)g_vmx_lapic_base + g_vmx_lapic_reg;
    
    value_tobe_written= *((u32 *)src_registeraddress);
    
    if(g_vmx_lapic_reg == LAPIC_ICR_LOW){
      if ( (value_tobe_written & 0x00000F00) == 0x500){
        //this is an INIT IPI, we just void it
        printf("\n0x%04x:0x%08x -> (ICR=0x%08x write) INIT IPI detected and skipped, value=0x%08x", 
          (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP, g_vmx_lapic_reg, value_tobe_written);
      }else if( (value_tobe_written & 0x00000F00) == 0x600 ){
        //this is a STARTUP IPI
        u32 icr_value_high = *((u32 *)((u32)&g_vmx_virtual_LAPIC_base + (u32)LAPIC_ICR_HIGH));
        printf("\n0x%04x:0x%08x -> (ICR=0x%08x write) STARTUP IPI detected, value=0x%08x", 
          (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP, g_vmx_lapic_reg, value_tobe_written);        
				delink_lapic_interception=processSIPI(vcpu, value_tobe_written, icr_value_high);
      }else{
        //neither an INIT or SIPI, just propagate this IPI to physical LAPIC
        *((u32 *)dst_registeraddress) = value_tobe_written;
      }
    }else{
      *((u32 *)dst_registeraddress) = value_tobe_written;
    }
                
  }else if( g_vmx_lapic_op == LAPIC_OP_READ){
    u32 src_registeraddress;
    u32 value_read;
    ASSERT( (g_vmx_lapic_reg == LAPIC_ICR_LOW) || (g_vmx_lapic_reg == LAPIC_ICR_HIGH) );

    src_registeraddress = (u32)&g_vmx_virtual_LAPIC_base + g_vmx_lapic_reg;
   
    value_read = *((u32 *)src_registeraddress);
  }

//fallthrough:  
  //clear #DB intercept 
	vcpu->vmcs.control_exception_bitmap &= ~(1UL << 1); 

  //make LAPIC page inaccessible and flush TLB
  if(delink_lapic_interception){
    printf("\n%s: delinking LAPIC interception since all cores have SIPI", __FUNCTION__);
    vmx_apic_hwpgtbl_setentry(vcpu, g_vmx_lapic_base, 
					(u64)g_vmx_lapic_base | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			
  }else{
    vmx_apic_hwpgtbl_setentry(vcpu, g_vmx_lapic_base, 
					(u64)g_vmx_lapic_base);			
	}

  //restore guest IF and TF
  vcpu->vmcs.guest_RFLAGS &= ~(EFLAGS_IF);
  vcpu->vmcs.guest_RFLAGS &= ~(EFLAGS_TF);
  vcpu->vmcs.guest_RFLAGS |= g_vmx_lapic_guest_eflags_tfifmask;
}


//quiesce interface to switch all guest cores into hypervisor mode
void emhf_smpguest_arch_x86vmx_quiesce(VCPU *vcpu){
        printf("\nCPU(0x%02x): got quiesce signal...", vcpu->id);
        //grab hold of quiesce lock
        spin_lock(&g_vmx_lock_quiesce);
        printf("\nCPU(0x%02x): grabbed quiesce lock.", vcpu->id);

        spin_lock(&g_vmx_lock_quiesce_counter);
        g_vmx_quiesce_counter=0;
        spin_unlock(&g_vmx_lock_quiesce_counter);
        
        //send all the other CPUs the quiesce signal
        g_vmx_quiesce=1;  //we are now processing quiesce
        _vmx_send_quiesce_signal(vcpu);
        
        //wait for all the remaining CPUs to quiesce
        printf("\nCPU(0x%02x): waiting for other CPUs to respond...", vcpu->id);
        while(g_vmx_quiesce_counter < (g_midtable_numentries-1) );
        printf("\nCPU(0x%02x): all CPUs quiesced successfully.", vcpu->id);
	
}

void emhf_smpguest_arch_x86vmx_endquiesce(VCPU *vcpu){
        //set resume signal to resume the cores that are quiesced
        //Note: we do not need a spinlock for this since we are in any
        //case the only core active until this point
        g_vmx_quiesce_resume_counter=0;
        printf("\nCPU(0x%02x): waiting for other CPUs to resume...", vcpu->id);
        g_vmx_quiesce_resume_signal=1;
        
        while(g_vmx_quiesce_resume_counter < (g_midtable_numentries-1) );

        g_vmx_quiesce=0;  // we are out of quiesce at this point

        printf("\nCPU(0x%02x): all CPUs resumed successfully.", vcpu->id);
        
        //reset resume signal
        spin_lock(&g_vmx_lock_quiesce_resume_signal);
        g_vmx_quiesce_resume_signal=0;
        spin_unlock(&g_vmx_lock_quiesce_resume_signal);
                
        //release quiesce lock
        printf("\nCPU(0x%02x): releasing quiesce lock.", vcpu->id);
        spin_unlock(&g_vmx_lock_quiesce);
}        

//quiescing handler for #NMI (non-maskable interrupt) exception event
void emhf_smpguest_arch_x86vmx_eventhandler_nmiexception(VCPU *vcpu, struct regs *r){
	if( (!vcpu->nmiinhvm) && (!g_vmx_quiesce) ){
    printf("\nCPU(0x%02x): Spurious NMI within hypervisor. halt!", vcpu->id);
    HALT();
  }

	if(g_vmx_quiesce){
    //ok this NMI is because of g_vmx_quiesce. note: g_vmx_quiesce can be 1 and
    //this could be a NMI for the guest. we have no way of distinguising
    //this. however, since g_vmx_quiesce=1, we can handle this NMI as a quiesce NMI
    //and rely on the platform h/w to reissue the NMI later
    printf("\nCPU(0x%02x): NMI for core quiesce", vcpu->id);
    printf("\nCPU(0x%02x): CS:EIP=0x%04x:0x%08x", vcpu->id, (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);
  
    printf("\nCPU(0x%02x): quiesced, updating counter. awaiting EOQ...", vcpu->id);
    spin_lock(&g_vmx_lock_quiesce_counter);
    g_vmx_quiesce_counter++;
    spin_unlock(&g_vmx_lock_quiesce_counter);
    
    while(!g_vmx_quiesce_resume_signal);
    printf("\nCPU(0x%02x): EOQ received, resuming...", vcpu->id);
    
    spin_lock(&g_vmx_lock_quiesce_resume_counter);
    g_vmx_quiesce_resume_counter++;
    spin_unlock(&g_vmx_lock_quiesce_resume_counter);
    
    //printf("\nCPU(0x%08x): Halting!", vcpu->id);
    //HALT();
    
  }else{
    //we are not in quiesce, so simply inject this NMI back to guest
    ASSERT( vcpu->nmiinhvm == 1 );
    printf("\nCPU(0x%02x): Regular NMI, injecting back to guest...", vcpu->id);
		vcpu->vmcs.control_VM_entry_exception_errorcode = 0;
					vcpu->vmcs.control_VM_entry_interruption_information = NMI_VECTOR |
			     INTR_TYPE_NMI |
			     INTR_INFO_VALID_MASK;
  }
}

//perform required setup after a guest awakens a new CPU
void emhf_smpguest_arch_x86vmx_postCPUwakeup(VCPU *vcpu){
	//setup guest CS and EIP as specified by the SIPI vector
	vcpu->vmcs.guest_CS_selector = ((vcpu->sipivector * PAGE_SIZE_4K) >> 4); 
	vcpu->vmcs.guest_CS_base = (vcpu->sipivector * PAGE_SIZE_4K); 
	vcpu->vmcs.guest_RIP = 0x0ULL;
}

//walk guest page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
u8 * emhf_smpguest_arch_x86vmx_walk_pagetables(VCPU *vcpu, u32 vaddr){
  if((u32)vcpu->vmcs.guest_CR4 & CR4_PAE ){
    //PAE paging used by guest
    u32 kcr3 = (u32)vcpu->vmcs.guest_CR3;
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
    u32 kcr3 = (u32)vcpu->vmcs.guest_CR3;
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
