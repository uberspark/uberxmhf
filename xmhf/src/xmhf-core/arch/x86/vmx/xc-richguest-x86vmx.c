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

// smpg-x86vmx - EMHF SMP guest component x86 (VMX) backend
// implementation
// author: amit vasudevan (amitvasudevan@acm.org)
#include <xmhf-core.h> 
#include <xc-x86.h>
#include <xc-x86vmx.h>


//---function to obtain the vcpu of the currently executing core----------------
//XXX: move this into baseplatform as backend
//note: this always returns a valid VCPU pointer
static VCPU *_vmx_getvcpu(void){

#ifndef __XMHF_VERIFICATION__

  int i;
  u32 eax, edx, *lapic_reg;
  u32 lapic_id;
  
  //read LAPIC id of this core
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G
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
  HALT();
  return NULL; // currently unreachable 

#else //__XMHF_VERIFICATION

	//verification is always done in the context of a single core and vcpu/midtable is 
	//populated by the verification driver
	//TODO: LAPIC hardware modeling and moving this function as a public

#endif //__XMHF_VERIFICATION

  
}


//----------------------------------------------------------------------
//Queiscing interfaces
//----------------------------------------------------------------------

static void _vmx_send_quiesce_signal(VCPU __attribute__((unused)) *vcpu){
  volatile u32 *icr_low = (u32 *)(0xFEE00000 + 0x300);
  volatile u32 *icr_high = (u32 *)(0xFEE00000 + 0x310);
  u32 icr_high_value= 0xFFUL << 24;
  u32 prev_icr_high_value;
  u32 delivered;
  
  prev_icr_high_value = *icr_high;
  
  *icr_high = icr_high_value;    //send to all but self
  *icr_low = 0x000C0400UL;      //send NMI        
  
  //check if IPI has been delivered successfully
  //printf("\n%s: CPU(0x%02x): firing NMIs...", __FUNCTION__, vcpu->id);
#ifndef __XMHF_VERIFICATION__  
  do{
	delivered = *icr_high;
	delivered &= 0x00001000;
  }while(delivered);
#else
	//TODO: plug in h/w model of LAPIC, for now assume hardware just
	//works
#endif

  //restore icr high
  *icr_high = prev_icr_high_value;
    
  //printf("\n%s: CPU(0x%02x): NMIs fired!", __FUNCTION__, vcpu->id);
}


//quiesce interface to switch all guest cores into hypervisor mode
//note: we are in atomic processsing mode for this "vcpu"
void xmhf_smpguest_arch_x86vmx_quiesce(VCPU *vcpu){

        //printf("\nCPU(0x%02x): got quiesce signal...", vcpu->id);
        //grab hold of quiesce lock
        spin_lock(&g_vmx_lock_quiesce);
        //printf("\nCPU(0x%02x): grabbed quiesce lock.", vcpu->id);

		vcpu->quiesced = 1;
		//reset quiesce counter
        spin_lock(&g_vmx_lock_quiesce_counter);
        g_vmx_quiesce_counter=0;
        spin_unlock(&g_vmx_lock_quiesce_counter);
        
        //send all the other CPUs the quiesce signal
        g_vmx_quiesce=1;  //we are now processing quiesce
        _vmx_send_quiesce_signal(vcpu);
        
        //wait for all the remaining CPUs to quiesce
        //printf("\nCPU(0x%02x): waiting for other CPUs to respond...", vcpu->id);
        while(g_vmx_quiesce_counter < (g_midtable_numentries-1) );
        //printf("\nCPU(0x%02x): all CPUs quiesced successfully.", vcpu->id);

}

void xmhf_smpguest_arch_x86vmx_endquiesce(VCPU *vcpu){
		(void)vcpu;

        //set resume signal to resume the cores that are quiesced
        //Note: we do not need a spinlock for this since we are in any
        //case the only core active until this point
        g_vmx_quiesce_resume_counter=0;
        //printf("\nCPU(0x%02x): waiting for other CPUs to resume...", vcpu->id);
        g_vmx_quiesce_resume_signal=1;
        
        while(g_vmx_quiesce_resume_counter < (g_midtable_numentries-1) );

		vcpu->quiesced=0;
        g_vmx_quiesce=0;  // we are out of quiesce at this point

        //printf("\nCPU(0x%02x): all CPUs resumed successfully.", vcpu->id);
        
        //reset resume signal
        spin_lock(&g_vmx_lock_quiesce_resume_signal);
        g_vmx_quiesce_resume_signal=0;
        spin_unlock(&g_vmx_lock_quiesce_resume_signal);
                
        //release quiesce lock
        //printf("\nCPU(0x%02x): releasing quiesce lock.", vcpu->id);
        spin_unlock(&g_vmx_lock_quiesce);

        
}

//quiescing handler for #NMI (non-maskable interrupt) exception event
//note: we are in atomic processsing mode for this "vcpu"
void xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(VCPU *vcpu, struct regs *r){
	u32 nmiinhvm;	//1 if NMI originated from the HVM else 0 if within the hypervisor
	u32 _vmx_vmcs_info_vmexit_interrupt_information;
	u32 _vmx_vmcs_info_vmexit_reason;

    (void)r;

	//determine if the NMI originated within the HVM or within the
	//hypervisor. we use VMCS fields for this purpose. note that we
	//use vmread directly instead of relying on vcpu-> to avoid 
	//race conditions
	__vmx_vmread(0x4404, &_vmx_vmcs_info_vmexit_interrupt_information);
	__vmx_vmread(0x4402, &_vmx_vmcs_info_vmexit_reason);
	
	nmiinhvm = ( (_vmx_vmcs_info_vmexit_reason == VMX_VMEXIT_EXCEPTION) && ((_vmx_vmcs_info_vmexit_interrupt_information & INTR_INFO_VECTOR_MASK) == 2) ) ? 1 : 0;
	
	if(g_vmx_quiesce){ //if g_vmx_quiesce =1 process quiesce regardless of where NMI originated from
		//if this core has been quiesced, simply return
			if(vcpu->quiesced)
				return;
				
			vcpu->quiesced=1;
	
			//increment quiesce counter
			spin_lock(&g_vmx_lock_quiesce_counter);
			g_vmx_quiesce_counter++;
			spin_unlock(&g_vmx_lock_quiesce_counter);

			//wait until quiesceing is finished
			//printf("\nCPU(0x%02x): Quiesced", vcpu->id);
			while(!g_vmx_quiesce_resume_signal);
			//printf("\nCPU(0x%02x): EOQ received, resuming...", vcpu->id);

			spin_lock(&g_vmx_lock_quiesce_resume_counter);
			g_vmx_quiesce_resume_counter++;
			spin_unlock(&g_vmx_lock_quiesce_resume_counter);
			
			vcpu->quiesced=0;
	}else{
		//we are not in quiesce
		//inject the NMI if it was triggered in guest mode
		
		if(nmiinhvm){
			if(vcpu->vmcs.control_exception_bitmap & CPU_EXCEPTION_NMI){
				//TODO: hypapp has chosen to intercept NMI so callback
			}else{
				//printf("\nCPU(0x%02x): Regular NMI, injecting back to guest...", vcpu->id);
				vcpu->vmcs.control_VM_entry_exception_errorcode = 0;
				vcpu->vmcs.control_VM_entry_interruption_information = NMI_VECTOR |
					INTR_TYPE_NMI |
					INTR_INFO_VALID_MASK;
			}
		}
	}
	
}

//----------------------------------------------------------------------


//walk guest page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
u8 * xmhf_smpguest_arch_x86vmx_walk_pagetables(VCPU *vcpu, u32 vaddr){
  
  //if rich guest has paging disabled then physical address is the 
  //supplied virtual address itself
	if( !((vcpu->vmcs.guest_CR0 & CR0_PE) && (vcpu->vmcs.guest_CR0 & CR0_PG)) )
		return (u8 *)gpa2hva(vaddr);

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
    if( !(pae_get_flags_from_pdpe(pdpt_entry) & _PAGE_PRESENT) )
		return (u8 *)0xFFFFFFFFUL;
    tmp = pae_get_addr_from_pdpe(pdpt_entry);
    kpd = (pdt_t)((u32)tmp); 
    pd_entry = kpd[pd_index];

    if( !(pae_get_flags_from_pde(pd_entry) & _PAGE_PRESENT) )
		return (u8 *)0xFFFFFFFFUL;


    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (u32)pae_get_addr_from_pde(pd_entry);
      kpt = (pt_t)((u32)tmp);  
      pt_entry  = kpt[pt_index];

	  if( !(pae_get_flags_from_pte(pt_entry) & _PAGE_PRESENT) )
		return (u8 *)0xFFFFFFFFUL;
      
      // find physical page base addr from page table entry 
      paddr = (u64)pae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 2MB page 
      offset = pae_get_offset_big(vaddr);
      paddr = (u64)pae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }
  
    return (u8 *)gpa2hva(paddr);
    
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
  
  
    if( !(npae_get_flags_from_pde(pd_entry) & _PAGE_PRESENT) )
		return (u8 *)0xFFFFFFFFUL;

    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (u32)npae_get_addr_from_pde(pd_entry);
      kpt = (npt_t)((u32)tmp);  
      pt_entry  = kpt[pt_index];
      
      if( !(npae_get_flags_from_pte(pt_entry) & _PAGE_PRESENT) )
		return (u8 *)0xFFFFFFFFUL;

      // find physical page base addr from page table entry 
      paddr = (u64)npae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 4MB page 
      offset = npae_get_offset_big(vaddr);
      paddr = (u64)npae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }

    return (u8 *)gpa2hva(paddr);
  }
}



//handle guest memory reporting (via INT 15h redirection)
void xmhf_smpguest_arch_x86vmx_handle_guestmemoryreporting(context_desc_t context_desc, struct regs *r){
	u16 cs, ip;
	u16 guest_flags;
	VCPU *vcpu = (VCPU *)&g_bplt_vcpu[context_desc.cpu_desc.id];

	//if E820 service then...
	if((u16)r->eax == 0xE820){
		//AX=0xE820, EBX=continuation value, 0 for first call
		//ES:DI pointer to buffer, ECX=buffer size, EDX='SMAP'
		//return value, CF=0 indicated no error, EAX='SMAP'
		//ES:DI left untouched, ECX=size returned, EBX=next continuation value
		//EBX=0 if last descriptor
		printf("\nCPU(0x%02x): INT 15(e820): AX=0x%04x, EDX=0x%08x, EBX=0x%08x, ECX=0x%08x, ES=0x%04x, DI=0x%04x", vcpu->id, 
		(u16)r->eax, r->edx, r->ebx, r->ecx, (u16)vcpu->vmcs.guest_ES_selector, (u16)r->edi);
		
		if( (r->edx == 0x534D4150UL) && (r->ebx < xcbootinfo->memmapinfo_numentries) ){
			
			//copy the E820 descriptor and return its size
			if(!xmhf_smpguest_memcpyto(context_desc, (const void *)((u32)(vcpu->vmcs.guest_ES_base+(u16)r->edi)), (void *)&xcbootinfo->memmapinfo_buffer[r->ebx], sizeof(GRUBE820)) ){
				printf("\n%s: Error in copying e820 descriptor to guest. Halting!", __FUNCTION__);
				HALT();
			}	
				
			r->ecx=20;

			//set EAX to 'SMAP' as required by the service call				
			r->eax=r->edx;

			//we need to update carry flag in the guest EFLAGS register
			//however since INT 15 would have pushed the guest FLAGS on stack
			//we cannot simply reflect the change by modifying vmcb->rflags
			//instead we need to make the change to the pushed FLAGS register on
			//the guest stack. the real-mode IRET frame looks like the following 
			//when viewed at top of stack
			//guest_ip		(16-bits)
			//guest_cs		(16-bits)
			//guest_flags (16-bits)
			//...
		
			//grab guest eflags on guest stack
			if(!xmhf_smpguest_readu16(context_desc, (const void *)((u32)vcpu->vmcs.guest_SS_base + (u16)vcpu->vmcs.guest_RSP + 0x4), &guest_flags)){
				printf("\n%s: Error in reading guest_flags. Halting!", __FUNCTION__);
				HALT();
			}
	
			//increment e820 descriptor continuation value
			r->ebx=r->ebx+1;
					
			if(r->ebx > (xcbootinfo->memmapinfo_numentries-1) ){
				//we have reached the last record, so set CF and make EBX=0
				r->ebx=0;
				guest_flags |= (u16)EFLAGS_CF;
			}else{
				//we still have more records, so clear CF
				guest_flags &= ~(u16)EFLAGS_CF;
			}

			//write updated eflags in guest stack
			if(!xmhf_smpguest_writeu16(context_desc, (const void *)((u32)vcpu->vmcs.guest_SS_base + (u16)vcpu->vmcs.guest_RSP + 0x4), guest_flags)){
				printf("\n%s: Error in updating guest_flags. Halting!", __FUNCTION__);
				HALT();
			}
			  
			
		}else{	//invalid state specified during INT 15 E820, halt
				printf("\nCPU(0x%02x): INT15 (E820), invalid state specified by guest. Halting!", vcpu->id);
				HALT();
		}
		
		//update RIP to execute the IRET following the VMCALL instruction
		//effectively returning from the INT 15 call made by the guest
		vcpu->vmcs.guest_RIP += 3;
	
		return;
	} //E820 service
	
	//ok, this is some other INT 15h service, so simply chain to the original
	//INT 15h handler

	//read the original INT 15h handler which is stored right after the VMCALL instruction
	if(!xmhf_smpguest_readu16(context_desc, 0x4AC+0x4, &ip) || !xmhf_smpguest_readu16(context_desc, 0x4AC+0x6, &cs)){
		printf("\n%s: Error in reading original INT 15h handler. Halting!", __FUNCTION__);
		HALT();
	}
	
	//update VMCS with the CS and IP and let go
	vcpu->vmcs.guest_RIP = ip;
	vcpu->vmcs.guest_CS_base = cs * 16;
	vcpu->vmcs.guest_CS_selector = cs;		 
}


//----------------------------------------------------------------------

//quiescing handler for #NMI (non-maskable interrupt) exception event
//void xmhf_smpguest_arch_x86_eventhandler_nmiexception(VCPU *vcpu, struct regs *r){
void xmhf_smpguest_arch_eventhandler_nmiexception(struct regs *r){
	VCPU *vcpu;
	
	vcpu= _vmx_getvcpu();
		xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(vcpu, r);
}	


//walk guest page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
u8 * xmhf_smpguest_arch_walk_pagetables(context_desc_t context_desc, u32 vaddr){
	VCPU *vcpu = (VCPU *)&g_bplt_vcpu[context_desc.cpu_desc.id];
		return xmhf_smpguest_arch_x86vmx_walk_pagetables(vcpu, vaddr);
}

//quiesce interface to switch all guest cores into hypervisor mode
void xmhf_smpguest_arch_quiesce(VCPU *vcpu){
		xmhf_smpguest_arch_x86vmx_quiesce(vcpu);
}

//endquiesce interface to resume all guest cores after a quiesce
void xmhf_smpguest_arch_endquiesce(VCPU *vcpu){
		xmhf_smpguest_arch_x86vmx_endquiesce(vcpu);
}

