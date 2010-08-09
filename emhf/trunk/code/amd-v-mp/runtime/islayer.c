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

// islayer.c
// author: amit vasudevan (amitvasudevan@acm.org) and ning qu (qning@cmu.edu)
#include <target.h>


//---globals and externs--------------------------------------------------------
VCPU *getvcpu(void);

extern u32 midtable_numentries;

//the quiesce counter, all CPUs except for the one requesting the
//quiesce will increment this when they get their quiesce signal
u32 quiesce_counter=0;
u32 lock_quiesce_counter=1; //spinlock to access the above

//resume counter to rally all CPUs after resumption from quiesce
u32 quiesce_resume_counter=0;
u32 lock_quiesce_resume_counter=1; //spinlock to access the above

//the quiesce variable and its lock
u32 quiesce=0;      //if 1, then we have a quiesce in process
u32 lock_quiesce=1; 

//resume signal
u32 quiesce_resume_signal=0; //signal becomes 1 to resume after quiescing
u32 lock_quiesce_resume_signal=1; //spinlock to access the above

//---NMI processing routine-----------------------------------------------------
void processNMI(VCPU *vcpu, struct vmcb_struct *vmcb, struct regs *r){
  if( (!vcpu->nmiinhvm) && (!quiesce) ){
    printf("\nCPU(0x%02x): Spurious NMI within hypervisor. halt!", vcpu->id);
    HALT();
  }

  if(quiesce){
    //ok this NMI is because of quiesce. note: quiesce can be 1 and
    //this could be a NMI for the guest. we have no way of distinguising
    //this. however, since quiesce=1, we can handle this NMI as a quiesce NMI
    //and rely on the platform h/w to reissue the NMI later
    printf("\nCPU(0x%02x): NMI for core quiesce", vcpu->id);
    printf("\nCPU(0x%02x): CS:EIP=0x%04x:0x%08x", vcpu->id, (u16)vmcb->cs.sel, (u32)vmcb->rip);
  
    printf("\nCPU(0x%02x): quiesced, updating counter. awaiting EOQ...", vcpu->id);
    spin_lock(&lock_quiesce_counter);
    quiesce_counter++;
    spin_unlock(&lock_quiesce_counter);
    
    while(!quiesce_resume_signal);
    printf("\nCPU(0x%02x): EOQ received, resuming...", vcpu->id);
    
    spin_lock(&lock_quiesce_resume_counter);
    quiesce_resume_counter++;
    spin_unlock(&lock_quiesce_resume_counter);
    
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
}

//---generic exception handler--------------------------------------------------
void XtRtmExceptionHandler(u32 vector, struct regs *r){
	VCPU *vcpu = getvcpu();
  INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE *noecode_sf= (INTR_SAMEPRIVILEGE_STACKFRAME_NOERRORCODE *)((u32)r->esp + (u32)0x0C);
  INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE *ecode_sf= (INTR_SAMEPRIVILEGE_STACKFRAME_ERRORCODE *)((u32)r->esp + (u32)0x0C);

  printf("\nCPU(0x%02x): XtRtmExceptionHandler: Exception=0x%08X", vcpu->id, vector);
  printf("\nCPU(0x%02x): ESP=0x%08x", vcpu->id, r->esp);
  if(vector == 0x2){
    processNMI(vcpu, (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr, r);
    return;
  }	
  //HALT();
}




//---quiescing implementation---------------------------------------------------
void send_quiesce_signal(VCPU *vcpu, struct vmcb_struct *vmcb){
  u32 *icr_low = (u32 *)(0xFEE00000 + 0x300);
  u32 *icr_high = (u32 *)(0xFEE00000 + 0x310);
  u32 icr_high_value= 0xFFUL << 24;
  u32 prev_icr_high_value;
    
  prev_icr_high_value = *icr_high;
  
  *icr_high = icr_high_value;    //send to all but self
  *icr_low = 0x000C0400UL;      //send NMI        
  
  //restore icr high
  *icr_high = prev_icr_high_value;
    
  printf("\nCPU(0x%02x): NMIs fired!", vcpu->id);
}


void do_quiesce(VCPU *vcpu, struct vmcb_struct *vmcb){
        printf("\nCPU(0x%02x): got quiesce signal...", vcpu->id);
        //grab hold of quiesce lock
        spin_lock(&lock_quiesce);
        printf("\nCPU(0x%02x): grabbed quiesce lock.", vcpu->id);

        spin_lock(&lock_quiesce_counter);
        quiesce_counter=0;
        spin_unlock(&lock_quiesce_counter);
        
        //send all the other CPUs the quiesce signal
        quiesce=1;  //we are now processing quiesce
        send_quiesce_signal(vcpu, vmcb);
        
        //wait for all the remaining CPUs to quiesce
        printf("\nCPU(0x%02x): waiting for other CPUs to respond...", vcpu->id);
        while(quiesce_counter < (midtable_numentries-1) );
        printf("\nCPU(0x%02x): all CPUs quiesced successfully.", vcpu->id);
        
        //perform operation now with all CPUs halted...
        
        //set resume signal to resume the cores that are quiesced
        //Note: we do not need a spinlock for this since we are in any
        //case the only core active until this point
        quiesce_resume_counter=0;
        printf("\nCPU(0x%02x): waiting for other CPUs to resume...", vcpu->id);
        quiesce_resume_signal=1;
        
        while(quiesce_resume_counter < (midtable_numentries-1) );

        quiesce=0;  // we are out of quiesce at this point

        printf("\nCPU(0x%02x): all CPUs resumed successfully.", vcpu->id);
        
        //reset resume signal
        spin_lock(&lock_quiesce_resume_signal);
        quiesce_resume_signal=0;
        spin_unlock(&lock_quiesce_resume_signal);
                
        //release quiesce lock
        printf("\nCPU(0x%02x): releasing quiesce lock.", vcpu->id);
        spin_unlock(&lock_quiesce);
        
        //printf("\nCPU(0x%02x): Halting!", vcpu->id);
        //HALT();
}

//---guest kernel page-table walker---------------------------------------------
u32 kernel_pt_walker(struct vmcb_struct *vmcb, u32 vaddr){
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


//------------------------------------------------------------------------------
u8 guest_readcode_byte(struct vmcb_struct *vmcb, u32 addr){
	u32 paddr;
	
	if((u32)vmcb->cr0 & CR0_PG)
		paddr=kernel_pt_walker(vmcb, addr); //paging enabled in guest, so addr is virtual
	else
		paddr=vmcb->cs.base + addr; //paging is not enabled, we use CS base and offset of addr	

	return ( *(u8 *)paddr );
}


//------------------------------------------------------------------------------
//handle_swint - software INTn intercept handling
extern GRUBE820 *grube820list;

u32 ine820handler=0;
handle_swint(struct vmcb_struct *vmcb, struct regs *r){
	u8 op1, op2;

	//the way to get the vector is to look into the guest code
	//vmcb->rip points to the SWINT instruction
	op1=guest_readcode_byte(vmcb, vmcb->rip);
	op2=guest_readcode_byte(vmcb, vmcb->rip+1);

	if(op1 == 0xCD){
		if(op2 == 0x15){
			printf("\nINT15: EAX=0x%08X", vmcb->rax);
			if(ine820handler && (u32)vmcb->rax != 0xE820){
				ine820handler=0;
				vmcb->general1_intercepts &= ~(u32) GENERAL1_INTERCEPT_SWINT;
				printf("\ndelinking SWINT...");
			}
			
			if((u32)vmcb->rax == 0xE820){
				ine820handler=1;
				//EAX=0xE820, EBX=continuation value, 0 for first call
				//ES:DI pointer to buffer, ECX=buffer size, EDX='SMAP'
				if(r->edx != 0x534D4150UL){ //'SMAP'
					printf("\nunhandled INT15h E820, invalid signature!");
					HALT();
				}			
			
				//return value, CF=0 indicated no error, EAX='SMAP'
				//ES:DI left untouched, ECX=size returned, EBX=next continuation value
				//EBX=0 if last descriptor
				if(r->ebx > lpb->XtVmmE820NumEntries){
					printf("\ninvalid continuation value specified!");
					HALT();				
				}
			
				printf("\nECX=%u", r->ecx);
			
				printf("\nreturning for index=%u", r->ebx);
				printf("\nES=0x%04X, DI=0x%04X", vmcb->es.base, (u16)r->edi);
				memcpy((void *)((u32)((vmcb->es.base)+(u16)r->edi)), (void *)&grube820list[r->ebx],
					sizeof(GRUBE820));
				r->ebx=r->ebx+1;
				
				
				vmcb->rax=(u64)r->edx;
				r->ecx=20;

				if(r->ebx > lpb->XtVmmE820NumEntries){
					r->ebx=0;	
					vmcb->rflags |= ((u64)0x1);
				}else{
					vmcb->rflags &= ~((u64)0x1);
				}

				printf("\nnext continuation value=%u", r->ebx);
				vmcb->eventinj.bytes=0;
				vmcb->rip+=2;
				return;
			}
		}
		
		//inject it back into the guest
		vmcb->eventinj.fields.vector= op2;
		vmcb->eventinj.fields.type=0x4;
		vmcb->eventinj.fields.ev=0;
		vmcb->eventinj.fields.v=1;
		vmcb->rip+=2;
	}else{
		printf("\nSWINT:0x%02X 0x%02X", op1, op2);
		HALT();
	}
}
//end handle_swint - software INTn intercept handling
//------------------------------------------------------------------------------

extern u32 lapic_base;

//invoked on a nested page-fault 
//struct regs *r -> guest OS GPR state
//win_vmcb	-> rest of the guest OS state
//win_vmcb->exitinfo1 = error code similar to PF
//win_vmcb->exitinfo2 = faulting guest OS physical address
void npt_handleexit(VCPU *vcpu, struct regs *r)
{
  struct vmcb_struct *vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;
  u32 gpa = vmcb->exitinfo2;
  u32 errorcode = vmcb->exitinfo1;
  
  if(gpa >= lapic_base && gpa < (lapic_base + PAGE_SIZE_4K)){
    //LAPIC access, xfer control to apropriate handler
    //printf("\n0x%04x:0x%08x -> LAPIC access, gpa=0x%08x, errorcode=0x%08x", 
    //  (u16)vmcb->cs.sel, (u32)vmcb->rip, gpa, errorcode);
    lapic_access_handler(vcpu, gpa, errorcode);
    //HALT();
  }  
  
  return;
}

void lapic_access_dbexception(VCPU *vcpu, struct regs *r);

//---NMI handling---------------------------------------------------------------
// note: we use NMI for core quiescing, we simply inject the others back
// into the guest in the normal case
void handle_nmi(VCPU *vcpu, struct vmcb_struct *vmcb, struct regs *r){
    //now we adopt a simple trick, this NMI is pending, the only
    //way we can dismiss it is if we set GIF=0 and make GIF=1 so that
    //the core thinks it must dispatch the pending NMI :p
    //set nmiinhvm to 1 since this NMI was when the core was in HVM 
    vcpu->nmiinhvm=1;
    __asm__ __volatile__("clgi\r\n");
    __asm__ __volatile__("stgi\r\n"); //at this point we get control in
                                      //our exception handler which handles the rest
    printf("\nCPU(0x%02x): resuming guest...", vcpu->id);
}

//---IO Intercept handling------------------------------------------------------
void handle_ioio(VCPU *vcpu, struct vmcb_struct *vmcb, struct regs *r){
  ioio_info_t ioinfo;
  u32 ret, retvalue;
  
  ioinfo.bytes = vmcb->exitinfo1;

  if (ioinfo.fields.rep || ioinfo.fields.str){
    printf("\nCPU(0x%02x): Fatal, unsupported batch I/O ops!", vcpu->id);
    HALT();
  }

  //handle IO intercept, IO can either be skipped for the guest
  // or can be chained back
  //printf("\nCPU(0x%02x): IO Intercept, port=0x%04x, type=%u", vcpu->id, 
  //    ioinfo.fields.port, ioinfo.fields.type);
  
  //for now we just chain
	if (ioinfo.fields.type){
    // IN 
    if (ioinfo.fields.sz8)
      *(u8 *)&vmcb->rax = inb(ioinfo.fields.port);
    if (ioinfo.fields.sz16)
      *(u16 *)&vmcb->rax = inw(ioinfo.fields.port);
    if (ioinfo.fields.sz32) 
       *(u32 *)&vmcb->rax = inl(ioinfo.fields.port);
  }else{
    // OUT 
    if (ioinfo.fields.sz8)
      outb((u8)vmcb->rax, ioinfo.fields.port);
    if (ioinfo.fields.sz16)
      outw((u16)vmcb->rax, ioinfo.fields.port);
    if (ioinfo.fields.sz32) 
      outl((u32)vmcb->rax, ioinfo.fields.port);
  }
  
  // exitinfo2 stores the rip of instruction following the IN/OUT 
  vmcb->rip = vmcb->exitinfo2;
}
  
//---MSR intercept handling-----------------------------------------------------
void handle_msr(VCPU *vcpu, struct vmcb_struct *vmcb, struct regs *r){
  ASSERT( (vmcb->exitinfo1 == 0) || (vmcb->exitinfo1 == 1) );
  printf("\nCPU(0x%02x): MSR intercept, type=%u, MSR=0x%08x", vcpu->id,
    (u32)vmcb->exitinfo1, r->ecx);
  switch(vmcb->exitinfo1){
    case 0:{  //RDMSR with MSR in ECX
      rdmsr(r->ecx, &r->eax, &r->edx);        
    }
    break;
    
    case 1:{  //WRMSR with MSR in ECX
      wrmsr(r->ecx, r->eax, r->edx);
    }
    break;
  }  

  vmcb->rip += 2; 
}


u32 XtRtmIslInterceptHandler(VCPU *vcpu, struct regs *r);
u32 XtRtmIslInterceptHandler(VCPU *vcpu, struct regs *r){
  struct vmcb_struct *vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;
  
  vmcb->tlb_control = TLB_CONTROL_NOTHING;
    
  switch(vmcb->exitcode){
    //IO interception
 		case VMEXIT_IOIO:{
   		handle_ioio(vcpu, vmcb, r);
   	}
   	break;
  
    //MSR interception
    case VMEXIT_MSR:{
      handle_msr(vcpu, vmcb, r);
    }
    break;
    
    //this only gets called on BSP
    case VMEXIT_SWINT:{
			handle_swint(vmcb, r);
		}
		break;

#ifdef __NESTED_PAGING__	
	  case VMEXIT_NPF:{
      ASSERT( isbsp() == 1); //only BSP gets a NPF during LAPIC SIPI detection
			npt_handleexit(vcpu, r);
    }
		break;
#endif		

 		case VMEXIT_EXCEPTION_DB:{
     ASSERT(isbsp() == 1); //LAPIC SIPI detection only happens on BSP
     lapic_access_dbexception(vcpu, r);
     }
     break;


    case VMEXIT_INIT:{
      printf("\nCPU(0x%02x): INIT intercepted, halting.", vcpu->id);
      printf("\nGuest CS:EIP=0x%04x:0x%08x", (u16)vmcb->cs.sel, (u32)vmcb->rip);
      {
        u8 *code;
        u32 paddr;
        int i;
        paddr= kernel_pt_walker(vmcb, (u32)vmcb->rip); 
        code = (u8 *)paddr; 
        printf("\nCode physical address=0x%08x\n", (u32)code);
        for(i=0; i < 16; i++)
          printf("0x%02x ", code[i]);
        HALT();
      }
      
      //initspin:
      //  goto initspin;
    }
    break;

    case VMEXIT_VMMCALL:{
      u32 call_id= (u32)vmcb->rax;
      if(call_id == 0x0000BEEF){
        do_quiesce(vcpu, vmcb);
      }else{
        printf("\nCPU(0x%02x): unhandled vmmcall id=0x%08x", vcpu->id, call_id);
        HALT();
      }
    
      vmcb->rip += 3;
    }
    break;

    case VMEXIT_NMI:{
        handle_nmi(vcpu, vmcb, r);
      }
      break;
    
		default:{
				printf("\nUnhandled Intercept:0x%08X", vmcb->exitcode);
				printf("\nCS:EIP=0x%04x:0x%08x", (u16)vmcb->cs.sel, (u32)vmcb->rip);
        HALT();
		}
	}	//end switch(vmcb->exitcode)	

	return 0;
}

