// apic.c - APIC virtualization support for Intel cores
// author: amit vasudevan (amitvasudevan@acm.org)
#include <target.h>

//forward prototypes
u32 processSIPI(VCPU *vcpu, u32 icr_low_value, u32 icr_high_value);

//---globals referenced by this module------------------------------------------
extern u8 memregion_virtual_LAPIC[];
extern u32 midtable_numentries;
extern MIDTAB *midtable;

//this function sets up the EPT for the vcpu core to intercept LAPIC
//accesses.
//NOTE: this function MUST be called only from the BSP and the vcpu
//passed in should also be that of the BSP
void apic_setup(VCPU *vcpu){
  u32 eax, edx;

	//we should only be called from the BSP
	ASSERT( isbsp() == 1 );	
  
  //clear virtual LAPIC page
  memset((void *)&memregion_virtual_LAPIC, 0, PAGE_SIZE_4K);
  
  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  ASSERT( edx == 0 ); //APIC should be below 4G
  vcpu->lapic_base = eax & 0xFFFFF000UL;
  printf("\nBSP(0x%02x): LAPIC base=0x%08x", vcpu->id, vcpu->lapic_base);
  
  //initialize LAPIC interception variables
  vcpu->lapic_reg=0;
  vcpu->lapic_op=LAPIC_OP_RSVD;
  
  //set physical 4K page of LAPIC base address to not-present
  //this will cause EPT violation which is then
  //handled by lapic_access_handler
	emhf_hwpgtbl_setprot(vcpu, vcpu->lapic_base, 0);
}


//------------------------------------------------------------------------------
//if there is a read request, store the register accessed
//store request as READ
//map npt entry of the physical LAPIC page with lapic_base and single-step
//if there is a write request, map npt entry of physical LAPIC
//page with physical address of virtual_LAPIC page, store the
//register accessed, store request as WRITE and single-step

u32 lapic_access_handler(VCPU *vcpu, u32 paddr, u32 errorcode){
	//printf("\nCPU(0x%02x): LAPIC: p=0x%08x, ecode=0x%08x", vcpu->id,
	//		paddr, errorcode);

  //get LAPIC register being accessed
  vcpu->lapic_reg = (paddr - vcpu->lapic_base);

  if(errorcode & EPT_ERRORCODE_WRITE){
    //printf("\nCPU(0x%02x): LAPIC[WRITE] reg=0x%08x", vcpu->id,
		//	vcpu->lapic_reg);

		if(vcpu->lapic_reg == LAPIC_ICR_LOW || vcpu->lapic_reg == LAPIC_ICR_HIGH ){
      vcpu->lapic_op = LAPIC_OP_WRITE;

      //change LAPIC physical address in EPT to point to physical address 
			//of memregion_virtual_LAPIC
			emhf_hwpgtbl_setentry(vcpu, vcpu->lapic_base, 
					(u64)__hva2spa__((u32)&memregion_virtual_LAPIC) | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			

    }else{
      vcpu->lapic_op = LAPIC_OP_RSVD;

      //change LAPIC physical address in EPT to point to physical LAPIC
      emhf_hwpgtbl_setentry(vcpu, vcpu->lapic_base, 
					(u64)vcpu->lapic_base | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			
    }    
  }else{
    //printf("\nCPU(0x%02x): LAPIC[READ] reg=0x%08x", vcpu->id,
		//	vcpu->lapic_reg);

    if(vcpu->lapic_reg == LAPIC_ICR_LOW || vcpu->lapic_reg == LAPIC_ICR_HIGH ){
      vcpu->lapic_op = LAPIC_OP_READ;

      //change LAPIC physical address in EPT to point to physical address 
			//of memregion_virtual_LAPIC
			emhf_hwpgtbl_setentry(vcpu, vcpu->lapic_base, 
					(u64)__hva2spa__((u32)&memregion_virtual_LAPIC) | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			

    }else{
      vcpu->lapic_op = LAPIC_OP_RSVD;

      //change LAPIC physical address in EPT to point to physical LAPIC
      emhf_hwpgtbl_setentry(vcpu, vcpu->lapic_base, 
					(u64)vcpu->lapic_base | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			
    }  
  }

  //setup #DB intercept 
	vcpu->vmcs.control_exception_bitmap |= (1UL << 1); //enable INT 1 intercept (#DB fault)
  
	//save guest IF and TF masks
  vcpu->lapic_guest_eflags_tfifmask = (u32)vcpu->vmcs.guest_RFLAGS & ((u32)EFLAGS_IF | (u32)EFLAGS_TF);	

  //set guest TF
	vcpu->vmcs.guest_RFLAGS |= EFLAGS_TF;
	
  //disable interrupts by clearing guest IF on this CPU until we get 
	//control in lapic_access_dbexception after a DB exception
	vcpu->vmcs.guest_RFLAGS &= ~(EFLAGS_IF);
}


//------------------------------------------------------------------------------
//within single-step
//if request was READ, we can get the value read by reading from
//the LAPIC register 
//if request was WRITE, we get the value from reading virtual_LAPIC_vaddr
//to propagate we just write to the physical LAPIC

void lapic_access_dbexception(VCPU *vcpu, struct regs *r){
  u32 delink_lapic_interception=0;
  
  if(vcpu->lapic_op == LAPIC_OP_WRITE){
    u32 src_registeraddress, dst_registeraddress;
    u32 value_tobe_written;
    
    ASSERT( (vcpu->lapic_reg == LAPIC_ICR_LOW) || (vcpu->lapic_reg == LAPIC_ICR_HIGH) );
   
    src_registeraddress = (u32)&memregion_virtual_LAPIC + vcpu->lapic_reg;
    dst_registeraddress = (u32)vcpu->lapic_base + vcpu->lapic_reg;
    
    value_tobe_written= *((u32 *)src_registeraddress);
    
    if(vcpu->lapic_reg == LAPIC_ICR_LOW){
      if ( (value_tobe_written & 0x00000F00) == 0x500){
        //this is an INIT IPI, we just void it
        printf("\n0x%04x:0x%08x -> (ICR=0x%08x write) INIT IPI detected and skipped, value=0x%08x", 
          (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP, vcpu->lapic_reg, value_tobe_written);
      }else if( (value_tobe_written & 0x00000F00) == 0x600 ){
        //this is a STARTUP IPI
        u32 icr_value_high = *((u32 *)((u32)&memregion_virtual_LAPIC + (u32)LAPIC_ICR_HIGH));
        printf("\n0x%04x:0x%08x -> (ICR=0x%08x write) STARTUP IPI detected, value=0x%08x", 
          (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP, vcpu->lapic_reg, value_tobe_written);        
				delink_lapic_interception=processSIPI(vcpu, value_tobe_written, icr_value_high);
      }else{
        //neither an INIT or SIPI, just propagate this IPI to physical LAPIC
        *((u32 *)dst_registeraddress) = value_tobe_written;
      }
    }else{
      *((u32 *)dst_registeraddress) = value_tobe_written;
    }
                
  }else if( vcpu->lapic_op == LAPIC_OP_READ){
    u32 src_registeraddress;
    u32 value_read;
    ASSERT( (vcpu->lapic_reg == LAPIC_ICR_LOW) || (vcpu->lapic_reg == LAPIC_ICR_HIGH) );

    src_registeraddress = (u32)&memregion_virtual_LAPIC + vcpu->lapic_reg;
   
    value_read = *((u32 *)src_registeraddress);
  }

fallthrough:  
  //clear #DB intercept 
	vcpu->vmcs.control_exception_bitmap &= ~(1UL << 1); 

  //make LAPIC page inaccessible and flush TLB
  if(delink_lapic_interception){
    printf("\n%s: delinking LAPIC interception since all cores have SIPI", __FUNCTION__);
    emhf_hwpgtbl_setentry(vcpu, vcpu->lapic_base, 
					(u64)vcpu->lapic_base | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			
  }else{
    emhf_hwpgtbl_setentry(vcpu, vcpu->lapic_base, 
					(u64)vcpu->lapic_base);			
	}

  //restore guest IF and TF
  vcpu->vmcs.guest_RFLAGS &= ~(EFLAGS_IF);
  vcpu->vmcs.guest_RFLAGS &= ~(EFLAGS_TF);
  vcpu->vmcs.guest_RFLAGS |= vcpu->lapic_guest_eflags_tfifmask;
}


//---checks if all logical cores have received SIPI
//returns 1 if yes, 0 if no
u32 have_all_cores_recievedSIPI(void){
  u32 i;
  VCPU *vcpu;
  
	//iterate through all logical processors in master-id table
	for(i=0; i < midtable_numentries; i++){
  	vcpu = (VCPU *)midtable[i].vcpu_vaddr_ptr;
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
u32 processSIPI(VCPU *vcpu, u32 icr_low_value, u32 icr_high_value){
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
    for(i=0; i < (int)midtable_numentries; i++){
      if(midtable[i].cpu_lapic_id == dest_lapic_id){
        dest_vcpu = (VCPU *)midtable[i].vcpu_vaddr_ptr;
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
  	printf("\nCPU(0x%02x): Sent SIPI command to AP, should awaken it!");
  }

	if(have_all_cores_recievedSIPI())
		return 1;	//all cores have received SIPI, we can discontinue LAPIC interception
	else
		return 0;	//some cores are still to receive SIPI, continue LAPIC interception  
}










/*
u32 lapic_base=0;
u32 lapic_reg=0;
#define LAPIC_OP_RSVD   (3)
#define LAPIC_OP_READ   (2)
#define LAPIC_OP_WRITE  (1)
u32 lapic_op=LAPIC_OP_RSVD;

//have one 4k buffer
//2. virtual_LAPIC_vaddr  - 4k buffer which is the virtual LAPIC page that
//                        guest reads and writes from/to
extern u32 virtual_LAPIC_base[];

extern MIDTAB *midtable;
extern u32 midtable_numentries;


//--NPT manipulation routines---------------------------------------------------
void npt_changemapping(VCPU *vcpu, u32 dest_paddr, u32 new_paddr, u64 protflags){
	pt_t pts;
	u32 page;
	//printf("\n%s: pts addr=0x%08x, dp=0x%08x, np=0x%08x", __FUNCTION__, vcpu->npt_vaddr_pts,
  //  dest_paddr, new_paddr);
  pts = (pt_t)vcpu->npt_vaddr_pts;

	page=dest_paddr/PAGE_SIZE_4K;
  //printf("\n  page=0x%08x", page);
  pts[page] = pae_make_pte(new_paddr, protflags);
}

//------------------------------------------------------------------------------
static inline void clgi(void){
  __asm__ __volatile__ ("clgi\r\n");
}
static inline void stgi(void){
  __asm__ __volatile__ ("stgi\r\n");
}


//------------------------------------------------------------------------------
//if there is a read request, store the register accessed
//store request as READ
//map npt entry of the physical LAPIC page with lapic_base and single-step
//if there is a write request, map npt entry of physical LAPIC
//page with physical address of virtual_LAPIC page, store the
//register accessed, store request as WRITE and single-step

u32 lapic_access_handler(VCPU *vcpu, u32 paddr, u32 errorcode){
  struct vmcb_struct *vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;
  
  //get LAPIC register being accessed
  lapic_reg = (paddr - lapic_base);

  if(errorcode & PF_ERRORCODE_WRITE){
    if(lapic_reg == LAPIC_ICR_LOW || lapic_reg == LAPIC_ICR_HIGH ){
      lapic_op = LAPIC_OP_WRITE;

      //change LAPIC physical address NPT mapping to point to physical 
      //address of virtual_LAPIC_base
      //printf("\nvirtual_LAPIC_base, v=0x%08x, p=0x%08x",  
      //  (u32)virtual_LAPIC_base, __hva2spa__((u32)virtual_LAPIC_base));
      npt_changemapping(vcpu, lapic_base, __hva2spa__((u32)virtual_LAPIC_base), (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER));
      vmcb->tlb_control = TLB_CONTROL_FLUSHALL;  

    }else{
      lapic_op = LAPIC_OP_RSVD;

      //change LAPIC physical address NPT mapping to point to physical LAPIC
      npt_changemapping(vcpu, lapic_base, lapic_base, (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER));
      vmcb->tlb_control = TLB_CONTROL_FLUSHALL;  
    }    
    
    //setup #DB intercept in vmcb
    vmcb->exception_intercepts |= (u32)EXCEPTION_INTERCEPT_DB;
  
    //set guest TF
    vmcb->rflags |= (u64)EFLAGS_TF;
  
    clgi();
    
  }else{
    //printf("\nREAD from LAPIC register");
    if(lapic_reg == LAPIC_ICR_LOW || lapic_reg == LAPIC_ICR_HIGH ){
      lapic_op = LAPIC_OP_READ;

      //change LAPIC physical address NPT mapping to point to physical 
      //address of virtual_LAPIC_base
      //printf("\nvirtual_LAPIC_base, v=0x%08x, p=0x%08x",  
      //  (u32)virtual_LAPIC_base, __hva2spa__((u32)virtual_LAPIC_base));
      npt_changemapping(vcpu, lapic_base, __hva2spa__((u32)virtual_LAPIC_base), (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER));
      vmcb->tlb_control = TLB_CONTROL_FLUSHALL;  

    }else{

      lapic_op = LAPIC_OP_RSVD;

      //change LAPIC physical address NPT mapping to point to physical LAPIC
      npt_changemapping(vcpu, lapic_base, lapic_base, (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER));
      vmcb->tlb_control = TLB_CONTROL_FLUSHALL;
    }  

    //setup #DB intercept in vmcb
    vmcb->exception_intercepts |= (u32)EXCEPTION_INTERCEPT_DB;
  
    //set guest TF
    vmcb->rflags |= (u64)EFLAGS_TF;

    //disable interrupts on this CPU until we get control in 
    //lapic_access_dbexception after a DB exception
    clgi();
  }
  
}

//---SIPI processing logic------------------------------------------------------
//return 1 if lapic interception has to be discontinued, typically after
//all aps have received their SIPI, else 0
u32 processSIPI(VCPU *vcpu, u32 icr_low_value, u32 icr_high_value){
  //we assume that destination is always physical and 
  //specified via top 8 bits of icr_high_value
  u32 dest_lapic_id;
  VCPU *dest_vcpu = (VCPU *)0;
  
  ASSERT( (icr_low_value & 0x000C0000) == 0x0 );
  
  dest_lapic_id= icr_high_value >> 24;
  
  printf("\n%s: dest_lapic_id is 0x%02x", __FUNCTION__, dest_lapic_id);
  
  //find the vcpu entry of the core with dest_lapic_id
  {
    int i;
    for(i=0; i < (int)midtable_numentries; i++){
      if(midtable[i].cpu_lapic_id == dest_lapic_id){
        dest_vcpu = (VCPU *)midtable[i].vcpu_vaddr_ptr;
        ASSERT( dest_vcpu->id == dest_lapic_id );
        break;        
      }
    }
    
    ASSERT( dest_vcpu != (VCPU *)0 );
  }

  printf("\nfound AP to pass SIPI to; id=0x%02x, vcpu=0x%08x",
      dest_vcpu->id, (u32)dest_vcpu);  
  
  //debug, halt on id=0x2
  //if(dest_vcpu->id == 0x3){
  //  printf("\nonly 2 AP supported as of now!");
  //  HALT();
  //}
  
  //send the sipireceived flag to trigger the AP to start the HVM
  if(dest_vcpu->sipireceived){
    printf("\nDestination CPU #0x%02x has already received SIPI, ignoring", dest_vcpu->id);
    if(dest_vcpu->id == 0x03)
      return 1;
    else
      return 0;
  }
  
  dest_vcpu->sipivector = (u8)icr_low_value;
  dest_vcpu->sipireceived = 1;
  
  printf("\nSent SIPI command to AP, should awaken it!");
  return 0;  
}


//------------------------------------------------------------------------------
//within single-step
//if request was READ, we can get the value read by reading from
//the LAPIC register 
//if request was WRITE, we get the value from reading virtual_LAPIC_vaddr
//to propagate we just write to the physical LAPIC

void lapic_access_dbexception(VCPU *vcpu, struct regs *r){
  struct vmcb_struct *vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;
  u32 delink_lapic_interception=0;
  
  if(lapic_op == LAPIC_OP_WRITE){
    u32 src_registeraddress, dst_registeraddress;
    u32 value_tobe_written;
    
    ASSERT( (lapic_reg == LAPIC_ICR_LOW) || (lapic_reg == LAPIC_ICR_HIGH) );
   
    src_registeraddress = (u32)virtual_LAPIC_base + lapic_reg;
    dst_registeraddress = (u32)lapic_base + lapic_reg;
    
    value_tobe_written= *((u32 *)src_registeraddress);
    
    if(lapic_reg == LAPIC_ICR_LOW){
      if ( (value_tobe_written & 0x00000F00) == 0x500){
        //this is an INIT IPI, we just void it
        printf("\n0x%04x:0x%08x -> (ICR=0x%08x write) INIT IPI detected and skipped, value=0x%08x", 
          (u16)vmcb->cs.sel, (u32)vmcb->rip, lapic_reg, value_tobe_written);
      }else if( (value_tobe_written & 0x00000F00) == 0x600 ){
        //this is a STARTUP IPI
        u32 icr_value_high = *((u32 *)((u32)virtual_LAPIC_base + (u32)LAPIC_ICR_HIGH));
        printf("\n0x%04x:0x%08x -> (ICR=0x%08x write) STARTUP IPI detected, value=0x%08x", 
          (u16)vmcb->cs.sel, (u32)vmcb->rip, lapic_reg, value_tobe_written);
        delink_lapic_interception=processSIPI(vcpu, value_tobe_written, icr_value_high);
      }else{
        //neither an INIT or SIPI, just propagate this IPI to physical LAPIC
        *((u32 *)dst_registeraddress) = value_tobe_written;
      }
    }else{
      *((u32 *)dst_registeraddress) = value_tobe_written;
    }
                
  }else if( lapic_op == LAPIC_OP_READ){
    u32 src_registeraddress;
    u32 value_read;
    ASSERT( (lapic_reg == LAPIC_ICR_LOW) || (lapic_reg == LAPIC_ICR_HIGH) );

    src_registeraddress = (u32)virtual_LAPIC_base + lapic_reg;
   
    value_read = *((u32 *)src_registeraddress);
    //printf("\n0x%04x:0x%08x -> (ICR=0x%08x read), value=0x%08x", 
    //  (u16)vmcb->cs.sel, (u32)vmcb->rip, lapic_reg, value_read);
  }

fallthrough:  
  //clear #DB intercept in VMCB
  vmcb->exception_intercepts &= ~(u32)EXCEPTION_INTERCEPT_DB;
  
  //clear guest TF
  vmcb->rflags &= ~(u64)EFLAGS_TF;
  
  
  //make LAPIC page inaccessible and flush TLB
  if(delink_lapic_interception){
    printf("\n%s: delinking LAPIC interception since all cores have SIPI", __FUNCTION__);
    npt_changemapping(vcpu, lapic_base, lapic_base, (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER));
	  vmcb->tlb_control = TLB_CONTROL_FLUSHALL;
  }else{
    npt_changemapping(vcpu, lapic_base, lapic_base, 0);
	  vmcb->tlb_control = TLB_CONTROL_FLUSHALL;
	}
  
  //enable interrupts on this CPU
  stgi();
}



void apic_setup(VCPU *vcpu){
  u32 eax, edx;
  struct vmcb_struct *vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;
  
  //read APIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  ASSERT( edx == 0 ); //APIC is below 4G
  lapic_base = eax & 0xFFFFF000UL;
  printf("\nBSP(0x%02x): Local APIC base=0x%08x", vcpu->id, lapic_base);
  
  //set physical 4K page of APIC base address to not-present
  //this will cause NPF on access to the APIC page which is then
  //handled by lapic_access_handler
  npt_changemapping(vcpu, lapic_base, lapic_base, 0);
  vmcb->tlb_control = TLB_CONTROL_FLUSHALL;  
}
*/