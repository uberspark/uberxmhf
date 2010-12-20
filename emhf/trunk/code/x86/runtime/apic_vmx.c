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

// apic_vmx.c - APIC virtualization support for Intel cores
// author: amit vasudevan (amitvasudevan@acm.org)
#include <target.h>
#include <globals.h>


//the LAPIC register that is being accessed during emulation
static u32 g_vmx_lapic_reg __attribute__(( section(".data") )) = 0;

//the LAPIC operation that is being performed during emulation
static u32 g_vmx_lapic_op __attribute__(( section(".data") )) = LAPIC_OP_RSVD;


//---hardware pagetable flush-all routine---------------------------------------
static void emhf_hwpgtbl_flushall(VCPU *vcpu){
  __vmx_invept(VMX_EPT_SINGLE_CONTEXT, 
          (u64)vcpu->vmcs.control_EPT_pointer_full, 
          0);
  __vmx_invvpid(VMX_VPID_EXTENT_SINGLE_CONTEXT, 1, 0);

}

//---hardware pagetable protection manipulation routine-------------------------
static void emhf_hwpgtbl_setprot(VCPU *vcpu, u64 gpa, u64 flags){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
  pt[pfn] &= ~(u64)7; //clear all previous flags
  pt[pfn] |= flags; //set new flags
  //flush the EPT mappings for new protections to take effect
  emhf_hwpgtbl_flushall(vcpu);
}

static void emhf_hwpgtbl_setentry(VCPU *vcpu, u64 gpa, u64 value){
  u32 pfn = (u32)gpa / PAGE_SIZE_4K;
  u64 *pt = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
  pt[pfn] = value; //set new value
  //flush the EPT mappings for new protections to take effect
  emhf_hwpgtbl_flushall(vcpu);
}


static u64 emhf_hwpgtbl_getprot(VCPU *vcpu, u64 gpa){
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
  	printf("\nCPU(0x%02x): Sent SIPI command to AP, should awaken it!");
  }

	if(have_all_cores_recievedSIPI())
		return 1;	//all cores have received SIPI, we can discontinue LAPIC interception
	else
		return 0;	//some cores are still to receive SIPI, continue LAPIC interception  
}


//---VMX APIC setup-------------------------------------------------------------
//this function sets up the EPT for the vcpu core to intercept LAPIC
//accesses.
//NOTE: this function MUST be called only from the BSP and the vcpu
//passed in should also be that of the BSP
void vmx_apic_setup(VCPU *vcpu){
  u32 eax, edx;

	//we should only be called from the BSP
	ASSERT( vmx_isbsp() == 1 );	
  
  //clear virtual LAPIC page
  memset((void *)&g_vmx_virtual_LAPIC_base, 0, PAGE_SIZE_4K);
  
  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  ASSERT( edx == 0 ); //APIC should be below 4G
  g_vmx_lapic_base = eax & 0xFFFFF000UL;
  //printf("\nBSP(0x%02x): LAPIC base=0x%08x", vcpu->id, vcpu->lapic_base);
  
  //set physical 4K page of LAPIC base address to not-present
  //this will cause EPT violation which is then
  //handled by vmx_lapic_access_handler
	emhf_hwpgtbl_setprot(vcpu, vcpu->lapic_base, 0);
}


//------------------------------------------------------------------------------
//if there is a read request, store the register accessed
//store request as READ
//map npt entry of the physical LAPIC page with lapic_base and single-step
//if there is a write request, map npt entry of physical LAPIC
//page with physical address of virtual_LAPIC page, store the
//register accessed, store request as WRITE and single-step

u32 vmx_lapic_access_handler(VCPU *vcpu, u32 paddr, u32 errorcode){
	//printf("\nCPU(0x%02x): LAPIC: p=0x%08x, ecode=0x%08x", vcpu->id,
	//		paddr, errorcode);

  //get LAPIC register being accessed
  g_vmx_lapic_reg = (paddr - g_vmx_lapic_base);

  if(errorcode & EPT_ERRORCODE_WRITE){
    //printf("\nCPU(0x%02x): LAPIC[WRITE] reg=0x%08x", vcpu->id,
		//	vcpu->lapic_reg);

		if(g_vmx_lapic_reg == LAPIC_ICR_LOW || g_vmx_lapic_reg == LAPIC_ICR_HIGH ){
      g_vmx_lapic_op = LAPIC_OP_WRITE;

      //change LAPIC physical address in EPT to point to physical address 
			//of memregion_virtual_LAPIC
			emhf_hwpgtbl_setentry(vcpu, g_vmx_lapic_base, 
					(u64)__hva2spa__((u32)&g_vmx_virtual_LAPIC_base) | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			

    }else{
      g_vmx_lapic_op = LAPIC_OP_RSVD;

      //change LAPIC physical address in EPT to point to physical LAPIC
      emhf_hwpgtbl_setentry(vcpu, g_vmx_lapic_base, 
					(u64)g_vmx_lapic_base | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			
    }    
  }else{
    //printf("\nCPU(0x%02x): LAPIC[READ] reg=0x%08x", vcpu->id,
		//	vcpu->lapic_reg);

    if(g_vmx_lapic_reg == LAPIC_ICR_LOW || g_vmx_lapic_reg == LAPIC_ICR_HIGH ){
      g_vmx_lapic_op = LAPIC_OP_READ;

      //change LAPIC physical address in EPT to point to physical address 
			//of memregion_virtual_LAPIC
			emhf_hwpgtbl_setentry(vcpu, g_vmx_lapic_base, 
					(u64)__hva2spa__((u32)&g_vmx_virtual_LAPIC_base) | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			

    }else{
      g_vmx_lapic_op = LAPIC_OP_RSVD;

      //change LAPIC physical address in EPT to point to physical LAPIC
      emhf_hwpgtbl_setentry(vcpu, g_vmx_lapic_base, 
					(u64)g_vmx_lapic_base | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			
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

void vmx_lapic_access_dbexception(VCPU *vcpu, struct regs *r){
  u32 delink_lapic_interception=0;
  
  if(vcpu->lapic_op == LAPIC_OP_WRITE){
    u32 src_registeraddress, dst_registeraddress;
    u32 value_tobe_written;
    
    ASSERT( (vcpu->lapic_reg == LAPIC_ICR_LOW) || (vcpu->lapic_reg == LAPIC_ICR_HIGH) );
   
    src_registeraddress = (u32)&g_vmx_virtual_LAPIC_base + vcpu->lapic_reg;
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

fallthrough:  
  //clear #DB intercept 
	vcpu->vmcs.control_exception_bitmap &= ~(1UL << 1); 

  //make LAPIC page inaccessible and flush TLB
  if(delink_lapic_interception){
    printf("\n%s: delinking LAPIC interception since all cores have SIPI", __FUNCTION__);
    emhf_hwpgtbl_setentry(vcpu, g_vmx_lapic_base, 
					(u64)g_vmx_lapic_base | (u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE);			
  }else{
    emhf_hwpgtbl_setentry(vcpu, g_vmx_lapic_base, 
					(u64)g_vmx_lapic_base);			
	}

  //restore guest IF and TF
  vcpu->vmcs.guest_RFLAGS &= ~(EFLAGS_IF);
  vcpu->vmcs.guest_RFLAGS &= ~(EFLAGS_TF);
  vcpu->vmcs.guest_RFLAGS |= vcpu->lapic_guest_eflags_tfifmask;
}


//---apic_wakeupAPs-------------------------------------------------------------
//wake up APs using the LAPIC by sending the INIT-SIPI-SIPI IPI sequence
void vmx_apic_wakeupAPs(void){
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
  udelay(10000);
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
      udelay(200);
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

