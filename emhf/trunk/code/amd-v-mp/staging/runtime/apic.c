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

// apic.c - APIC virtualization support
// author: amit vasudevan (amitvasudevan@acm.org)
#include <target.h>
#include <globals.h>

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
    for(i=0; i < (int)g_runtime.midtable_numentries; i++){
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
