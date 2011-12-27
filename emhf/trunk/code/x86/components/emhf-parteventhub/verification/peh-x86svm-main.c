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

// peh-x86svm-main.c
// EMHF partition event-hub for AMD x86 svm (verification stub)
// author: amit vasudevan (amitvasudevan@acm.org)
#include <emhf.h> 

//======================================================================
//support functions
u32 svm_isbsp(void){
		return 1;	//assume BSP for now
}

u32 svm_lapic_access_handler(VCPU *vcpu, u32 paddr, u32 errorcode){
		return 0;
}

void svm_lapic_access_dbexception(VCPU *vcpu, struct regs *r){
		return;
}

void *memcpy (void *destaddr, void const *srcaddr, u32 len){
  char *dest = destaddr;
  char const *src = srcaddr;

  while (len-- > 0)
    *dest++ = *src++;
  return destaddr;
}


//======================================================================
//app stubs
u32 emhf_app_handleintercept_hwpgtblviolation(VCPU *vcpu,
      struct regs *r,
      u64 gpa, u64 gva, u64 violationcode){
			return APP_SUCCESS;
}

u32 emhf_app_handlehypercall(VCPU *vcpu, struct regs *r){
	u32 status=APP_SUCCESS;
	u32 call_id= (u32)r->eax;

   switch(call_id){
		case 0xDEADBEEF:
			//r->ebx contains a 32-bit number that needs to be printed out
			printf("\nCPU(0x%02x): Our hypercall", vcpu->id);
			break;
		
		default:
			printf("\nCPU(0x%02x): unsupported hypercall (0x%08x)!!", 
			  vcpu->id, call_id);
			status=APP_ERROR;
			break;
	}

	return status;			
}

/*
//---IO Intercept handling------------------------------------------------------
static void _svm_handle_ioio(VCPU *vcpu, struct vmcb_struct *vmcb, struct regs __attribute__((unused)) *r){
  ioio_info_t ioinfo;
  
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
static void _svm_handle_msr(VCPU *vcpu, struct vmcb_struct *vmcb, struct regs *r){
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


//invoked on a nested page-fault 
//struct regs *r -> guest OS GPR state
//win_vmcb	-> rest of the guest OS state
//win_vmcb->exitinfo1 = error code similar to PF
//win_vmcb->exitinfo2 = faulting guest OS physical address
static void _svm_handle_npf(VCPU *vcpu, struct regs *r){
  struct vmcb_struct *vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;
  u32 gpa = vmcb->exitinfo2;
  u32 errorcode = vmcb->exitinfo1;
  
  if(gpa >= g_svm_lapic_base && gpa < (g_svm_lapic_base + PAGE_SIZE_4K)){
    //LAPIC access, xfer control to apropriate handler
    //printf("\n0x%04x:0x%08x -> LAPIC access, gpa=0x%08x, errorcode=0x%08x", 
    //  (u16)vmcb->cs.sel, (u32)vmcb->rip, gpa, errorcode);
    ASSERT( svm_isbsp() == 1); //only BSP gets a NPF during LAPIC SIPI detection
    svm_lapic_access_handler(vcpu, gpa, errorcode);
    //HALT();
  } else {
	// call EMHF app hook
	emhf_app_handleintercept_hwpgtblviolation(vcpu, r, gpa, 0, errorcode);
  }
  
  return;
}


//---NMI handling---------------------------------------------------------------
// note: we use NMI for core quiescing, we simply inject the others back
// into the guest in the normal case
static void _svm_handle_nmi(VCPU *vcpu, struct vmcb_struct __attribute__((unused)) *vmcb, struct regs __attribute__((unused)) *r){
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


//---svm int 15 intercept handler-----------------------------------------------
static void _svm_int15_handleintercept(VCPU *vcpu, struct regs *r){
	u16 cs, ip;
	u8 *bdamemory = (u8 *)0x4AC;
	struct vmcb_struct *vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;
	
	//printf("\nCPU(0x%02x): BDA dump in intercept: %02x %02x %02x %02x %02x %02x %02x %02x", vcpu->id,
	//		bdamemory[0], bdamemory[1], bdamemory[2], bdamemory[3], bdamemory[4],
	//			bdamemory[5], bdamemory[6], bdamemory[7]);

	//if in V86 mode translate the virtual address to physical address
	if( (vmcb->cr0 & CR0_PE) && (vmcb->cr0 & CR0_PG) &&
			(vmcb->rflags & EFLAGS_VM) ){
		u8 *bdamemoryphysical;
		//bdamemoryphysical = (u8 *)_svm_lib_guestpgtbl_walk(vcpu, (u32)bdamemory);
		bdamemoryphysical = (u8 *)0x4AC;
		ASSERT( (u32)bdamemoryphysical != 0xFFFFFFFFUL );
		printf("\nINT15 (E820): V86 mode, bdamemory translated from %08x to %08x",
			(u32)bdamemory, (u32)bdamemoryphysical);
		bdamemory = bdamemoryphysical; 		
	}
	
	//if E820 service then...
	if((u16)vmcb->rax == 0xE820){
		//AX=0xE820, EBX=continuation value, 0 for first call
		//ES:DI pointer to buffer, ECX=buffer size, EDX='SMAP'
		//return value, CF=0 indicated no error, EAX='SMAP'
		//ES:DI left untouched, ECX=size returned, EBX=next continuation value
		//EBX=0 if last descriptor
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
		
		{
			u16 guest_cs, guest_ip, guest_flags;
			u16 *gueststackregion = (u16 *)( (u32)vmcb->ss.base + (u16)vmcb->rsp );
		
		
			//if V86 mode translate the virtual address to physical address
			if( (vmcb->cr0 & CR0_PE) && (vmcb->cr0 & CR0_PG) &&
				(vmcb->rflags & EFLAGS_VM) ){
				//u8 *gueststackregionphysical = (u8 *)_svm_lib_guestpgtbl_walk(vcpu, (u32)gueststackregion);
				//XXX: FIXME
				u8 *gueststackregionphysical = (u8 *)0x10000;
				ASSERT( (u32)gueststackregionphysical != 0xFFFFFFFFUL );
				printf("\nINT15 (E820): V86 mode, gueststackregion translated from %08x to %08x",
					(u32)gueststackregion, (u32)gueststackregionphysical);
				gueststackregion = (u16 *)gueststackregionphysical; 		
			}
		
			
			//printf("\nINT15 (E820): guest_ss=%04x, sp=%04x, stackregion=%08x", (u16)vcpu->vmcs.guest_SS_selector,
			//		(u16)vcpu->vmcs.guest_RSP, (u32)gueststackregion);
			
			//get guest IP, CS and FLAGS from the IRET frame
			guest_ip = gueststackregion[0];
			guest_cs = gueststackregion[1];
			guest_flags = gueststackregion[2];

			//printf("\nINT15 (E820): guest_flags=%04x, guest_cs=%04x, guest_ip=%04x",
			//	guest_flags, guest_cs, guest_ip);
		
			//increment e820 descriptor continuation value
			r->ebx=r->ebx+1;
					
			if(r->ebx > (rpb->XtVmmE820NumEntries-1) ){
				//we have reached the last record, so set CF and make EBX=0
				r->ebx=0;
				guest_flags |= (u16)EFLAGS_CF;
				gueststackregion[2] = guest_flags;
			}else{
				//we still have more records, so clear CF
				guest_flags &= ~(u16)EFLAGS_CF;
				gueststackregion[2] = guest_flags;
			}
		  
		}

 	  //update RIP to execute the IRET following the VMCALL instruction
 	  //effectively returning from the INT 15 call made by the guest
	  vmcb->rip += 3;

		return;
	}
	
	
	//ok, this is some other INT 15h service, so simply chain to the original
	//INT 15h handler
	
	//get IP and CS of the original INT 15h handler
	ip = *((u16 *)((u32)bdamemory + 4));
	cs = *((u16 *)((u32)bdamemory + 6));
	
	//printf("\nCPU(0x%02x): INT 15, transferring control to 0x%04x:0x%04x", vcpu->id,
	//	cs, ip);
		
	//update VMCB with the CS and IP and let go
	vmcb->rip = ip;
	vmcb->cs.base = cs * 16;
	vmcb->cs.sel = cs;		 
}*/


//---SVM intercept handler hub--------------------------------------------------
u32 emhf_parteventhub_intercept_handler_x86svm(VCPU *vcpu, struct regs *r){
  struct vmcb_struct *vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;
  
  vmcb->tlb_control = TLB_CONTROL_NOTHING;
    
  switch(vmcb->exitcode){
/*    //IO interception
 		case VMEXIT_IOIO:{
   		_svm_handle_ioio(vcpu, vmcb, r);
   	}
   	break;
  
    //MSR interception
    case VMEXIT_MSR:{
      _svm_handle_msr(vcpu, vmcb, r);
    }
    break;
    
    //this only gets called on BSP
    //case VMEXIT_SWINT:{
		//	_svm_handle_swint(vcpu, vmcb, r);
		//}
		//break;

	  case VMEXIT_NPF:{
			_svm_handle_npf(vcpu, r);
    }
		break;

 		case VMEXIT_EXCEPTION_DB:{
     ASSERT(svm_isbsp() == 1); //LAPIC SIPI detection only happens on BSP
     svm_lapic_access_dbexception(vcpu, r);
     }
     break;


    case VMEXIT_INIT:{
      printf("\nCPU(0x%02x): INIT intercepted, halting.", vcpu->id);
      printf("\nGuest CS:EIP=0x%04x:0x%08x", (u16)vmcb->cs.sel, (u32)vmcb->rip);
      //{
      //u8 *code;
      //u32 paddr;
      //  int i;
      //  paddr= svm_kernel_pt_walker(vmcb, (u32)vmcb->rip); 
      //  code = (u8 *)paddr; 
      //  printf("\nCode physical address=0x%08x\n", (u32)code);
      //  for(i=0; i < 16; i++)
      //    printf("0x%02x ", code[i]);
      //  HALT();
      //}
      HALT();
      
      //initspin:
      //  goto initspin;
    }
    break;*/

    case VMEXIT_VMMCALL:{
			//check to see if this is a hypercall for INT 15h hooking
			if(vmcb->cs.base == (VMX_UG_E820HOOK_CS << 4) &&
				vmcb->rip == VMX_UG_E820HOOK_IP){
				//assertions, we need to be either in real-mode or in protected
				//mode with paging and EFLAGS.VM bit set (virtual-8086 mode)
				ASSERT( !(vmcb->cr0 & CR0_PE)  ||
					( (vmcb->cr0 & CR0_PE) && (vmcb->cr0 & CR0_PG) &&
						(vmcb->rflags & EFLAGS_VM)  ) );
				//_svm_int15_handleintercept(vcpu, r);	
			}else{	//if not E820 hook, give app a chance to handle the hypercall
				if( emhf_app_handlehypercall(vcpu, r) != APP_SUCCESS){
					printf("\nCPU(0x%02x): error(halt), unhandled hypercall 0x%08x!", vcpu->id, r->eax);
					HALT();
				}
      	vmcb->rip += 3;
			}
    }
    break;

/*    case VMEXIT_NMI:{
        _svm_handle_nmi(vcpu, vmcb, r);
      }
      break;*/
    
		default:{
				printf("\nUnhandled Intercept:0x%08llx", vmcb->exitcode);
				printf("\nCS:EIP=0x%04x:0x%08x", (u16)vmcb->cs.sel, (u32)vmcb->rip);
        HALT();
		}
	}	//end switch(vmcb->exitcode)	

	return 0;
}

//----------------------------------------------------------------------
//verification driver function
//invoked using:
//cbmc emhf-memprot.c 
//-I<emhfcore>/trunk/code/libemhfc/include
//-I<emhfcore>/trunk/code/x86/include -D__EMHF_VERIFICATION__ -D__NESTED_PAGING__ 
//--bounds-check --pointer-check
//where <emhfcore> is where the emhf repo is checked out

u32 nondet_u32();

void main() {
	VCPU vcpu; //VCPU variable to identify the physical core
	struct regs r; //General Purporse Register structure
	struct vmcb_struct *vmcb; //AMD VMCB
  

	//set VMCB virtual address to something meaningful
	vcpu.vmcb_vaddr_ptr = 0xC0000000;	
	vmcb = (struct vmcb_struct *)vcpu.vmcb_vaddr_ptr;
	
	//set VMCB event code to indicate a hypercall
	vmcb->exitcode = VMEXIT_VMMCALL;
	
	//invoke the event hub intercept handler (this is where we would
	//land up when the hardware triggers any event within the guest)
	emhf_parteventhub_intercept_handler_x86svm(&vcpu, &r);

}
