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

// peh-x86svm-main.c
// EMHF partition event-hub for AMD x86 svm
// author: amit vasudevan (amitvasudevan@acm.org)
#include <xmhf.h> 


//---IO Intercept handling------------------------------------------------------
static void _svm_handle_ioio(VCPU *vcpu, struct _svm_vmcbfields *vmcb, struct regs __attribute__((unused)) *r){
  union svmioiointerceptinfo ioinfo;
  u32 app_ret_status = APP_IOINTERCEPT_CHAIN;
  u32 access_size, access_type;

  ioinfo.rawbits = vmcb->exitinfo1;
  
  if (ioinfo.fields.rep || ioinfo.fields.str){
    printf("\nCPU(0x%02x): Fatal, unsupported batch I/O ops!", vcpu->id);
    HALT();
  }

  if(ioinfo.fields.type)
	access_type = IO_TYPE_IN;
  else
	access_type = IO_TYPE_OUT;
	
  if(ioinfo.fields.sz8)
	access_size = IO_SIZE_BYTE;
  else if(ioinfo.fields.sz16)
	access_size = IO_SIZE_WORD;
  else
	access_size = IO_SIZE_DWORD;
	
	//call our app handler
	emhf_smpguest_arch_x86svm_quiesce(vcpu);
	app_ret_status=emhf_app_handleintercept_portaccess(vcpu, r, ioinfo.fields.port, access_type, 
          access_size);
    emhf_smpguest_arch_x86svm_endquiesce(vcpu);
	
  
  if(app_ret_status == APP_IOINTERCEPT_CHAIN){
	  if (ioinfo.fields.type){
		// IN 
		if (ioinfo.fields.sz8){
			vmcb->rax &= ~(u64)0x00000000000000FF;
			vmcb->rax |= (u8)inb(ioinfo.fields.port);
		  //*(u8 *)&vmcb->rax = inb(ioinfo.fields.port);
		}else if (ioinfo.fields.sz16){
			vmcb->rax &= ~(u64)0x000000000000FFFF;
			vmcb->rax |= (u16)inw(ioinfo.fields.port);
		  //*(u16 *)&vmcb->rax = inw(ioinfo.fields.port);
		}else if (ioinfo.fields.sz32){ 
			vmcb->rax &= ~(u64)0x00000000FFFFFFFF;
			vmcb->rax |= (u32)inl(ioinfo.fields.port);
		   //*(u32 *)&vmcb->rax = inl(ioinfo.fields.port);
		}else{
		   //h/w should set sz8, sz16 or sz32, we get here if there
		   //is a non-complaint CPU
		   printf("\nnon-complaint CPU (ioio intercept). Halting!");
		   HALT();
		}
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
  }else{
      //skip the IO instruction, app has taken care of it
	  vmcb->rip = vmcb->exitinfo2;
  }
  
  
}


//---MSR intercept handling-----------------------------------------------------
static void _svm_handle_msr(VCPU *vcpu, struct _svm_vmcbfields *vmcb, struct regs *r){
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
  struct _svm_vmcbfields *vmcb = (struct _svm_vmcbfields *)vcpu->vmcb_vaddr_ptr;
  u32 gpa = vmcb->exitinfo2;
  u32 errorcode = vmcb->exitinfo1;
  
  if(gpa >= g_svm_lapic_base && gpa < (g_svm_lapic_base + PAGE_SIZE_4K)){
    //LAPIC access, xfer control to apropriate handler
    //printf("\n0x%04x:0x%08x -> LAPIC access, gpa=0x%08x, errorcode=0x%08x", 
    //  (u16)vmcb->cs.sel, (u32)vmcb->rip, gpa, errorcode);
    ASSERT( vcpu->isbsp == 1); //only BSP gets a NPF during LAPIC SIPI detection
    //svm_lapic_access_handler(vcpu, gpa, errorcode);
    emhf_smpguest_arch_x86_eventhandler_hwpgtblviolation(vcpu, gpa, errorcode);
    //HALT();
  } else {
	//note: AMD does not provide guest virtual address on a #NPF
	//so we pass zero always
	// call EMHF app hook
	emhf_smpguest_arch_x86svm_quiesce(vcpu);
	emhf_app_handleintercept_hwpgtblviolation(vcpu, r, gpa, 0, errorcode);
	emhf_smpguest_arch_x86svm_endquiesce(vcpu);
  }
  
  return;
}


//---NMI handling---------------------------------------------------------------
// note: we use NMI for core quiescing, we simply inject the others back
// into the guest in the normal case
static void _svm_handle_nmi(VCPU *vcpu, struct _svm_vmcbfields __attribute__((unused)) *vmcb, struct regs __attribute__((unused)) *r){
    //now we adopt a simple trick, this NMI is pending, the only
    //way we can dismiss it is if we set GIF=0 and make GIF=1 so that
    //the core thinks it must dispatch the pending NMI :p
    (void)vcpu;
    
    //printf("\nCPU(0x%02x): triggering local NMI in CPU...", vcpu->id);
    
    __asm__ __volatile__("clgi\r\n");
    __asm__ __volatile__("stgi\r\n"); //at this point we get control in
                                      //our exception handler which handles the rest
    //printf("\nCPU(0x%02x): resuming guest...", vcpu->id);
}


//---svm int 15 intercept handler-----------------------------------------------
static void _svm_int15_handleintercept(VCPU *vcpu, struct regs *r){
	u16 cs, ip;
	u8 *bdamemory = (u8 *)0x4AC;
	struct _svm_vmcbfields *vmcb = (struct _svm_vmcbfields *)vcpu->vmcb_vaddr_ptr;

	//printf("\nCPU(0x%02x): BDA dump in intercept: %02x %02x %02x %02x %02x %02x %02x %02x", vcpu->id,
	//		bdamemory[0], bdamemory[1], bdamemory[2], bdamemory[3], bdamemory[4],
	//			bdamemory[5], bdamemory[6], bdamemory[7]);

	//if in V86 mode translate the virtual address to physical address
	if( (vmcb->cr0 & CR0_PE) && (vmcb->cr0 & CR0_PG) &&
			(vmcb->rflags & EFLAGS_VM) ){
		u8 *bdamemoryphysical;
		bdamemoryphysical = (u8 *)emhf_smpguest_arch_x86svm_walk_pagetables(vcpu, (u32)bdamemory);
		if((u32)bdamemoryphysical < rpb->XtVmmRuntimePhysBase){
			printf("\nINT15 (E820): V86 mode, bdamemory translated from %08x to %08x",
				(u32)bdamemory, (u32)bdamemoryphysical);
			bdamemory = bdamemoryphysical; 		
		}else{
			printf("\nCPU(0x%02x): INT15 (E820) V86 mode, translated bdamemory points beyond \
				guest physical memory space. Halting!", vcpu->id);
			HALT();
		}
	}


	//if E820 service then...
	if((u16)vmcb->rax == 0xE820){
		//AX=0xE820, EBX=continuation value, 0 for first call
		//ES:DI pointer to buffer, ECX=buffer size, EDX='SMAP'
		//return value, CF=0 indicated no error, EAX='SMAP'
		//ES:DI left untouched, ECX=size returned, EBX=next continuation value
		//EBX=0 if last descriptor
		printf("\nCPU(0x%02x): INT 15(e820): AX=0x%04x, EDX=0x%08x, EBX=0x%08x, ECX=0x%08x, ES=0x%04x, DI=0x%04x", vcpu->id, 
		(u16)vmcb->rax, r->edx, r->ebx, r->ecx, (u16)vmcb->es.selector, (u16)r->edi);
		
		//ASSERT(r->edx == 0x534D4150UL);  //'SMAP' should be specified by guest
		//ASSERT(r->ebx < rpb->XtVmmE820NumEntries); //invalid continuation value specified by guest!
		if( (r->edx == 0x534D4150UL) && (r->ebx < rpb->XtVmmE820NumEntries) ){
			
			//copy the e820 descriptor and return its size in ECX
			{
				
				if(((u32)((vmcb->es.base)+(u16)r->edi)) < rpb->XtVmmRuntimePhysBase){
						GRUBE820 *pe820entry;
						pe820entry = (GRUBE820 *)((u32)((vmcb->es.base)+(u16)r->edi));
					
						pe820entry->baseaddr_low = g_e820map[r->ebx].baseaddr_low;
						pe820entry->baseaddr_high = g_e820map[r->ebx].baseaddr_high;
						pe820entry->length_low = g_e820map[r->ebx].length_low;
						pe820entry->length_high = g_e820map[r->ebx].length_high;
						pe820entry->type = g_e820map[r->ebx].type;
					
						//memcpy((void *)((u32)((vmcb->es.base)+(u16)r->edi)), (void *)&g_e820map[r->ebx],
						//		sizeof(GRUBE820));
				}else{
						printf("\nCPU(0x%02x): INT15 E820. Guest buffer is beyond guest \
							physical memory bounds. Halting!", vcpu->id);
						HALT();
				}
						
			}
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
					u8 *gueststackregionphysical = (u8 *)emhf_smpguest_arch_x86svm_walk_pagetables(vcpu, (u32)gueststackregion);
					if((u32)gueststackregionphysical < rpb->XtVmmRuntimePhysBase){
						printf("\nINT15 (E820): V86 mode, gueststackregion translated from %08x to %08x",
							(u32)gueststackregion, (u32)gueststackregionphysical);
						gueststackregion = (u16 *)gueststackregionphysical; 		
					}else{
						printf("\nCPU(0x%02x): INT15 (E820) V86 mode, translated gueststackregion points beyond \
							guest physical memory space. Halting!", vcpu->id);
						HALT();
					}
				}
			
				
				//printf("\nINT15 (E820): guest_ss=%04x, sp=%04x, stackregion=%08x", (u16)vcpu->vmcs.guest_SS_selector,
				//		(u16)vcpu->vmcs.guest_RSP, (u32)gueststackregion);
				
				//get guest IP, CS and FLAGS from the IRET frame
					guest_ip = gueststackregion[0];
					guest_cs = gueststackregion[1];
					guest_flags = gueststackregion[2];

				(void)guest_cs;
				(void)guest_ip;
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
			
		}else{	//invalid state specified during INT 15 E820, fail by
				//setting carry flag
				printf("\nCPU(0x%02x): INT15 (E820), invalid state specified by guest \
						Halting!", vcpu->id);
				HALT();
		}
		
		//update RIP to execute the IRET following the VMCALL instruction
		//effectively returning from the INT 15 call made by the guest
		vmcb->rip += 3;

		return;
	} //E820 service
	
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
	vmcb->cs.selector = cs;		 
}


//---SVM intercept handler hub--------------------------------------------------
u32 emhf_parteventhub_arch_x86svm_intercept_handler(VCPU *vcpu, struct regs *r){
  struct _svm_vmcbfields *vmcb = (struct _svm_vmcbfields *)vcpu->vmcb_vaddr_ptr;
  
  vmcb->tlb_control = VMCB_TLB_CONTROL_NOTHING;

	/*//check APIC timer local vector table entry
	{
	  volatile u32 *tlvt = (u32 *)(0xFEE00000 + 0x320);
	  u32 mt = (*tlvt & 0x00000700) >> 8;
	  u32 mask = (*tlvt & 0x00010000) >> 16;
	  u32 tmm = (*tlvt & 0x00020000) >> 17;
	  if(mask == 0){
		printf("\n%s[%02x]: APIC TIMER mode with NMI detected %u %u %u", __FUNCTION__, vcpu->id,mt,mask,tmm);
		HALT();
	  
	  }
	
	}*/


	//handle intercepts
	switch(vmcb->exitcode){
		
		//--------------------------------------------------------------
		//xmhf-core and hypapp intercepts
		//--------------------------------------------------------------

		case SVM_VMEXIT_VMMCALL:{
			//check to see if this is a hypercall for INT 15h hooking
			if(vmcb->cs.base == (VMX_UG_E820HOOK_CS << 4) &&
				vmcb->rip == VMX_UG_E820HOOK_IP){
				//assertions, we need to be either in real-mode or in protected
				//mode with paging and EFLAGS.VM bit set (virtual-8086 mode)
				if( !(vmcb->cr0 & CR0_PE)  ||
					( (vmcb->cr0 & CR0_PE) && (vmcb->cr0 & CR0_PG) &&
						(vmcb->rflags & EFLAGS_VM)  ) ){
					_svm_int15_handleintercept(vcpu, r);	
				}else{
						printf("\nCPU(0x%02x): unhandled INT 15h request from protected mode", vcpu->id);
						printf("\nHalting!");
						HALT();
				}
			}else{	//if not E820 hook, give app a chance to handle the hypercall
				emhf_smpguest_arch_x86svm_quiesce(vcpu);
				if( emhf_app_handlehypercall(vcpu, r) != APP_SUCCESS){
					printf("\nCPU(0x%02x): error(halt), unhandled hypercall 0x%08x!", vcpu->id, r->eax);
					HALT();
				}
				emhf_smpguest_arch_x86svm_endquiesce(vcpu);
				vmcb->rip += 3;
			}
		}
		break;
		
		//IO interception
		case SVM_VMEXIT_IOIO:{
			_svm_handle_ioio(vcpu, vmcb, r);
		}
		break;

		//Nested Page Fault (NPF)
		case SVM_VMEXIT_NPF:{
		 _svm_handle_npf(vcpu, r);
		}
		break;

		case SVM_VMEXIT_INIT:{
			printf("\n***** INIT emhf_app_handleshutdown\n");
			emhf_app_handleshutdown(vcpu, r);      
			printf("\nCPU(0x%02x): Fatal, emhf_app_handleshutdown returned. Halting!", vcpu->id);
			HALT();
		}
		break;

		//--------------------------------------------------------------
		//xmhf-core only intercepts
		//--------------------------------------------------------------

		//MSR interception
		case SVM_VMEXIT_MSR:{
		  _svm_handle_msr(vcpu, vmcb, r);
		}
		break;

		case SVM_VMEXIT_EXCEPTION_DB:{
			if(vcpu->isbsp == 1){											//LAPIC SIPI detection only happens on BSP
				emhf_smpguest_arch_x86_eventhandler_dbexception(vcpu, r);
			}else{															//TODO: reflect back to guest
				printf("\nUnexpected DB exception on non-BSP core (0x%02x)", vcpu->id);
				printf("\nHalting!");
				HALT();
			}
		}
		break;

		case SVM_VMEXIT_NMI:{
			_svm_handle_nmi(vcpu, vmcb, r);
		}
		break;

		default:{
			printf("\nUnhandled Intercept:0x%08llx", vmcb->exitcode);
			printf("\n\tCS:EIP=0x%04x:0x%08x", (u16)vmcb->cs.selector, (u32)vmcb->rip);
			printf("\n\tedi:%08x esi:%08x ebp:%08x esp:%08llx",
				r->edi, r->esi, r->ebp, vmcb->rsp);
			printf("\n\tebx:%08x edx:%08x ecx:%08x eax:%08llx",
				r->ebx, r->edx, r->ecx, vmcb->rax);
			printf("\n\tExitInfo1: %llx", vmcb->exitinfo1);
			printf("\n\tExitInfo2: %llx", vmcb->exitinfo2);
			HALT();
		}
	}	//end switch(vmcb->exitcode)	


	return 0;
}
