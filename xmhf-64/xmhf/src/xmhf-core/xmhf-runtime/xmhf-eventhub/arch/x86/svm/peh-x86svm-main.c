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
  xmhf_smpguest_arch_x86svm_quiesce(vcpu);
  app_ret_status=xmhf_app_handleintercept_portaccess(vcpu, r, ioinfo.fields.port, access_type,
          access_size);
  xmhf_smpguest_arch_x86svm_endquiesce(vcpu);


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
  HALT_ON_ERRORCOND( (vmcb->exitinfo1 == 0) || (vmcb->exitinfo1 == 1) );
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
    HALT_ON_ERRORCOND( vcpu->isbsp == 1); //only BSP gets a NPF during LAPIC SIPI detection
    xmhf_smpguest_arch_x86_eventhandler_hwpgtblviolation(vcpu, gpa, errorcode);
  } else {
	//note: AMD does not provide guest virtual address on a #NPF so we pass zero always
	xmhf_smpguest_arch_x86svm_quiesce(vcpu);
	xmhf_app_handleintercept_hwpgtblviolation(vcpu, r, gpa, 0, errorcode);
	xmhf_smpguest_arch_x86svm_endquiesce(vcpu);
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

	//if in V86 mode translate the virtual address to physical address
	if( (vmcb->cr0 & CR0_PE) && (vmcb->cr0 & CR0_PG) &&
			(vmcb->rflags & EFLAGS_VM) ){
		u8 *bdamemoryphysical;
		#ifdef __XMHF_VERIFICATION__
			bdamemoryphysical = (u8 *)nondet_u32();
		#else
			bdamemoryphysical = (u8 *)xmhf_smpguest_arch_x86svm_walk_pagetables(vcpu, (hva_t)bdamemory);
		#endif
		if((sla_t)bdamemoryphysical < rpb->XtVmmRuntimePhysBase){
			printf("\nINT15 (E820): V86 mode, bdamemory translated from %08lx to %08lx",
				(hva_t)bdamemory, (sla_t)bdamemoryphysical);
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

		//HALT_ON_ERRORCOND(r->edx == 0x534D4150UL);  //'SMAP' should be specified by guest
		//HALT_ON_ERRORCOND(r->ebx < rpb->XtVmmE820NumEntries); //invalid continuation value specified by guest!
		if( (r->edx == 0x534D4150UL) && (r->ebx < rpb->XtVmmE820NumEntries) ){

			//copy the e820 descriptor and return its size in ECX
			{

				if(((u32)((vmcb->es.base)+(u16)r->edi)) < rpb->XtVmmRuntimePhysBase){
					#ifdef __XMHF_VERIFICATION__
						GRUBE820 pe820entry;
						pe820entry.baseaddr_low = g_e820map[r->ebx].baseaddr_low;
						pe820entry.baseaddr_high = g_e820map[r->ebx].baseaddr_high;
						pe820entry.length_low = g_e820map[r->ebx].length_low;
						pe820entry.length_high = g_e820map[r->ebx].length_high;
						pe820entry.type = g_e820map[r->ebx].type;
					#else
						GRUBE820 *pe820entry;
						pe820entry = (GRUBE820 *)((hva_t)((vmcb->es.base)+(u16)r->edi));

						pe820entry->baseaddr_low = g_e820map[r->ebx].baseaddr_low;
						pe820entry->baseaddr_high = g_e820map[r->ebx].baseaddr_high;
						pe820entry->length_low = g_e820map[r->ebx].length_low;
						pe820entry->length_high = g_e820map[r->ebx].length_high;
						pe820entry->type = g_e820map[r->ebx].type;
					#endif //__XMHF_VERIFICATION__
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
				//u16 guest_cs, guest_ip, guest_flags;
				u16 guest_cs __attribute__((unused)), guest_ip __attribute__((unused)), guest_flags;
				u16 *gueststackregion = (u16 *)( (hva_t)vmcb->ss.base + (u16)vmcb->rsp );


				//if V86 mode translate the virtual address to physical address
				if( (vmcb->cr0 & CR0_PE) && (vmcb->cr0 & CR0_PG) &&
					(vmcb->rflags & EFLAGS_VM) ){
					#ifdef __XMHF_VERIFICATION__
						u8 *gueststackregionphysical = (u8 *)nondet_u32();
					#else
						u8 *gueststackregionphysical = (u8 *)xmhf_smpguest_arch_x86svm_walk_pagetables(vcpu, (hva_t)gueststackregion);
					#endif
					if((sla_t)gueststackregionphysical < rpb->XtVmmRuntimePhysBase){
						printf("\nINT15 (E820): V86 mode, gueststackregion translated from %08x to %08x",
							(hva_t)gueststackregion, (sla_t)gueststackregionphysical);
						gueststackregion = (u16 *)gueststackregionphysical;
					}else{
						printf("\nCPU(0x%02x): INT15 (E820) V86 mode, translated gueststackregion points beyond \
							guest physical memory space. Halting!", vcpu->id);
						HALT();
					}
				}

				//get guest IP, CS and FLAGS from the IRET frame
				#ifdef __XMHF_VERIFICATION__
					guest_ip = nondet_u16();
					guest_cs = nondet_u16();
					guest_flags = nondet_u16();
				#else
					guest_ip = gueststackregion[0];
					guest_cs = gueststackregion[1];
					guest_flags = gueststackregion[2];
				#endif	//__XMHF_VERIFICATION__

				//increment e820 descriptor continuation value
				r->ebx=r->ebx+1;

				if(r->ebx > (rpb->XtVmmE820NumEntries-1) ){
					//we have reached the last record, so set CF and make EBX=0
					r->ebx=0;
					guest_flags |= (u16)EFLAGS_CF;
					#ifndef __XMHF_VERIFICATION__
						gueststackregion[2] = guest_flags;
					#endif
				}else{
					//we still have more records, so clear CF
					guest_flags &= ~(u16)EFLAGS_CF;
					#ifndef __XMHF_VERIFICATION__
						gueststackregion[2] = guest_flags;
					#endif
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

#ifdef __XMHF_VERIFICATION__
	//get IP and CS of the original INT 15h handler
	ip = nondet_u16();
	cs = nondet_u16();
#else
	//get IP and CS of the original INT 15h handler
	ip = *((u16 *)((hva_t)bdamemory + 4));
	cs = *((u16 *)((hva_t)bdamemory + 6));
#endif

	//update VMCB with the CS and IP and let go
	vmcb->rip = ip;
	vmcb->cs.base = cs * 16;
	vmcb->cs.selector = cs;
}



//---SVM intercept handler hub--------------------------------------------------
u32 xmhf_parteventhub_arch_x86svm_intercept_handler(VCPU *vcpu, struct regs *r){
  struct _svm_vmcbfields *vmcb = (struct _svm_vmcbfields *)vcpu->vmcb_vaddr_ptr;

  vmcb->tlb_control = VMCB_TLB_CONTROL_NOTHING;

	//handle intercepts
	switch(vmcb->exitcode){

		//--------------------------------------------------------------
		//xmhf-core and hypapp intercepts
		//--------------------------------------------------------------

		case SVM_VMEXIT_VMMCALL:{
			//check to see if this is a hypercall for INT 15h hooking
			if(vmcb->cs.base == (VMX_UG_E820HOOK_CS << 4) &&
				vmcb->rip == VMX_UG_E820HOOK_IP){
				//we need to be either in real-mode or in protected
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
				xmhf_smpguest_arch_x86svm_quiesce(vcpu);
				if( xmhf_app_handlehypercall(vcpu, r) != APP_SUCCESS){
					printf("\nCPU(0x%02x): error(halt), unhandled hypercall 0x%08x!", vcpu->id, r->eax);
					HALT();
				}
				xmhf_smpguest_arch_x86svm_endquiesce(vcpu);
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
			printf("\n***** INIT xmhf_app_handleshutdown\n");
			xmhf_app_handleshutdown(vcpu, r);
			printf("\nCPU(0x%02x): Fatal, xmhf_app_handleshutdown returned. Halting!", vcpu->id);
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
				xmhf_smpguest_arch_x86_eventhandler_dbexception(vcpu, r);
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


#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
	{
		//ensure that whenever a partition is resumed on a vcpu, we have nested paging
		//enabled and that the base points to the nested page tables we have initialized
		assert( (vmcb->np_enable == 1) );
		assert( (vmcb->n_cr3 == vcpu->npt_vaddr_ptr) );
	}
#endif

	return 0;
}
