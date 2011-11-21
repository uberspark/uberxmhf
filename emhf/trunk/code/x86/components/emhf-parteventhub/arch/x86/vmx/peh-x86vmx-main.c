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

// peh-x86vmx-main.c
// EMHF partition event-hub for Intel x86 vmx
// author: amit vasudevan (amitvasudevan@acm.org)
#include <emhf.h> 

//---hvm_intercept_handler------------------------------------------------------
u32 vmx_intercept_handler(VCPU *vcpu, struct regs *r){
  //read VMCS from physical CPU/core
	_vmx_getVMCS(vcpu);

	//sanity check for VM-entry errors
	if( (u32)vcpu->vmcs.info_vmexit_reason & 0x80000000UL ){
		printf("\nVM-ENTRY error: reason=0x%08x, qualification=0x%016llx", 
			(u32)vcpu->vmcs.info_vmexit_reason, (u64)vcpu->vmcs.info_exit_qualification);
    _vmx_dumpVMCS(vcpu);
    HALT();
  }
  
  //handle intercepts
  switch((u32)vcpu->vmcs.info_vmexit_reason){
		case VMEXIT_IOIO:
			{
				_vmx_handle_intercept_ioportaccess(vcpu, r);
			}
			break;

      case VMEXIT_EPT_VIOLATION:{
		    _vmx_handle_intercept_eptviolation(vcpu, r);
    	}
			break;  	

    case VMEXIT_HLT:
			if(!vcpu->vmx_guest_unrestricted){
				//isl_handleintercept_hlt(vcpu, r);
				printf("\nCPU(0x%02x): V86 monitor based real-mode exec. unsupported!", vcpu->id);
				HALT();
			}else{
			 	printf("\nCPU(0x%02x): Unexpected HLT intercept in UG, Halting!", vcpu->id);
				HALT();
			}
			break;

 		case VMEXIT_EXCEPTION:{
			switch( ((u32)vcpu->vmcs.info_vmexit_interrupt_information & INTR_INFO_VECTOR_MASK) ){
				//case 0x0D: //v86monitor only
				//	_vmx_handle_intercept_exception_0D(vcpu, r);
				//	break;

				case 0x01:
					vmx_lapic_access_dbexception(vcpu, r);
					break;				
				
				case 0x02:	//NMI
					vcpu->nmiinhvm=1;	//this NMI occured when the core was in guest (HVM)
					_vmx_processNMI(vcpu, r);
					vcpu->nmiinhvm=0;
					break;
				
				default:
					printf("\nVMEXIT-EXCEPTION:");
					printf("\ncontrol_exception_bitmap=0x%08lx",
						(unsigned long)vcpu->vmcs.control_exception_bitmap);
					printf("\ninterruption information=0x%08lx", 
						(unsigned long)vcpu->vmcs.info_vmexit_interrupt_information);
					printf("\nerrorcode=0x%08lx", 
						(unsigned long)vcpu->vmcs.info_vmexit_interrupt_error_code);
					HALT();
			}
		}
		break;

 		case VMEXIT_CRX_ACCESS:{
			u32 tofrom, gpr, crx; 
			//printf("\nVMEXIT_CRX_ACCESS:");
			//printf("\ninstruction length: %u", info_vmexit_instruction_length);
			crx=(u32) ((u64)vcpu->vmcs.info_exit_qualification & 0x000000000000000FULL);
			gpr=
			 (u32) (((u64)vcpu->vmcs.info_exit_qualification & 0x0000000000000F00ULL) >> (u64)8);
			tofrom = 
			(u32) (((u64)vcpu->vmcs.info_exit_qualification & 0x0000000000000030ULL) >> (u64)4); 
			//printf("\ncrx=%u, gpr=%u, tofrom=%u", crx, gpr, tofrom);
			switch(crx){
				//case 0x3: //CR3 access (v86monitor only)
				//	_vmx_handle_intercept_cr3access(vcpu, r, gpr, tofrom);
				//	break;
				
				case 0x4: //CR4 access
					if(!vcpu->vmx_guest_unrestricted){
						printf("\nHALT: v86 monitor based real-mode exec. unsupported!");
						HALT();
						//handle_intercept_cr4access(vcpu, r, gpr, tofrom);
					}else{
						vmx_handle_intercept_cr4access_ug(vcpu, r, gpr, tofrom);	
					}
					break;
				
				//case 0x0: //CR0 access (v86monitor only)
				//	_vmx_handle_intercept_cr0access(vcpu, r, gpr, tofrom);
				//	break;
			
				default:
					printf("\nunhandled crx, halting!");
					HALT();
			}
			vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
		}
		break;	

 		case VMEXIT_RDMSR:
			_vmx_handle_intercept_rdmsr(vcpu, r);
			break;
			
		case VMEXIT_WRMSR:
			_vmx_handle_intercept_wrmsr(vcpu, r);
			break;
			
		case VMEXIT_CPUID:
			_vmx_handle_intercept_cpuid(vcpu, r);
			break;

    case VMEXIT_INIT:{
        printf("\n***** VMEXIT_INIT emhf_app_handleshutdown\n");
      emhf_app_handleshutdown(vcpu, r);      
      printf("\nCPU(0x%02x): warning, emhf_app_handleshutdown returned!", vcpu->id);
      HALT();
    }
    break;

    case VMEXIT_VMCALL:{
			//check to see if this is a hypercall for INT 15h hooking
			if(vcpu->vmcs.guest_CS_base == (VMX_UG_E820HOOK_CS << 4) &&
				vcpu->vmcs.guest_RIP == VMX_UG_E820HOOK_IP){
				//assertions, we need to be either in real-mode or in protected
				//mode with paging and EFLAGS.VM bit set (virtual-8086 mode)
				ASSERT( !(vcpu->vmcs.guest_CR0 & CR0_PE)  ||
					( (vcpu->vmcs.guest_CR0 & CR0_PE) && (vcpu->vmcs.guest_CR0 & CR0_PG) &&
						(vcpu->vmcs.guest_RFLAGS & EFLAGS_VM)  ) );
				_vmx_int15_handleintercept(vcpu, r);	
			}else{	//if not E820 hook, give app a chance to handle the hypercall
				if( emhf_app_handlehypercall(vcpu, r) != APP_SUCCESS){
					printf("\nCPU(0x%02x): error(halt), unhandled hypercall 0x%08x!", vcpu->id, r->eax);
					HALT();
				}
      	vcpu->vmcs.guest_RIP += 3;
			}
    }
    break;


		case VMEXIT_TASKSWITCH:{
			u32 idt_v = vcpu->vmcs.info_IDT_vectoring_information & VECTORING_INFO_VALID_MASK;
			u32 type = vcpu->vmcs.info_IDT_vectoring_information & VECTORING_INFO_TYPE_MASK;
			u32 reason = vcpu->vmcs.info_exit_qualification >> 30;
			u16 tss_selector = (u16)vcpu->vmcs.info_exit_qualification;
			
			if(reason == TASK_SWITCH_GATE && type == INTR_TYPE_NMI){
	      printf("\nCPU(0x%02x): NMI received (MP guest shutdown?)", vcpu->id);
				emhf_app_handleshutdown(vcpu, r);      
  	    printf("\nCPU(0x%02x): warning, emhf_app_handleshutdown returned!", vcpu->id);
    		printf("\nCPU(0x%02x): HALTING!", vcpu->id);
	      HALT();
			}else{
				printf("\nCPU(0x%02x): Unhandled Task Switch. Halt!", vcpu->id);
				printf("\n	idt_v=0x%08x, type=0x%08x, reason=0x%08x, tsssel=0x%04x",
					idt_v, type, reason, tss_selector); 
			}
    	HALT();
		}
		break;

    
    default:{
      printf("\nCPU(0x%02x): Unhandled intercept: 0x%08x", vcpu->id, (u32)vcpu->vmcs.info_vmexit_reason);
      printf("\n	CPU(0x%02x): EFLAGS=0x%08x", vcpu->id, (u32)vcpu->vmcs.guest_RFLAGS);
			printf("\n	SS:ESP =0x%04x:0x%08x", (u16)vcpu->vmcs.guest_SS_selector, (u32)vcpu->vmcs.guest_RSP);
			printf("\n	CS:EIP =0x%04x:0x%08x", (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP);
			printf("\n	IDTR base:limit=0x%08x:0x%04x", (u32)vcpu->vmcs.guest_IDTR_base,
					(u16)vcpu->vmcs.guest_IDTR_limit);
			//printf("\n 	runtime_v86_idt_base=0x%08x", (u32)__runtime_v86_idt);
			printf("\n	GDTR base:limit=0x%08x:0x%04x", (u32)vcpu->vmcs.guest_GDTR_base,
					(u16)vcpu->vmcs.guest_GDTR_limit);
			//printf("\n 	runtime_v86_idt_base=0x%08x", (u32)__runtime_v86_idt);
     	if(vcpu->vmcs.info_IDT_vectoring_information & 0x80000000){
				printf("\nCPU(0x%02x): HALT; Nested events unhandled 0x%08x",
					vcpu->id, vcpu->vmcs.info_IDT_vectoring_information);
			}


			HALT();
    }
  }

 	//check and clear guest interruptibility state
	if(vcpu->vmcs.guest_interruptibility != 0){
		//printf("\nWARNING!: interruptibility=%08lx", (unsigned long)vcpu->vmcs.guest_interruptibility);
		vcpu->vmcs.guest_interruptibility = 0;
	}

	//make sure we have no nested events
	if(vcpu->vmcs.info_IDT_vectoring_information & 0x80000000){
				printf("\nCPU(0x%02x): HALT; Nested events unhandled with hwp:0x%08x",
					vcpu->id, vcpu->vmcs.info_IDT_vectoring_information);
				HALT();
	}

	//write updated VMCS back to CPU
  _vmx_putVMCS(vcpu);
  if(vcpu->vmcs.guest_RIP == 0x7c00){
		printf("\nCPU(0x%02x): We are starting at guest boot-sector...", vcpu->id);
	}
	
	return 1;
}
