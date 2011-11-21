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
// EMHF partition event-hub for AMD x86 svm
// author: amit vasudevan (amitvasudevan@acm.org)
#include <emhf.h> 

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


//---SVM intercept handler hub--------------------------------------------------
u32 svm_intercept_handler(VCPU *vcpu, struct regs *r){
  struct vmcb_struct *vmcb = (struct vmcb_struct *)vcpu->vmcb_vaddr_ptr;
  
  vmcb->tlb_control = TLB_CONTROL_NOTHING;
    
  switch(vmcb->exitcode){
    //IO interception
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
      {
        u8 *code;
        u32 paddr;
        int i;
        paddr= svm_kernel_pt_walker(vmcb, (u32)vmcb->rip); 
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
			//check to see if this is a hypercall for INT 15h hooking
			if(vmcb->cs.base == (VMX_UG_E820HOOK_CS << 4) &&
				vmcb->rip == VMX_UG_E820HOOK_IP){
				//assertions, we need to be either in real-mode or in protected
				//mode with paging and EFLAGS.VM bit set (virtual-8086 mode)
				ASSERT( !(vmcb->cr0 & CR0_PE)  ||
					( (vmcb->cr0 & CR0_PE) && (vmcb->cr0 & CR0_PG) &&
						(vmcb->rflags & EFLAGS_VM)  ) );
				_svm_int15_handleintercept(vcpu, r);	
			}else{	//if not E820 hook, give app a chance to handle the hypercall
				if( emhf_app_handlehypercall(vcpu, r) != APP_SUCCESS){
					printf("\nCPU(0x%02x): error(halt), unhandled hypercall 0x%08x!", vcpu->id, r->eax);
					HALT();
				}
      	vmcb->rip += 3;
			}
    }
    break;

    case VMEXIT_NMI:{
        _svm_handle_nmi(vcpu, vmcb, r);
      }
      break;
    
		default:{
				printf("\nUnhandled Intercept:0x%08llx", vmcb->exitcode);
				printf("\nCS:EIP=0x%04x:0x%08x", (u16)vmcb->cs.sel, (u32)vmcb->rip);
        HALT();
		}
	}	//end switch(vmcb->exitcode)	

	return 0;
}
