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

//----------------------------------------------------------------------
// xmhf-core-verify-startup.c
// XMHF core startup verification driver
// author: amit vasudevan (amitvasudevan@acm.org)
//----------------------------------------------------------------------
#include <xmhf.h>

//if the following is defined, we will excercise the VMX backend
//for ihub during verification
#define X86_VMX			1
u32 xmhf_verify_cpu_vendor = CPU_VENDOR_INTEL;

//u32 xmhf_verify_cpu_vendor = CPU_VENDOR_AMD;

//globals referenced by this module
VCPU vcpu;
struct _svm_vmcbfields _xvmcb;
RPB *rpb; 	//runtime parameter block pointer
RPB _xrpb;	

void runtime_main(){
		/* xmhf_runtime_main */
		extern void xmhf_runtime_main(void);
		//setup RPB pointer and required runtime parameter block values
		rpb = (RPB *)&_xrpb;
		rpb->XtVmmE820NumEntries = 1; 									//number of E820 entries
		rpb->XtVmmRuntimePhysBase = 0xC0000000;							//runtime physical base address
		rpb->XtVmmRuntimeSize = 0x8800000;								//128 MB + 8MB (NPTs) runtime size
		rpb->XtGuestOSBootModuleBase = 0x20000;							//guest OS boot module base address
		rpb->XtGuestOSBootModuleSize = 512;								//guest OS boot module size
		rpb->runtime_appmodule_base = 0;								//optional hypapp module base
		rpb->runtime_appmodule_size = 0;								//optional hypapp module size


		//setup bare minimum vcpu
		vcpu.isbsp = 1;													//assume BSP
		vcpu.id = 0;													//give a LAPIC id
		vcpu.esp = 0xC6000000;											//give a stack

#if defined (X86_VMX)
		vcpu.cpu_vendor = CPU_VENDOR_INTEL;								
		vcpu.vmx_vmcs_vaddr = 0xC7000000;								//VMCS address
		vcpu.vmx_vaddr_ept_pml4_table = 0xC7F00000;						//EPT PML4 table 		
		vcpu.vmx_guest_unrestricted = 1;								//VMX unrestricted guest support
		vcpu.vmx_vaddr_ept_p_tables = 0xC8000000;						//EPT page tables
#else
		vcpu.cpu_vendor = CPU_VENDOR_AMD;
		vcpu.vmcb_vaddr_ptr = &_xvmcb;									//set vcpu VMCB virtual address to something meaningful
		vcpu.npt_vaddr_ptr = 0xC7F00000;								//NPT PDPT page
		vcpu.npt_vaddr_pts = 0xC8000000;								//where our NPTs reside
#endif		
				
		xmhf_runtime_main(&vcpu, 0);									//call "init" function

}

	
void runtime_entry_main(){
		/* xmhf_runtime_entry */
		extern void xmhf_runtime_entry(void);
		xmhf_runtime_entry();
}

//----------------------------------------------------------------------

void main(){
		runtime_entry_main();
		
		runtime_main();
}
