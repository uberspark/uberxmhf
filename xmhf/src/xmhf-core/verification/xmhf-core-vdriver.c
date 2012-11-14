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
// xmhf-core-vdriver.c
// XMHF core CBMC verification driver
// author: amit vasudevan (amitvasudevan@acm.org)
//----------------------------------------------------------------------
#include <xmhf.h>



#define V_HYPERCALL		0xDEADBEEF

VCPU vcpu;
struct regs r;
struct _svm_vmcbfields _xvmcb;
//globals referenced by this module
RPB *rpb; 	//runtime parameter block pointer
//actual definitions
RPB _xrpb;	

void main() {
		//setup RPB pointer and required runtime parameter block values
		rpb = (RPB *)&_xrpb;
		rpb->XtVmmE820NumEntries = 1; 									//lets worry about E820 later
		rpb->XtVmmRuntimePhysBase = 0xC0000000;
		rpb->XtVmmRuntimeSize = 0x8800000;								//128 MB + 8MB (NPTs) runtime size

		//setup bare minimum vcpu
		vcpu.isbsp = 1;													//assume BSP
		vcpu.id = 0;													//give a LAPIC id
		vcpu.cpu_vendor = CPU_VENDOR_INTEL;								//stick with AMD now

		//AMD specific fields
		vcpu.npt_vaddr_ptr = 0xC7F00000;								//NPT PDPT page
		vcpu.npt_vaddr_pts = 0xC8000000;								//where our NPTs reside
		vcpu.vmcb_vaddr_ptr = &_xvmcb;									//set vcpu VMCB virtual address to something meaningful

		//Intel specific fields
		vcpu.vmx_vmcs_vaddr = 0xC7000000;								//VMCS address
		
		
		//globals
		g_midtable_numentries=1;

		g_svm_lapic_base = 0xFEE00000;


		emhf_runtime_main(&vcpu, 0);									//call "init" function
		
/*		//state under the control of attacker, we need these to be
		//non-deterministic
		{
			_xvmcb.exitcode = (u64)nondet_u64();
			_xvmcb.exitinfo1 = (u64)nondet_u64();
			_xvmcb.exitinfo2 = (u64)nondet_u64();

			_xvmcb.es.attrib = (u16)nondet_u16();
			_xvmcb.es.base = (u64)nondet_u64();
			_xvmcb.es.limit = (u32)nondet_u32();
			_xvmcb.es.selector = (u16)nondet_u16();

			_xvmcb.cs.attrib = (u16)nondet_u16();
			_xvmcb.cs.base = (u64)nondet_u64();
			_xvmcb.cs.limit = (u32)nondet_u32();
			_xvmcb.cs.selector = (u16)nondet_u16();

			_xvmcb.ss.attrib = (u16)nondet_u16();
			_xvmcb.ss.base = (u64)nondet_u64();
			_xvmcb.ss.limit = (u32)nondet_u32();
			_xvmcb.ss.selector = (u16)nondet_u16();

			_xvmcb.ds.attrib = (u16)nondet_u16();
			_xvmcb.ds.base = (u64)nondet_u64();
			_xvmcb.ds.limit = (u32)nondet_u32();
			_xvmcb.ds.selector = (u16)nondet_u16();

			_xvmcb.fs.attrib = (u16)nondet_u16();
			_xvmcb.fs.base = (u64)nondet_u64();
			_xvmcb.fs.limit = (u32)nondet_u32();
			_xvmcb.fs.selector = (u16)nondet_u16();

			_xvmcb.gs.attrib = (u16)nondet_u16();
			_xvmcb.gs.base = (u64)nondet_u64();
			_xvmcb.gs.limit = (u32)nondet_u32();
			_xvmcb.gs.selector = (u16)nondet_u16();

			_xvmcb.gdtr.attrib = (u16)nondet_u16();
			_xvmcb.gdtr.base = (u64)nondet_u64();
			_xvmcb.gdtr.limit = (u32)nondet_u32();
			_xvmcb.gdtr.selector = (u16)nondet_u16();

			_xvmcb.ldtr.attrib = (u16)nondet_u16();
			_xvmcb.ldtr.base = (u64)nondet_u64();
			_xvmcb.ldtr.limit = (u32)nondet_u32();
			_xvmcb.ldtr.selector = (u16)nondet_u16();
			
			_xvmcb.idtr.attrib = (u16)nondet_u16();
			_xvmcb.idtr.base = (u64)nondet_u64();
			_xvmcb.idtr.limit = (u32)nondet_u32();
			_xvmcb.idtr.selector = (u16)nondet_u16();

			_xvmcb.tr.attrib = (u16)nondet_u16();
			_xvmcb.tr.base = (u64)nondet_u64();
			_xvmcb.tr.limit = (u32)nondet_u32();
			_xvmcb.tr.selector = (u16)nondet_u16();
			
			_xvmcb.cr4 = (u64)nondet_u64();
			_xvmcb.cr3 = (u64)nondet_u64();
			_xvmcb.cr0 = (u64)nondet_u64();
			_xvmcb.dr7 = (u64)nondet_u64();
			_xvmcb.dr6 = (u64)nondet_u64();
			_xvmcb.rflags = (u64)nondet_u64();
			_xvmcb.rip = (u64)nondet_u64();
			_xvmcb.rsp = (u64)nondet_u64();
			_xvmcb.rax = (u64)nondet_u64();
			_xvmcb.cr2 = (u64)nondet_u64();
			_xvmcb.g_pat = (u64)nondet_u64();
			_xvmcb.efer = (u64)nondet_u64();                   

			r.eax = r.ebx = r.ecx= r.edx = r.esi = r.edi = r.ebp = r.esp = nondet_u32(); 
		}

		emhf_parteventhub_arch_x86svm_intercept_handler(&vcpu, &r);
*/
		
		assert(1);
}
//----------------------------------------------------------------------
