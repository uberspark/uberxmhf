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
		vcpu.cpu_vendor = CPU_VENDOR_AMD;								//stick with AMD now
		vcpu.npt_vaddr_pts = 0xC8000000;								//where our NPTs reside
		vcpu.vmcb_vaddr_ptr = (u32)&_xvmcb;								//set vcpu VMCB virtual address to something meaningful

		//globals
		g_svm_lapic_base = 0xFEE00000;
		
		//state under the control of attacker, we need these to be
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
		
		assert(1);
}
//----------------------------------------------------------------------
