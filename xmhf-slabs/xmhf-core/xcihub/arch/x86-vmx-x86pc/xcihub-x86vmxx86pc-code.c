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

// XMHF ihub slab -- x86 (VMX) backend implementation
// author: amit vasudevan (amitvasudevan@acm.org)
#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcihub.h>
#include <xcapi.h>
#include <xhhyperdep.h>
#include <xcrichguest.h>


static u32 _vmx_getregval(u32 gpr, struct regs r){

	  switch(gpr){
		case 0: return r.eax;
		case 1: return r.ecx;
		case 2: return r.edx;
		case 3: return r.ebx;
		case 4: return r.esp;
		case 5: return r.ebp;
		case 6: return r.esi;
		case 7: return r.edi;
		default:
			_XDPRINTF_("\n%s: warning, invalid gpr value (%u): returning zero value", __FUNCTION__, gpr);
			return 0;
	}
}

//---intercept handler (CPUID)--------------------------------------------------
static struct regs _vmx_handle_intercept_cpuid(context_desc_t context_desc, struct regs r){
	asm volatile ("cpuid\r\n"
          :"=a"(r.eax), "=b"(r.ebx), "=c"(r.ecx), "=d"(r.edx)
          :"a"(r.eax), "c" (r.ecx));
    return r;
}

//------------------------------------------------------------------------------
// guest MSR r/w intercept handling
// HAL invokes NT kernel via SYSENTER if CPU supports it. However,
// regular apps using NTDLL will still use INT 2E if registry entry is not
// tweaked. So, we HAVE to emulate SYSENTER_CS/EIP/ESP to ensure that
// NT kernel doesnt panic with SESSION5_INITIALIZATION_FAILED!
//
// This took me nearly a month of disassembly into the HAL,
// NTKERNEL and debugging to figure out..eh?
//
// AMD SVM is neater, only
// when you ask for these MSR intercepts do they get stored and read from
// the VMCB. However, for Intel regardless they get stored and read from VMCS
// for the guest. So we need to have these intercepts bare minimum!!
// A line to this effect would have been much appreciated in the Intel manuals
// doh!!!
//------------------------------------------------------------------------------

//---intercept handler (WRMSR)--------------------------------------------------
static void _vmx_handle_intercept_wrmsr(context_desc_t context_desc, struct regs r){
	//_XDPRINTF_("\nCPU(0x%02x): WRMSR 0x%08x", xc_cpu->cpuid, r.ecx);
	xc_hypapp_arch_param_t ap;

	ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_SYSENTER));
	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_SYSENTER;

	switch(r.ecx){
		case IA32_SYSENTER_CS_MSR:
			ap.param.sysenter.sysenter_cs = r.eax;
			XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, ap));
			break;
		case IA32_SYSENTER_EIP_MSR:
			ap.param.sysenter.sysenter_rip = r.eax;
			XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, ap));
			break;
		case IA32_SYSENTER_ESP_MSR:
			ap.param.sysenter.sysenter_rsp = r.eax;
			XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, ap));
			break;
		default:{
			asm volatile ("wrmsr\r\n"
          : //no outputs
          :"a"(r.eax), "c" (r.ecx), "d" (r.edx));
			break;
		}
	}
}

//---intercept handler (RDMSR)--------------------------------------------------
static struct regs _vmx_handle_intercept_rdmsr(context_desc_t context_desc, struct regs r){
	xc_hypapp_arch_param_t ap;

	ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_SYSENTER));

	switch(r.ecx){
		case IA32_SYSENTER_CS_MSR:
			r.eax = ap.param.sysenter.sysenter_cs;
			r.edx = 0;
			break;
		case IA32_SYSENTER_EIP_MSR:
			r.eax = ap.param.sysenter.sysenter_rip;
			r.edx = 0;
			break;
		case IA32_SYSENTER_ESP_MSR:
			r.eax = ap.param.sysenter.sysenter_rsp;
			r.edx = 0;
			break;
		default:{
			asm volatile ("rdmsr\r\n"
          : "=a"(r.eax), "=d"(r.edx)
          : "c" (r.ecx));
			break;
		}
	}

	return r;
}


//---intercept handler (EPT voilation)----------------------------------
static void _vmx_handle_intercept_eptviolation(context_desc_t context_desc, u32 gpa, u32 gva, u32 errorcode, struct regs r __attribute__((unused))){

	XMHF_SLAB_CALL(xmhf_hypapp_handleintercept_hptfault(context_desc, gpa, gva,	(errorcode & 7)));
}


//---intercept handler (I/O port access)----------------------------------------
static struct regs _vmx_handle_intercept_ioportaccess(context_desc_t context_desc, u32 access_size, u32 access_type,
	u32 portnum, u32 stringio, struct regs r __attribute__((unused))){
	u32 app_ret_status = APP_TRAP_CHAIN;

	HALT_ON_ERRORCOND(!stringio);	//we dont handle string IO intercepts

	{
		xc_hypapp_arch_param_t xc_hypapp_arch_param;
		xc_hypapp_arch_param.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CBTRAP_IO;
		xc_hypapp_arch_param.param.cbtrapio.portnum = portnum;
		xc_hypapp_arch_param.param.cbtrapio.access_type = access_type;
		xc_hypapp_arch_param.param.cbtrapio.access_size = access_size;
		app_ret_status=XMHF_SLAB_CALL(xmhf_hypapp_handleintercept_trap(context_desc, xc_hypapp_arch_param));
	}

	if(app_ret_status == APP_TRAP_CHAIN){
		if(access_type == IO_TYPE_OUT){
			if( access_size== IO_SIZE_BYTE)
					outb((u8)r.eax, portnum);
			else if (access_size == IO_SIZE_WORD)
					outw((u16)r.eax, portnum);
			else if (access_size == IO_SIZE_DWORD)
					outl((u32)r.eax, portnum);
		}else{
			if( access_size== IO_SIZE_BYTE){
					r.eax &= 0xFFFFFF00UL;	//clear lower 8 bits
					r.eax |= (u8)inb(portnum);
			}else if (access_size == IO_SIZE_WORD){
					r.eax &= 0xFFFF0000UL;	//clear lower 16 bits
					r.eax |= (u16)inw(portnum);
			}else if (access_size == IO_SIZE_DWORD){
					r.eax = (u32)inl(portnum);
			}
		}
	}

	return r;
}


//---CR0 access handler-------------------------------------------------
static void vmx_handle_intercept_cr0access_ug(context_desc_t context_desc, struct regs r, u32 gpr, u32 tofrom){
	u32 cr0_value;
	xc_hypapp_arch_param_t ap;

	HALT_ON_ERRORCOND(tofrom == VMX_CRX_ACCESS_TO);

	cr0_value = _vmx_getregval(gpr, r);

	ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS));
	ap.param.controlregs.cr0 = cr0_value;
	ap.param.controlregs.control_cr0_shadow = (cr0_value & ~(CR0_CD | CR0_NW));
	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS;
	XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, ap));

	//we need to flush logical processor VPID mappings as we emulated CR0 load above
	__vmx_invvpid(VMX_INVVPID_SINGLECONTEXT, 1, 0);
}

//---CR4 access handler---------------------------------------------------------
static void vmx_handle_intercept_cr4access_ug(context_desc_t context_desc, struct regs r, u32 gpr, u32 tofrom){
  if(tofrom == VMX_CRX_ACCESS_TO){
	u32 cr4_proposed_value;

	cr4_proposed_value = _vmx_getregval(gpr, r);

	//we need to flush logical processor VPID mappings as we emulated CR4 load above
	__vmx_invvpid(VMX_INVVPID_SINGLECONTEXT, 1, 0);
  }
}

//---XSETBV intercept handler-------------------------------------------
static void _vmx_handle_intercept_xsetbv(context_desc_t context_desc, struct regs r){
	u64 xcr_value;

	xcr_value = ((u64)r.edx << 32) + (u64)r.eax;

	if(r.ecx != XCR_XFEATURE_ENABLED_MASK){
			_XDPRINTF_("\n%s: unhandled XCR register %u", __FUNCTION__, r.ecx);
			HALT();
	}

	//XXX: TODO: check for invalid states and inject GP accordingly
	_XDPRINTF_("\n%s: xcr_value=%llx", __FUNCTION__, xcr_value);

	//set XCR with supplied value
	xsetbv(XCR_XFEATURE_ENABLED_MASK, xcr_value);
}

static void _vmx_propagate_cpustate_guestx86gprs(context_desc_t context_desc, struct regs x86gprs){
	xc_hypapp_arch_param_t ap;

	ap.param.cpugprs = x86gprs;
	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS;
	XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, ap));
}

//====================================================================================

static void _vmx_intercept_handler(context_desc_t context_desc, struct regs x86gprs){
	xc_hypapp_arch_param_t ap;
	xc_hypapp_arch_param_x86vmx_cpustate_inforegs_t inforegs;

	ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_INFOREGS));
	inforegs = ap.param.inforegs;


	//sanity check for VM-entry errors
	if( inforegs.info_vmexit_reason & 0x80000000UL ){
		_XDPRINTF_("\nVM-ENTRY error: reason=0x%08x, qualification=0x%016llx",
			inforegs.info_vmexit_reason, inforegs.info_exit_qualification);
		HALT();
	}

	//make sure we have no nested events
	if( inforegs.info_idt_vectoring_information & 0x80000000){
		_XDPRINTF_("\nCPU(0x%02x): HALT; Nested events unhandled with hwp:0x%08x",
			context_desc.cpu_desc.cpu_index, inforegs.info_idt_vectoring_information);
		HALT();
	}

	//handle intercepts
	switch(inforegs.info_vmexit_reason){
		//--------------------------------------------------------------
		//xmhf-core and hypapp intercepts
		//--------------------------------------------------------------

		case VMX_VMEXIT_VMCALL:{
			xc_hypapp_arch_param_t vmmcall_ap;
			xc_hypapp_arch_param_x86vmx_cpustate_desc_t vmmcall_desc;
			xc_hypapp_arch_param_x86vmx_cpustate_activity_t vmmcall_activity;
			xc_hypapp_arch_param_x86vmx_cpustate_controlregs_t vmmcall_controlregs;

			vmmcall_ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_DESC));
			vmmcall_desc = vmmcall_ap.param.desc;
			vmmcall_ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY));
			vmmcall_activity = vmmcall_ap.param.activity;
			vmmcall_ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS));
			vmmcall_controlregs = vmmcall_ap.param.controlregs;

			//if INT 15h E820 hypercall, then let the xmhf-core handle it
			if(vmmcall_desc.cs.base == (VMX_UG_E820HOOK_CS << 4) &&	vmmcall_activity.rip == VMX_UG_E820HOOK_IP){
				//we need to be either in real-mode or in protected
				//mode with paging and EFLAGS.VM bit set (virtual-8086 mode)
				HALT_ON_ERRORCOND( !(vmmcall_controlregs.cr0 & CR0_PE)  ||
					( (vmmcall_controlregs.cr0 & CR0_PE) && (vmmcall_controlregs.cr0 & CR0_PG) &&
						(vmmcall_activity.rflags & EFLAGS_VM)  ) );
				x86gprs = XMHF_SLAB_CALL(xcrichguest_arch_handle_guestmemoryreporting(context_desc, x86gprs));
				_vmx_propagate_cpustate_guestx86gprs(context_desc, x86gprs);

				vmmcall_ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY));
				vmmcall_activity = vmmcall_ap.param.activity;
				vmmcall_activity.interruptibility=0;
				vmmcall_ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
				vmmcall_ap.param.activity = vmmcall_activity;
				XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, vmmcall_ap));


			}else{	//if not E820 hook, give hypapp a chance to handle the hypercall
				{
					u64 hypercall_id = (u64)x86gprs.eax;
					u64 hypercall_param = ((u64)x86gprs.edx << 32) | x86gprs.ecx;

					if( XMHF_SLAB_CALL(xmhf_hypapp_handlehypercall(context_desc, hypercall_id, hypercall_param)) != APP_SUCCESS){
						_XDPRINTF_("\nCPU(0x%02x): error(halt), unhandled hypercall 0x%08x!", context_desc.cpu_desc.cpu_index, x86gprs.eax);
						HALT();
					}
				}

				vmmcall_ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY));
				vmmcall_activity = vmmcall_ap.param.activity;
				vmmcall_activity.rip+=3;
				vmmcall_activity.interruptibility=0;
				vmmcall_ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
				vmmcall_ap.param.activity = vmmcall_activity;
				XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, vmmcall_ap));
			}
		}
		break;

		case VMX_VMEXIT_IOIO:{
			u32 access_size, access_type, portnum, stringio;
			xc_hypapp_arch_param_t ioio_ap;
			xc_hypapp_arch_param_x86vmx_cpustate_activity_t ioio_activity;

			access_size = inforegs.info_exit_qualification & 0x00000007UL;
			access_type = ( inforegs.info_exit_qualification & 0x00000008UL) >> 3;
			portnum =  ( inforegs.info_exit_qualification & 0xFFFF0000UL) >> 16;
			stringio = ( inforegs.info_exit_qualification & 0x00000010UL) >> 4;

			x86gprs = _vmx_handle_intercept_ioportaccess(context_desc, access_size, access_type, portnum, stringio, x86gprs);
			_vmx_propagate_cpustate_guestx86gprs(context_desc, x86gprs);
			ioio_ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY));
			ioio_activity = ioio_ap.param.activity;
			ioio_activity.rip+=inforegs.info_vmexit_instruction_length;
			ioio_activity.interruptibility=0;
			ioio_ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
			ioio_ap.param.activity = ioio_activity;
			XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, ioio_ap));
		}
		break;

		case VMX_VMEXIT_EPT_VIOLATION:{
			u32 errorcode, gpa, gva;
			xc_hypapp_arch_param_t eptviolation_ap;
			xc_hypapp_arch_param_x86vmx_cpustate_activity_t eptviolation_activity;

			errorcode = inforegs.info_exit_qualification;
			gpa = inforegs.info_guest_paddr_full;
			gva = inforegs.info_guest_linear_address;

			_vmx_handle_intercept_eptviolation(context_desc, gpa, gva, errorcode, x86gprs);

			eptviolation_ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY));
			eptviolation_activity = eptviolation_ap.param.activity;
			eptviolation_activity.interruptibility=0;
			eptviolation_ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
			eptviolation_ap.param.activity = eptviolation_activity;
			XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, eptviolation_ap));
		}
		break;

		case VMX_VMEXIT_INIT:{
			_XDPRINTF_("\n***** VMEXIT_INIT xmhf_hypapp_handleshutdown\n");
			XMHF_SLAB_CALL(xmhf_hypapp_handleshutdown(context_desc));
			_XDPRINTF_("\nCPU(0x%02x): Fatal, xmhf_hypapp_handleshutdown returned. Halting!", context_desc.cpu_desc.cpu_index);
			HALT();
		}
		break;

		//--------------------------------------------------------------
		//xmhf-core only intercepts
		//--------------------------------------------------------------

 		case VMX_VMEXIT_CRX_ACCESS:{
			u32 tofrom, gpr, crx;
			xc_hypapp_arch_param_t crxaccess_ap;
			xc_hypapp_arch_param_x86vmx_cpustate_activity_t crxaccess_activity;

			crx=(u32) ((u64)inforegs.info_exit_qualification & 0x000000000000000FULL);
			gpr=(u32) (((u64)inforegs.info_exit_qualification & 0x0000000000000F00ULL) >> (u64)8);
			tofrom = (u32) (((u64)inforegs.info_exit_qualification & 0x0000000000000030ULL) >> (u64)4);

			if ( ((int)gpr >=0) && ((int)gpr <= 7) ){
				switch(crx){
					case 0x0: //CR0 access
						vmx_handle_intercept_cr0access_ug(context_desc, x86gprs, gpr, tofrom);
						break;

					case 0x4: //CR4 access
						vmx_handle_intercept_cr4access_ug(context_desc, x86gprs, gpr, tofrom);
						break;

					default:
						_XDPRINTF_("\nunhandled crx, halting!");
						HALT();
				}
				crxaccess_ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY));
				crxaccess_activity = crxaccess_ap.param.activity;
				crxaccess_activity.rip+=inforegs.info_vmexit_instruction_length;
				crxaccess_activity.interruptibility=0;
				crxaccess_ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
				crxaccess_ap.param.activity = crxaccess_activity;
				XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, crxaccess_ap));

			}else{
				_XDPRINTF_("\n[%02x]%s: invalid gpr value (%u). halting!", context_desc.cpu_desc.cpu_index,
					__FUNCTION__, gpr);
				HALT();
			}
		}
		break;

 		case VMX_VMEXIT_RDMSR:{
			xc_hypapp_arch_param_t rdmsr_ap;
			xc_hypapp_arch_param_x86vmx_cpustate_activity_t rdmsr_activity;

			x86gprs = _vmx_handle_intercept_rdmsr(context_desc, x86gprs);
			_vmx_propagate_cpustate_guestx86gprs(context_desc, x86gprs);

			rdmsr_ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY));
			rdmsr_activity = rdmsr_ap.param.activity;
			rdmsr_activity.rip+=inforegs.info_vmexit_instruction_length;
			rdmsr_activity.interruptibility=0;
			rdmsr_ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
			rdmsr_ap.param.activity = rdmsr_activity;
			XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, rdmsr_ap));
		}
		break;

		case VMX_VMEXIT_WRMSR:{
			xc_hypapp_arch_param_t wrmsr_ap;
			xc_hypapp_arch_param_x86vmx_cpustate_activity_t wrmsr_activity;

			_vmx_handle_intercept_wrmsr(context_desc, x86gprs);

			wrmsr_ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY));
			wrmsr_activity = wrmsr_ap.param.activity;
			wrmsr_activity.rip+=inforegs.info_vmexit_instruction_length;
			wrmsr_activity.interruptibility=0;
			wrmsr_ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
			wrmsr_ap.param.activity = wrmsr_activity;
			XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, wrmsr_ap));
		}
		break;

		case VMX_VMEXIT_CPUID:{
			xc_hypapp_arch_param_t cpuid_ap;
			xc_hypapp_arch_param_x86vmx_cpustate_activity_t cpuid_activity;

			x86gprs = _vmx_handle_intercept_cpuid(context_desc, x86gprs);
			_vmx_propagate_cpustate_guestx86gprs(context_desc, x86gprs);

			cpuid_ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY));
			cpuid_activity = cpuid_ap.param.activity;
			cpuid_activity.rip+=inforegs.info_vmexit_instruction_length;
			cpuid_activity.interruptibility=0;
			cpuid_ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
			cpuid_ap.param.activity = cpuid_activity;
			XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, cpuid_ap));
		}
		break;

		case VMX_VMEXIT_TASKSWITCH:{
			u32 idt_v = inforegs.info_idt_vectoring_information & VECTORING_INFO_VALID_MASK;
			u32 type = inforegs.info_idt_vectoring_information & VECTORING_INFO_TYPE_MASK;
			u32 reason = inforegs.info_exit_qualification >> 30;
			u16 tss_selector = (u16)inforegs.info_exit_qualification;

			if(reason == TASK_SWITCH_GATE && type == INTR_TYPE_NMI){
				_XDPRINTF_("\nCPU(0x%02x): NMI received (MP guest shutdown?)", context_desc.cpu_desc.cpu_index);
				XMHF_SLAB_CALL(xmhf_hypapp_handleshutdown(context_desc));
				_XDPRINTF_("\nCPU(0x%02x): warning, xmhf_hypapp_handleshutdown returned!", context_desc.cpu_desc.cpu_index);
				_XDPRINTF_("\nCPU(0x%02x): HALTING!", context_desc.cpu_desc.cpu_index);
				HALT();
			}else{
				_XDPRINTF_("\nCPU(0x%02x): Unhandled Task Switch. Halt!", context_desc.cpu_desc.cpu_index);
				_XDPRINTF_("\n	idt_v=0x%08x, type=0x%08x, reason=0x%08x, tsssel=0x%04x",
					idt_v, type, reason, tss_selector);
			}
			HALT();
		}
		break;

		case VMX_VMEXIT_XSETBV:{
			xc_hypapp_arch_param_t xsetbv_ap;
			xc_hypapp_arch_param_x86vmx_cpustate_activity_t xsetbv_activity;

			_vmx_handle_intercept_xsetbv(context_desc, x86gprs);

			xsetbv_ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY));
			xsetbv_activity = xsetbv_ap.param.activity;
			xsetbv_activity.rip+=inforegs.info_vmexit_instruction_length;
			xsetbv_activity.interruptibility=0;
			xsetbv_ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
			xsetbv_ap.param.activity = xsetbv_activity;
			XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, xsetbv_ap));
		}
		break;

		case VMX_VMEXIT_SIPI:{
			u32 sipivector = (u8)inforegs.info_exit_qualification;
			xc_hypapp_arch_param_t sipi_ap;
			xc_hypapp_arch_param_x86vmx_cpustate_activity_t sipi_activity;
			xc_hypapp_arch_param_x86vmx_cpustate_desc_t sipi_desc;

			sipi_ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY));
			sipi_activity = sipi_ap.param.activity;
			sipi_ap = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_DESC));
			sipi_desc = sipi_ap.param.desc;

			_XDPRINTF_("\nCPU(%02x): SIPI vector=0x%08x", context_desc.cpu_desc.cpu_index, sipivector);
			sipi_desc.cs.selector = ((sipivector * PAGE_SIZE_4K) >> 4);
			sipi_desc.cs.base = (sipivector * PAGE_SIZE_4K);
			sipi_activity.rip = 0;
			sipi_activity.activity_state = 0; //active
			sipi_activity.interruptibility=0;

			sipi_ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
			sipi_ap.param.activity = sipi_activity;
			XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, sipi_ap));
			sipi_ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_DESC;
			sipi_ap.param.desc = sipi_desc;
			XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, sipi_ap));

		}
		break;


		default:{
			_XDPRINTF_("\nCPU(0x%02x): Unhandled intercept: 0x%08x Halting!", context_desc.cpu_desc.cpu_index, (u32)inforegs.info_vmexit_reason);
			HALT();
		}
	} //end inforegs.info_vmexit_reason
}




//void xmhf_partition_eventhub_arch_x86vmx(xc_cpu_t *xc_cpu, struct regs *cpugprs){
void xmhf_partition_eventhub_arch_x86vmx(struct regs *cpugprs){
	static u32 _xc_partition_eventhub_lock = 1;
	xc_hypapp_arch_param_t cpustateparams;
	struct regs x86gprs;
	context_desc_t context_desc;

	//serialize
    spin_lock(&_xc_partition_eventhub_lock);

	context_desc = XMHF_SLAB_CALL(xc_api_partition_getcontextdesc(xmhf_baseplatform_arch_x86_getcpulapicid()));
	if(context_desc.cpu_desc.cpu_index == XC_PARTITION_INDEX_INVALID || context_desc.partition_desc.partition_index == XC_PARTITION_INDEX_INVALID){
		_XDPRINTF_("\n%s: invalid partition/cpu context. Halting!\n", __FUNCTION__);
		HALT();
	}

	//set cpu gprs state based on cpugprs
	cpustateparams = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS));
	x86gprs.edi = cpustateparams.param.cpugprs.edi = cpugprs->edi;
	x86gprs.esi = cpustateparams.param.cpugprs.esi = cpugprs->esi;
	x86gprs.ebp = cpustateparams.param.cpugprs.ebp = cpugprs->ebp;
	x86gprs.esp = cpustateparams.param.cpugprs.esp;	//guest ESP is stored in the VMCS and is returned by xc_api_cpustate_get above
	x86gprs.ebx = cpustateparams.param.cpugprs.ebx = cpugprs->ebx;
	x86gprs.edx = cpustateparams.param.cpugprs.edx = cpugprs->edx;
	x86gprs.ecx = cpustateparams.param.cpugprs.ecx = cpugprs->ecx;
	x86gprs.eax = cpustateparams.param.cpugprs.eax = cpugprs->eax;
	cpustateparams.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS;
	XMHF_SLAB_CALL(xc_api_cpustate_set(context_desc, cpustateparams));

	_vmx_intercept_handler(context_desc, x86gprs);

	cpustateparams = XMHF_SLAB_CALL(xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS));
	cpugprs->edi = cpustateparams.param.cpugprs.edi;
	cpugprs->esi = cpustateparams.param.cpugprs.esi;
	cpugprs->ebp = cpustateparams.param.cpugprs.ebp;
	//cpugprs->esp, guest ESP is loaded from VMCS which is set using xc_api_cpustate_set
	cpugprs->ebx = cpustateparams.param.cpugprs.ebx;
	cpugprs->edx = cpustateparams.param.cpugprs.edx;
	cpugprs->ecx = cpustateparams.param.cpugprs.ecx;
	cpugprs->eax = cpustateparams.param.cpugprs.eax;

	//end serialization and resume partition
    spin_unlock(&_xc_partition_eventhub_lock);
}


//==================================================================================

/*//---hvm_intercept_handler------------------------------------------------------
void xcihub_arch_entry(void) __attribute__((naked)){

		asm volatile (
			"pushal\r\n"
			"movl %0, %%eax \r\n"				//eax = VMCS_INFO_VMEXIT_REASON
			"vmread %%eax, %%ebx \r\n"			//ebx = VMCS[VMCS_INFO_VMEXIT_REASON]
			"cmpl %1, %%ebx \r\n"				//if (ebx == VMX_VMEXIT_EXCEPTION)
			"jne normal \r\n"					//nope, so just do normal eventhub processing
			"movl %2, %%eax \r\n"				//eax = VMCS_INFO_VMEXIT_INTERRUPT_INFORMATION
			"vmread %%eax, %%ebx \r\n"			//ebx = VMCS[VMCS_INFO_VMEXIT_INTERRUPT_INFORMATION]
			"andl %3, %%ebx \r\n"				//ebx &= INTR_INFO_VECTOR_MASK
			"cmpl %4, %%ebx \r\n"				//if (ebx == 0x2)
			"jne normal \r\n"					//nope, so just do normal eventhub processing
			"int $0x02 \r\n"					//NMI exception intercept, so trigger NMI handler
			"jmp exithub \r\n"					//skip over normal event hub processing
			"normal: \r\n"						//normal event hub processing setup
			"movl %%esp, %%eax\r\n"
			"pushl %%eax\r\n"
			"call xmhf_partition_eventhub_arch_x86vmx\r\n"
			"addl $0x04, %%esp\r\n"
			"exithub: \r\n"						//event hub epilogue to resume partition
			"popal\r\n"
			"vmresume\r\n"
			"int $0x03\r\n"
			"hlt\r\n"
			: //no outputs
			: "i" (VMCS_INFO_VMEXIT_REASON), "i" (VMX_VMEXIT_EXCEPTION), "i" (VMCS_INFO_VMEXIT_INTERRUPT_INFORMATION), "i" (INTR_INFO_VECTOR_MASK), "i" (0x2)
			: //no clobber
		);

}*/


//---hvm_intercept_handler------------------------------------------------------
void xcihub_arch_entry(void) __attribute__((naked)){

		asm volatile (
            "pushq %%rax \r\n"
            "pushq %%rcx \r\n"
            "pushq %%rdx \r\n"
            "pushq %%rbx \r\n"
            "pushq %%rsp \r\n"
            "pushq %%rbp \r\n"
            "pushq %%rsi \r\n"
            "pushq %%rdi \r\n"

			"movq %0, %%rax \r\n"				//rax = VMCS_INFO_VMEXIT_REASON
			"vmread %%rax, %%rbx \r\n"			//ebx = VMCS[VMCS_INFO_VMEXIT_REASON]
			"cmpl %1, %%ebx \r\n"				//if (ebx == VMX_VMEXIT_EXCEPTION)
			"jne normal \r\n"					//nope, so just do normal eventhub processing
			"movq %2, %%rax \r\n"				//eax = VMCS_INFO_VMEXIT_INTERRUPT_INFORMATION
			"vmread %%rax, %%rbx \r\n"			//ebx = VMCS[VMCS_INFO_VMEXIT_INTERRUPT_INFORMATION]
			"andl %3, %%ebx \r\n"				//ebx &= INTR_INFO_VECTOR_MASK
			"cmpl %4, %%ebx \r\n"				//if (ebx == 0x2)
			"jne normal \r\n"					//nope, so just do normal eventhub processing
			"int $0x02 \r\n"					//NMI exception intercept, so trigger NMI handler
			"jmp exithub \r\n"					//skip over normal event hub processing
			"normal: \r\n"						//normal event hub processing setup

			"movq %%rsp, %%rdi\r\n"
			"call xmhf_partition_eventhub_arch_x86vmx\r\n"

			"exithub: \r\n"						//event hub epilogue to resume partition

            "popq %%rdi \r\n"
            "popq %%rsi \r\n"
            "popq %%rbp \r\n"
            "popq %%rsp \r\n"
            "popq %%rbx \r\n"
            "popq %%rdx \r\n"
            "popq %%rcx \r\n"
            "popq %%rax \r\n"

			"vmresume\r\n"

			"int $0x03\r\n"
			"hlt\r\n"
			: //no outputs
			: "i" (VMCS_INFO_VMEXIT_REASON), "i" (VMX_VMEXIT_EXCEPTION), "i" (VMCS_INFO_VMEXIT_INTERRUPT_INFORMATION), "i" (INTR_INFO_VECTOR_MASK), "i" (0x2)
			: //no clobber
		);

}




