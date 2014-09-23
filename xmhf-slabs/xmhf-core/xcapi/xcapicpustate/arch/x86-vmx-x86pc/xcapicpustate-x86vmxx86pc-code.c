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

// XMHF core API -- x86vmx arch. backend
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcapi.h>
#include <xcihub.h>



///////////////////////////////////////////////////////////////////////////////
// CPU state related APIs

static struct regs _cpustate_x86gprs[MAX_PLATFORM_CPUS];
__attribute__((aligned(4096))) static xc_cpuarchdata_x86vmx_t _cpustate_archdatavmx[MAX_PLATFORM_CPUS];


static void _cpustate_operation_cpugprs_set(context_desc_t context_desc, struct regs x86gprs){
	_cpustate_x86gprs[context_desc.cpu_desc.cpu_index].edi = x86gprs.edi;
	_cpustate_x86gprs[context_desc.cpu_desc.cpu_index].esi = x86gprs.esi;
	_cpustate_x86gprs[context_desc.cpu_desc.cpu_index].ebp = x86gprs.ebp;
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RSP, x86gprs.esp);
	_cpustate_x86gprs[context_desc.cpu_desc.cpu_index].ebx = x86gprs.ebx;
	_cpustate_x86gprs[context_desc.cpu_desc.cpu_index].edx = x86gprs.edx;
	_cpustate_x86gprs[context_desc.cpu_desc.cpu_index].ecx = x86gprs.ecx;
	_cpustate_x86gprs[context_desc.cpu_desc.cpu_index].eax = x86gprs.eax;
}

static struct regs _cpustate_operation_cpugprs_get(context_desc_t context_desc){
	struct regs x86gprs;

	x86gprs.edi = _cpustate_x86gprs[context_desc.cpu_desc.cpu_index].edi;
	x86gprs.esi = _cpustate_x86gprs[context_desc.cpu_desc.cpu_index].esi;
	x86gprs.ebp = _cpustate_x86gprs[context_desc.cpu_desc.cpu_index].ebp;
	x86gprs.esp = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_RSP);
	x86gprs.ebx = _cpustate_x86gprs[context_desc.cpu_desc.cpu_index].ebx;
	x86gprs.edx = _cpustate_x86gprs[context_desc.cpu_desc.cpu_index].edx;
	x86gprs.ecx = _cpustate_x86gprs[context_desc.cpu_desc.cpu_index].ecx;
	x86gprs.eax = _cpustate_x86gprs[context_desc.cpu_desc.cpu_index].eax;

	return x86gprs;
}


static void _cpustate_operation_desc_set(context_desc_t context_desc, xc_hypapp_arch_param_x86vmx_cpustate_desc_t desc){

	//CS, DS, ES, FS, GS and SS segments
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_SELECTOR, desc.cs.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_BASE, desc.cs.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_LIMIT, desc.cs.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_ACCESS_RIGHTS, desc.cs.access_rights);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_SELECTOR, desc.ds.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_BASE, desc.ds.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_LIMIT, desc.ds.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_ACCESS_RIGHTS, desc.ds.access_rights);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_SELECTOR, desc.es.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_BASE, desc.es.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_LIMIT, desc.es.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_ACCESS_RIGHTS, desc.es.access_rights);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_SELECTOR, desc.fs.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_BASE, desc.fs.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_LIMIT, desc.fs.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_ACCESS_RIGHTS, desc.fs.access_rights);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_SELECTOR, desc.gs.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_BASE, desc.gs.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_LIMIT, desc.gs.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_ACCESS_RIGHTS, desc.gs.access_rights);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_SELECTOR, desc.ss.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_BASE, desc.ss.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_LIMIT, desc.ss.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_ACCESS_RIGHTS, desc.ss.access_rights);
	//IDTR
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_IDTR_BASE, desc.idtr.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_IDTR_LIMIT, desc.idtr.limit);
	//GDTR
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_BASE, desc.gdtr.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_LIMIT, desc.gdtr.limit);
	//LDTR, unusable
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_BASE, desc.ldtr.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_LIMIT, desc.ldtr.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_SELECTOR, desc.ldtr.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_ACCESS_RIGHTS, desc.ldtr.access_rights);
	//TR, should be usable for VMX to work, but not used by guest
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_BASE, desc.tr.base);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_LIMIT, desc.tr.limit);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_SELECTOR, desc.tr.selector);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_ACCESS_RIGHTS, desc.tr.access_rights);


}

static xc_hypapp_arch_param_x86vmx_cpustate_desc_t _cpustate_operation_desc_get(context_desc_t context_desc){
	xc_hypapp_arch_param_x86vmx_cpustate_desc_t desc;

	//CS, DS, ES, FS, GS and SS segments
	desc.cs.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CS_SELECTOR);
	desc.cs.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CS_BASE);
	desc.cs.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CS_LIMIT);
	desc.cs.access_rights = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CS_ACCESS_RIGHTS);
	desc.ds.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_DS_SELECTOR);
	desc.ds.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_DS_BASE);
	desc.ds.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_DS_LIMIT);
	desc.ds.access_rights = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_DS_ACCESS_RIGHTS);
	desc.es.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_ES_SELECTOR);
	desc.es.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_ES_BASE);
	desc.es.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_ES_LIMIT);
	desc.es.access_rights = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_ES_ACCESS_RIGHTS);
	desc.fs.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_FS_SELECTOR);
	desc.fs.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_FS_BASE);
	desc.fs.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_FS_LIMIT);
	desc.fs.access_rights = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_FS_ACCESS_RIGHTS);
	desc.gs.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_GS_SELECTOR);
	desc.gs.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_GS_BASE);
	desc.gs.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_GS_LIMIT);
	desc.gs.access_rights = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_GS_ACCESS_RIGHTS);
	desc.ss.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_SS_SELECTOR);
	desc.ss.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_SS_BASE);
	desc.ss.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_SS_LIMIT);
	desc.ss.access_rights = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_SS_ACCESS_RIGHTS);
	//IDTR
	desc.idtr.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_IDTR_BASE);
	desc.idtr.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_IDTR_LIMIT);
	//GDTR
	desc.gdtr.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_GDTR_BASE);
	desc.gdtr.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_GDTR_LIMIT);
	//LDTR); unusable
	desc.ldtr.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_LDTR_BASE);
	desc.ldtr.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_LDTR_LIMIT);
	desc.ldtr.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_LDTR_SELECTOR);
	desc.ldtr.access_rights =xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_LDTR_ACCESS_RIGHTS);
	//TR); should be usable for VMX to work; not used by guest
	desc.tr.base = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_TR_BASE);
	desc.tr.limit = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_TR_LIMIT);
	desc.tr.selector = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_TR_SELECTOR);
	desc.tr.access_rights = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_TR_ACCESS_RIGHTS);

	return desc;
}


void xc_api_cpustate_arch_set(context_desc_t context_desc, xc_hypapp_arch_param_t ap){
	switch(ap.operation){
		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS:{
				_cpustate_operation_cpugprs_set(context_desc, ap.param.cpugprs);
				break;
		}

		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_DESC:{
				_cpustate_operation_desc_set(context_desc, ap.param.desc);
				break;
		}

		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY:{
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RIP, ap.param.activity.rip);
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ACTIVITY_STATE, ap.param.activity.activity_state);
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RFLAGS, ap.param.activity.rflags);
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_INTERRUPTIBILITY, ap.param.activity.interruptibility);
				break;
		}

		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS:{
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR0, ap.param.controlregs.cr0 );
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR0_SHADOW, ap.param.controlregs.control_cr0_shadow);
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, ap.param.controlregs.cr3 );
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR4, ap.param.controlregs.cr4 );
				break;
		}

		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_SYSENTER:{
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SYSENTER_CS, ap.param.sysenter.sysenter_cs);
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SYSENTER_ESP, ap.param.sysenter.sysenter_rsp);
				xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SYSENTER_EIP, ap.param.sysenter.sysenter_rip);
				break;
		}

		default:
			break;
	}

}

xc_hypapp_arch_param_t xc_api_cpustate_arch_get(context_desc_t context_desc, u64 operation){
	xc_hypapp_arch_param_t ap;

	switch(operation){
		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS:{
				ap.param.cpugprs = _cpustate_operation_cpugprs_get(context_desc);
				break;
		}

		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_DESC:{
				ap.param.desc = _cpustate_operation_desc_get(context_desc);
				break;
		}

		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY:{
				ap.param.activity.rip = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_RIP);
				ap.param.activity.activity_state =xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_ACTIVITY_STATE);
				ap.param.activity.rflags = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_RFLAGS);
				ap.param.activity.interruptibility = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_INTERRUPTIBILITY);
				break;
		}

		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS:{
				ap.param.controlregs.cr0 = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0);
				ap.param.controlregs.control_cr0_shadow = xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_CR0_SHADOW);
				ap.param.controlregs.cr3 = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR3);
				ap.param.controlregs.cr4 = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR4);
				break;
		}

		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_SYSENTER:{
				ap.param.sysenter.sysenter_cs = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_SYSENTER_CS);
				ap.param.sysenter.sysenter_rip = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_SYSENTER_EIP);
				ap.param.sysenter.sysenter_rsp = xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_SYSENTER_ESP);
				break;
		}

		case XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_INFOREGS:{
				ap.param.inforegs.info_vminstr_error = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMINSTR_ERROR);
				ap.param.inforegs.info_vmexit_reason = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMEXIT_REASON);
				ap.param.inforegs.info_vmexit_interrupt_information = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMEXIT_INTERRUPT_INFORMATION);
				ap.param.inforegs.info_vmexit_interrupt_error_code = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMEXIT_INTERRUPT_ERROR_CODE);
				ap.param.inforegs.info_idt_vectoring_information = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_IDT_VECTORING_INFORMATION);
				ap.param.inforegs.info_idt_vectoring_error_code = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_IDT_VECTORING_ERROR_CODE);
				ap.param.inforegs.info_vmexit_instruction_length = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMEXIT_INSTRUCTION_LENGTH);
				ap.param.inforegs.info_vmx_instruction_information = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMX_INSTRUCTION_INFORMATION);
				ap.param.inforegs.info_exit_qualification = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_EXIT_QUALIFICATION);
				ap.param.inforegs.info_io_rcx = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_IO_RCX);
				ap.param.inforegs.info_io_rsi = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_IO_RSI);
				ap.param.inforegs.info_io_rdi = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_IO_RDI);
				ap.param.inforegs.info_io_rip = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_IO_RIP);
				ap.param.inforegs.info_guest_linear_address = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_GUEST_LINEAR_ADDRESS);
				ap.param.inforegs.info_guest_paddr_full = xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_GUEST_PADDR_FULL);
				break;
		}

		default:
			break;
	}

	return ap;
}


bool xc_api_cpustate_arch_setupbasestate(context_desc_t context_desc){

	const u32 vmx_msr_area_msrs[] = {MSR_EFER, MSR_IA32_PAT, MSR_K6_STAR}; //critical MSRs that need to be saved/restored across guest VM switches
	const unsigned int vmx_msr_area_msrs_count = (sizeof(vmx_msr_area_msrs)/sizeof(vmx_msr_area_msrs[0]));	//count of critical MSRs that need to be saved/restored across VM switches
	u32 lodword, hidword;
	u64 vmcs_phys_addr = hva2spa((void*)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_vmcs_region);

	//save contents of VMX MSRs as well as MSR EFER and EFCR
	{
		u32 i;
		u32 eax, edx;
		for(i=0; i < IA32_VMX_MSRCOUNT; i++){
			rdmsr( (IA32_VMX_BASIC_MSR + i), &eax, &edx);
			_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[i] = (u64)edx << 32 | (u64) eax;
		}

		rdmsr(MSR_EFER, &eax, &edx);
		_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msr_efer = (u64)edx << 32 | (u64) eax;
		rdmsr(MSR_EFCR, &eax, &edx);
		_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msr_efcr = (u64)edx << 32 | (u64) eax;

		//_XDPRINTF_("\nCPU(0x%02x): MSR_EFER=0x%08x%08x", xc_cpu->cpuid, (u32)((u64)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msr_efer >> 32),
		//	(u32)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msr_efer);
		//_XDPRINTF_("\nCPU(0x%02x): MSR_EFCR=0x%08x%08x", xc_cpu->cpuid, (u32)((u64)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msr_efcr >> 32),
		//	(u32)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msr_efcr);
  	}

	//we require unrestricted guest support, bail out if we don't have it
	if( !( (u32)((u64)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[IA32_VMX_MSRCOUNT-1] >> 32) & 0x80 ) ){
		_XDPRINTF_("%s(%u): need unrestricted guest support but did not find any!\n", __FUNCTION__, context_desc.cpu_desc.cpu_index);
		return false;
	}

    write_cr4( read_cr4() |  CR4_VMXE);

	//enter VMX root operation using VMXON
	{
		u32 retval=0;
		u64 vmxonregion_paddr = hva2spa((void*)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_vmxon_region);
		//set VMCS rev id
		*((u32 *)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_vmxon_region) = (u32)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

		asm volatile( "vmxon %1 \n"
				 "jbe vmfail \n"
				 "movl $0x1, %%eax \n"
				 "movl %%eax, %0 \n"
				 "jmp vmsuccess \n"
				 "vmfail: \n"
				 "movl $0x0, %%eax \n"
				 "movl %%eax, %0 \n"
				 "vmsuccess: \n"
		   : "=m" (retval)
		   : "m"(vmxonregion_paddr)
		   : "eax");

		if(!retval){
			_XDPRINTF_("%s(%u): unable to enter VMX root operation\n", __FUNCTION__, cpuid);
			return false;
		}
	}

	//clear VMCS
	if(!__vmx_vmclear((u64)vmcs_phys_addr))
		return false;

	//set VMCS revision id
	*((u32 *)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_vmcs_region) = (u32)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

	//load VMPTR
	if(!__vmx_vmptrld((u64)vmcs_phys_addr))
		return false;


	//setup host state
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CR0, read_cr0());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CR4, read_cr4());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CR3, read_cr3());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CS_SELECTOR, read_segreg_cs());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_DS_SELECTOR, read_segreg_ds());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_ES_SELECTOR, read_segreg_es());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_FS_SELECTOR, read_segreg_fs());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_GS_SELECTOR, read_segreg_gs());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SS_SELECTOR, read_segreg_ss());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_TR_SELECTOR, read_tr_sel());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_GDTR_BASE, xmhf_baseplatform_arch_x86_getgdtbase());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_IDTR_BASE, xmhf_baseplatform_arch_x86_getidtbase());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_TR_BASE, xmhf_baseplatform_arch_x86_gettssbase());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_RIP, &xcihub_arch_entry);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_RSP, read_rsp());
	rdmsr(IA32_SYSENTER_CS_MSR, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_CS, lodword);
	rdmsr(IA32_SYSENTER_ESP_MSR, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_ESP, (((u64)hidword << 32) | (u64)lodword));
	rdmsr(IA32_SYSENTER_EIP_MSR, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_EIP, (((u64)hidword << 32) | (u64)lodword));
	rdmsr(IA32_MSR_FS_BASE, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_FS_BASE, (((u64)hidword << 32) | (u64)lodword) );
	rdmsr(IA32_MSR_GS_BASE, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_GS_BASE, (((u64)hidword << 32) | (u64)lodword) );

	//setup default VMX controls
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_PIN_BASED, (u32)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (u32)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_CONTROLS, (u32)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, (u32)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR]);

    //64-bit host
  	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_CONTROLS, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_EXIT_CONTROLS) | (1 << 9)) );


	//IO bitmap support
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL, hva2spa(xc_api_trapmask_arch_gettrapmaskbuffer(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_TRAP_IO)));
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL, hva2spa( (xc_api_trapmask_arch_gettrapmaskbuffer(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_TRAP_IO) + PAGE_SIZE_4K) ));
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 25)) );

	//Critical MSR load/store
	{
		u32 i;
		msr_entry_t *hmsr = (msr_entry_t *)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msr_area_host_region;
		msr_entry_t *gmsr = (msr_entry_t *)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msr_area_guest_region;

		//store host and guest initial values of the critical MSRs
		for(i=0; i < vmx_msr_area_msrs_count; i++){
			u32 msr, eax, edx;
			msr = vmx_msr_area_msrs[i];
			rdmsr(msr, &eax, &edx);

			//host MSR values will be what we get from RDMSR
			hmsr[i].index = msr;
			hmsr[i].data = ((u64)edx << 32) | (u64)eax;

            //adjust and populate guest MSR values according to the MSR
			gmsr[i].index = msr;
			gmsr[i].data = ((u64)edx << 32) | (u64)eax;
			switch(msr){
                case MSR_EFER:{
                    gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_LME);
                    gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_LMA);
                    gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_SCE);
                    gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_NXE);
                }
                break;

                default:
                    break;
			}

		}

		//host MSR load on exit, we store it ourselves before entry
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL, hva2spa((void*)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msr_area_host_region));
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);

		//guest MSR load on entry, store on exit
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, hva2spa((void*)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msr_area_guest_region));
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, hva2spa((void*)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msr_area_guest_region));
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, vmx_msr_area_msrs_count);

	}


	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_PAGEFAULT_ERRORCODE_MASK, 0x00000000);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_PAGEFAULT_ERRORCODE_MATCH, 0x00000000);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EXCEPTION_BITMAP, 0);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR3_TARGET_COUNT, 0);


	//activate secondary processor controls
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, (u32)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (u32) (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 31)) );

	//setup unrestricted guest
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (u64)(1 << 7)) );

	//setup VMCS link pointer
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_VMCS_LINK_POINTER_FULL, 0xFFFFFFFFFFFFFFFFULL);

	//setup NMI intercept for core-quiescing
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_PIN_BASED, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_PIN_BASED) | (u64)(1 << 3) ) );

	//trap access to CR0 fixed 1-bits
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR0_MASK, (u32)(((((u32)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR] & ~(CR0_PE)) & ~(CR0_PG)) | CR0_CD) | CR0_NW) );
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR0_SHADOW, xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0));

	//trap access to CR4 fixed bits (this includes the VMXE bit)
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR4_MASK, (u32)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR4_SHADOW, (u64)CR4_VMXE);

	//setup memory protection
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (u64)(1 <<1) | (u64)(1 << 5)) );
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VPID, 1);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_FULL, (hva2spa(xc_api_hpt_arch_gethptroot(context_desc)) | (u64)0x1E) );
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) & (u64)~(1 << 15) & (u64)~(1 << 16)) );

	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR0, (u32)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR4, (u32)_cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);

	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_EXCEPTION_ERRORCODE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_INTERRUPTION_INFORMATION, 0);

	/*_XDPRINTF_("%s: vmcs pinbased=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_PIN_BASED));
	_XDPRINTF_("%s: pinbase MSR=%016llx\n", __FUNCTION__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR]);
	_XDPRINTF_("%s: cpu_based vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED));
	_XDPRINTF_("%s: cpu_based MSR=%016llx\n", __FUNCTION__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR]);
	_XDPRINTF_("%s: seccpu_based vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED));
	_XDPRINTF_("%s: seccpu_based MSR=%016llx\n", __FUNCTION__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
	_XDPRINTF_("%s: entrycontrols vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS));
	_XDPRINTF_("%s: entrycontrols MSR=%016llx\n", __FUNCTION__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR]);
	_XDPRINTF_("%s: exitcontrols vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_EXIT_CONTROLS));
	_XDPRINTF_("%s: exitcontrols MSR=%016llx\n", __FUNCTION__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR]);
	_XDPRINTF_("%s: iobitmapa vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL));
	_XDPRINTF_("%s: iobitmapb vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap load vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap store vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap exit load vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL));
	_XDPRINTF_("%s: ept pointer vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_EPT_POINTER_FULL));
	_XDPRINTF_("%s: CR0 mask MSR=%016llx\n", __FUNCTION__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR]);
	_XDPRINTF_("%s: CR0 mask vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_CR0_MASK));
	_XDPRINTF_("%s: CR4 mask MSR=%016llx\n", __FUNCTION__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
	_XDPRINTF_("%s: CR4 mask vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_CR4_MASK));
	_XDPRINTF_("%s: CR0 shadow vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_CR0_SHADOW));
	_XDPRINTF_("%s: CR4 shadow vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_CR4_SHADOW));
    */

    return true;
}

