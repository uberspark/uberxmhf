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
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_ihub.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_gcpustate.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_sysdata.h>

/*
 * xcihub_rg_e820emulation -- rich guest E820 memory-map emulation
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
bool xcihub_rg_e820emulation(uint32_t cpuid, uint32_t src_slabid){
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp = (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;
	xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs = (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
	slab_params_t splusysd;
	uxmhf_uapi_sysdata_e820getmaxindex_t *usysd_getmaxindex = (uxmhf_uapi_sysdata_e820getmaxindex_t *)splusysd.in_out_params;
	uxmhf_uapi_sysdata_e820getentryforindex_t *usysd_getentryforindex = (uxmhf_uapi_sysdata_e820getentryforindex_t *)splusysd.in_out_params;
	uint32_t g_cs_base, g_eip;
	uint32_t g_es_base, g_ss_base;
	uint32_t g_esp;
	uint16_t g_flags;
	uint32_t e820_maxindex;
	uint16_t orig_int15h_ip, orig_int15h_cs;
	x86regs_t r;

	//clear out slab_params
	uberspark_uobjrtl_crt__memset(&spl, 0, sizeof(spl));
	uberspark_uobjrtl_crt__memset(&splusysd, 0, sizeof(splusysd));

	//setup uobj params
	spl.cpuid = cpuid;
	spl.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
	splusysd.cpuid = cpuid;
	splusysd.src_slabid = XMHFGEEC_SLAB_XC_IHUB;
	splusysd.dst_slabid = XMHFGEEC_SLAB_UAPI_SYSDATA;

	//read CS base and RIP
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
	gcpustate_vmrwp->encoding = VMCS_GUEST_CS_BASE;
	XMHF_SLAB_CALLNEW(&spl);
	g_cs_base= gcpustate_vmrwp->value;

	gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
	XMHF_SLAB_CALLNEW(&spl);
	g_eip = gcpustate_vmrwp->value;

	//check if this is a E820 emulation VMCALL, if not return false
	if ( !( (g_cs_base == (VMX_UG_E820HOOK_CS << 4)) && (g_eip == VMX_UG_E820HOOK_IP) ) )
		return false;

	//read ES.base, SS.base and ESP
	gcpustate_vmrwp->encoding = VMCS_GUEST_ES_BASE;
	XMHF_SLAB_CALLNEW(&spl);
	g_es_base= gcpustate_vmrwp->value;

	gcpustate_vmrwp->encoding = VMCS_GUEST_SS_BASE;
	XMHF_SLAB_CALLNEW(&spl);
	g_ss_base= gcpustate_vmrwp->value;

	gcpustate_vmrwp->encoding = VMCS_GUEST_RSP;
	XMHF_SLAB_CALLNEW(&spl);
	g_esp = gcpustate_vmrwp->value;

	//read GPRs
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
	XMHF_SLAB_CALLNEW(&spl);
	memcpy(&r, &gcpustate_gprs->gprs, sizeof(x86regs_t));


	//if E820 service then...
	if((uint16_t)r.eax == 0xE820){
		//AX=0xE820, EBX=continuation value, 0 for first call
		//ES:DI pointer to buffer, ECX=buffer size, EDX='SMAP'
		//return value, CF=0 indicated no error, EAX='SMAP'
		//ES:DI left untouched, ECX=size returned, EBX=next continuation value
		//EBX=0 if last descriptor
		_XDPRINTF_("%s[%u]: INT 15(e820): AX=0x%04x, EDX=0x%08x, EBX=0x%08x\n", __func__, cpuid,
					(uint16_t)r.eax, (uint32_t)r.edx, (uint32_t)r.ebx);
		_XDPRINTF_("%s[%u]:   ECX=0x%08x, ES(base)=0x%08x, DI=0x%04x\n", __func__, cpuid,
				(uint32_t)r.ecx, g_es_base, (uint16_t)r.edi);

		//read maximum E820 index
		splusysd.dst_uapifn = UXMHF_UAPI_SYSDATA_E820GETMAXINDEX;
		XMHF_SLAB_CALLNEW(&splusysd);
		e820_maxindex = usysd_getmaxindex->index;

		if( (r.edx == 0x534D4150UL) && (r.ebx < e820_maxindex) ){

			splusysd.dst_uapifn = UXMHF_UAPI_SYSDATA_E820GETENTRYFORINDEX;
			usysd_getentryforindex->index = r.ebx;
			XMHF_SLAB_CALLNEW(&splusysd);

			CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmem_copy_obj2sys, (uint32_t)(g_es_base+(uint16_t)r.edi), &(usysd_getentryforindex->baseaddr_low), 20);

			_XDPRINTF_("%s[%u]:   base: 0x%08x%08x  len=0x%08x%08x, t=0x%08x\n", __func__, cpuid,
					usysd_getentryforindex->baseaddr_high, usysd_getentryforindex->baseaddr_low,
					usysd_getentryforindex->length_high, usysd_getentryforindex->length_low,
					usysd_getentryforindex->type);

			r.ecx=20;

			//set EAX to 'SMAP' as required by the service call
			r.eax=r.edx;

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

			//grab guest eflags on guest stack
			g_flags = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmemaccess_readu16, ((uint32_t)g_ss_base + (uint16_t)g_esp + 0x4));

			//increment e820 descriptor continuation value
			r.ebx=r.ebx+1;

			if(r.ebx > (e820_maxindex-1) ){
				//we have reached the last record, so set CF and make EBX=0
				r.ebx=0;
				g_flags |= (uint16_t)EFLAGS_CF;
			}else{
				//we still have more records, so clear CF
				g_flags &= ~(uint16_t)EFLAGS_CF;
			}

			CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmemaccess_writeu16, ((uint32_t)g_ss_base + (uint16_t)g_esp + 0x4), g_flags);

		}else{	//invalid state specified during INT 15 E820, halt
			_XDPRINTF_("%s[%u]: INT15 (E820), invalid state specified by guest. Halting!\n", __func__, cpuid);
			CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
		}

		//update GPRs
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE;
		memcpy(&gcpustate_gprs->gprs, &r, sizeof(x86regs_t));
		XMHF_SLAB_CALLNEW(&spl);

		//update RIP to execute the IRET following the VMCALL instruction
		//effectively returning from the INT 15 call made by the guest
		g_eip+=3;
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
		gcpustate_vmrwp->value = g_eip;
		XMHF_SLAB_CALLNEW(&spl);

	}else{

		//ok, this is some other INT 15h service, so simply chain to the original
		//INT 15h handler
		orig_int15h_ip = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmemaccess_readu16, 0x4AC+0x4);
		orig_int15h_cs = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmemaccess_readu16, 0x4AC+0x6);

		//update VMCS with the CS and IP and let go
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
		gcpustate_vmrwp->value = orig_int15h_ip;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_CS_SELECTOR;
		gcpustate_vmrwp->value = orig_int15h_cs;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_CS_BASE;
		gcpustate_vmrwp->value = (orig_int15h_cs * 16);
		XMHF_SLAB_CALLNEW(&spl);

	}

	//write interruptibility = 0
	spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
	gcpustate_vmrwp->encoding = VMCS_GUEST_INTERRUPTIBILITY;
	gcpustate_vmrwp->value = 0;
	XMHF_SLAB_CALLNEW(&spl);

	//we handled a VMCALL which was E820 emulation
	return true;
}



