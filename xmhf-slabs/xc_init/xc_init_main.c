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


/*
 * XMHF core initialization slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <geec_sentinel.h>
#include <xc.h>
#include <uapi_gcpustate.h>
#include <xh_hyperdep.h>
#include <xh_syscalllog.h>
#include <xh_ssteptrace.h>
#include <xh_aprvexec.h>

#include <xc_init.h>


/*
//////
// test slab invocation fragment
//////
static void xcinit_do_test(slab_params_t *sp){
	slab_params_t spl;
	spl.src_slabid = XMHFGEEC_SLAB_XC_INIT;
	spl.dst_slabid = XMHFGEEC_SLAB_XC_TESTSLAB;
	spl.cpuid = sp->cpuid;
	spl.dst_uapifn = 0;
	spl.in_out_params[0] = 0xF00DDEAD;
	_XDPRINTF_("XC_INIT[%u]: proceeding to call test slab, esp=%x\n", (u16)sp->cpuid, CASM_FUNCCALL(read_esp,CASM_NOPARAM));
	XMHF_SLAB_CALLNEW(&spl);
	_XDPRINTF_("XC_INIT[%u]: came back from test slab, esp=%x\n", (u16)sp->cpuid, CASM_FUNCCALL(read_esp,CASM_NOPARAM));
	_XDPRINTF_("XC_INIT[%u]: called test slab, return value=%x\n",
			   (u16)sp->cpuid, spl.in_out_params[1]);
}
*/

/*
//////
// call guest uobj
//////
static void xcinit_do_callguest(slab_params_t *sp){
	slab_params_t spl;

	memset(&spl, 0, sizeof(spl));
	spl.cpuid = sp->cpuid;
	spl.src_slabid = XMHFGEEC_SLAB_XC_INIT;
	spl.dst_slabid = XMHFGEEC_SLAB_XG_BENCHGUEST;
	XMHF_SLAB_CALLNEW(&spl);
}
*/


//////
// call guest uobj
//////
static void xcinit_do_callguest(slab_params_t *sp){
	slab_params_t spl;

	memset(&spl, 0, sizeof(spl));
	spl.cpuid = sp->cpuid;
	spl.src_slabid = XMHFGEEC_SLAB_XC_INIT;
	spl.dst_slabid = XMHFGEEC_SLAB_XG_RICHGUEST;
	XMHF_SLAB_CALLNEW(&spl);

}




//////
// setup guest uobj
//////
static void xcinit_setup_guest(slab_params_t *sp, bool isbsp){



	//setup guest slab VMCS state
	{
		slab_params_t spl;
		xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp =
			(xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;

		spl.cpuid = sp->cpuid;
		spl.src_slabid = XMHFGEEC_SLAB_XC_INIT;
		spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;

		//generic guest VMCS setup
		gcpustate_vmrwp->encoding = VMCS_CONTROL_CR4_SHADOW;
		gcpustate_vmrwp->value =(u64)CR4_VMXE;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_PAGEFAULT_ERRORCODE_MASK;
		gcpustate_vmrwp->value = 0x00000000;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_PAGEFAULT_ERRORCODE_MATCH;
		gcpustate_vmrwp->value = 0x00000000;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_EXCEPTION_BITMAP;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_CR3_TARGET_COUNT;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_VM_ENTRY_EXCEPTION_ERRORCODE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_VM_ENTRY_INTERRUPTION_INFORMATION;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		//GDTR
		gcpustate_vmrwp->encoding = VMCS_GUEST_GDTR_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_GDTR_LIMIT;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		//IDTR
		gcpustate_vmrwp->encoding = VMCS_GUEST_IDTR_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_IDTR_LIMIT;
		gcpustate_vmrwp->value = 0x3ff;
		XMHF_SLAB_CALLNEW(&spl);

		//LDTR, unusable
		gcpustate_vmrwp->encoding = VMCS_GUEST_LDTR_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_LDTR_LIMIT;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_LDTR_SELECTOR;
		gcpustate_vmrwp->value = 0 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_LDTR_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0x10000;
		XMHF_SLAB_CALLNEW(&spl);

		//TR
		gcpustate_vmrwp->encoding = VMCS_GUEST_TR_BASE ;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_TR_LIMIT;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_TR_SELECTOR;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_TR_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0x83;
		XMHF_SLAB_CALLNEW(&spl);

		//CS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_CS_SELECTOR;
		gcpustate_vmrwp->value = 0x0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_CS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_CS_LIMIT;
		gcpustate_vmrwp->value = 0x0000FFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_CS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0x0093;
		XMHF_SLAB_CALLNEW(&spl);

		//DS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_DS_SELECTOR;
		gcpustate_vmrwp->value = 0x0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_DS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_DS_LIMIT;
		gcpustate_vmrwp->value = 0x0000FFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_DS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0x0093;
		XMHF_SLAB_CALLNEW(&spl);

		//ES segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_ES_SELECTOR;
		gcpustate_vmrwp->value = 0x0 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_ES_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_ES_LIMIT;
		gcpustate_vmrwp->value = 0x0000FFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_ES_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0x0093;
		XMHF_SLAB_CALLNEW(&spl);

		//FS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_FS_SELECTOR;
		gcpustate_vmrwp->value = 0x0 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_FS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_FS_LIMIT;
		gcpustate_vmrwp->value = 0x0000FFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_FS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0x0093;
		XMHF_SLAB_CALLNEW(&spl);

		//GS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_GS_SELECTOR;
		gcpustate_vmrwp->value = 0x0 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_GS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_GS_LIMIT;
		gcpustate_vmrwp->value = 0x0000FFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_GS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0x0093;
		XMHF_SLAB_CALLNEW(&spl);

		//SS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_SS_SELECTOR;
		gcpustate_vmrwp->value = 0x0 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_SS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_SS_LIMIT;
		gcpustate_vmrwp->value = 0x0000FFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_SS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0x0093;
		XMHF_SLAB_CALLNEW(&spl);

		//guest EIP and activity state
		if(isbsp){
			_XDPRINTF_("%s[%u]: BSP: setting RIP and activity state for boot\n", __func__, (u16)sp->cpuid);
			gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
			gcpustate_vmrwp->value = 0x00007C00;
			XMHF_SLAB_CALLNEW(&spl);

			gcpustate_vmrwp->encoding = VMCS_GUEST_ACTIVITY_STATE;
			gcpustate_vmrwp->value = 0;
			XMHF_SLAB_CALLNEW(&spl);
		}else{
			gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
			gcpustate_vmrwp->value = 0x00000000;
			XMHF_SLAB_CALLNEW(&spl);

			gcpustate_vmrwp->encoding = VMCS_GUEST_ACTIVITY_STATE;
			gcpustate_vmrwp->value = 3;	//wait-for-SIPI
			XMHF_SLAB_CALLNEW(&spl);
		}

		//interruptibility
		gcpustate_vmrwp->encoding = VMCS_GUEST_INTERRUPTIBILITY;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		//guest ESP
		gcpustate_vmrwp->encoding = VMCS_GUEST_RSP;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		//guest RFLAGS
		gcpustate_vmrwp->encoding = VMCS_GUEST_RFLAGS;
		gcpustate_vmrwp->value = ((((0 & ~((1<<3)|(1<<5)|(1<<15)) ) | (1 <<1)) | (1<<9)) & ~(1<<14));
		XMHF_SLAB_CALLNEW(&spl);

		//other guest GPRS (EAX, EBX, ECX, EDX, ESI, EDI, EBP)
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE;
		spl.in_out_params[0] = 0;	//EDI
		spl.in_out_params[1] = 0;	//ESI
		spl.in_out_params[2] = 0;	//EBP
		spl.in_out_params[3] = 0;	//Reserved (ESP)
		spl.in_out_params[4] = 0;	//EBX
		spl.in_out_params[5] = 0;	//EDX
		spl.in_out_params[6] = 0;	//ECX
		spl.in_out_params[7] = 0;	//EAX
		XMHF_SLAB_CALLNEW(&spl);

		//guest control registers (CR0, CR3 and CR0_SHADOW)
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
		gcpustate_vmrwp->encoding = VMCS_GUEST_CR0;
		XMHF_SLAB_CALLNEW(&spl);
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_GUEST_CR0;
		gcpustate_vmrwp->value = gcpustate_vmrwp->value & ~(CR0_PE) & ~(CR0_PG);
		XMHF_SLAB_CALLNEW(&spl);
		gcpustate_vmrwp->encoding = VMCS_GUEST_CR3;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
		gcpustate_vmrwp->encoding = VMCS_GUEST_CR0;
		XMHF_SLAB_CALLNEW(&spl);
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_CONTROL_CR0_SHADOW;
		XMHF_SLAB_CALLNEW(&spl);

	}



}

/*
//////
// setup guest uobj
//////
static void xcinit_setup_guest(slab_params_t *sp, bool isbsp){
	__attribute__(( aligned(16) )) static u64 _xcguestslab_init_gdt[]  = {
		0x0000000000000000ULL,	//NULL descriptor
		0x00cf9b000000ffffULL,	//CPL-0 32-bit code descriptor (CS32)
		0x00cf93000000ffffULL,	//CPL-0 32-bit data descriptor (DS/SS/ES/FS/GS)
		0x0000000000000000ULL,	//NULL descriptor
	};
    u32 guest_slab_header_paddr = xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XG_BENCHGUEST].slab_physmem_extents[1].addr_start;
    u32 guest_slab_gdt_paddr = guest_slab_header_paddr + offsetof(guest_slab_header_t, gdt);
    u32 guest_slab_magic_paddr = guest_slab_header_paddr + offsetof(guest_slab_header_t, magic);
    u32 guest_slab_magic;

	//get and dump slab header magic
	{
		CASM_FUNCCALL(xmhfhw_sysmemaccess_copy, &guest_slab_magic,
		guest_slab_magic_paddr, sizeof(guest_slab_magic));
		_XDPRINTF_("%s[%u]: guest slab header at=%x\n", __func__, (u16)sp->cpuid, guest_slab_header_paddr);
		_XDPRINTF_("%s[%u]: guest slab header magic=%x\n", __func__, (u16)sp->cpuid, guest_slab_magic);
	}


	//initialize guest slab gdt
	{
		CASM_FUNCCALL(xmhfhw_sysmemaccess_copy, guest_slab_gdt_paddr,
		&_xcguestslab_init_gdt, sizeof(_xcguestslab_init_gdt));
	}

	//setup guest slab VMCS state
	{
		slab_params_t spl;
		xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp =
			(xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;

		spl.cpuid = sp->cpuid;
		spl.src_slabid = XMHFGEEC_SLAB_XC_INIT;
		spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;

		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_GUEST_GDTR_BASE;
		gcpustate_vmrwp->value = guest_slab_gdt_paddr;

		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_GDTR_LIMIT;
		gcpustate_vmrwp->value =  (sizeof(_xcguestslab_init_gdt)-1);

		XMHF_SLAB_CALLNEW(&spl);


		//more guest-specific state setup
		gcpustate_vmrwp->encoding = VMCS_CONTROL_CR4_SHADOW;
		gcpustate_vmrwp->value =(u64)CR4_VMXE;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_PAGEFAULT_ERRORCODE_MASK;
		gcpustate_vmrwp->value = 0x00000000;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_PAGEFAULT_ERRORCODE_MATCH;
		gcpustate_vmrwp->value = 0x00000000;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_EXCEPTION_BITMAP;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_CR3_TARGET_COUNT;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_VM_ENTRY_EXCEPTION_ERRORCODE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_VM_ENTRY_INTERRUPTION_INFORMATION;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_RSP;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_ACTIVITY_STATE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_RFLAGS;
		gcpustate_vmrwp->value = (1 <<1) | (EFLAGS_IOPL);
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_INTERRUPTIBILITY;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		//IDTR
		gcpustate_vmrwp->encoding = VMCS_GUEST_IDTR_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_IDTR_LIMIT;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		//LDTR, unusable
		gcpustate_vmrwp->encoding = VMCS_GUEST_LDTR_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_LDTR_LIMIT;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_LDTR_SELECTOR;
		gcpustate_vmrwp->value = 0 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_LDTR_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0x10000;
		XMHF_SLAB_CALLNEW(&spl);

		//guest CR3
		gcpustate_vmrwp->encoding = VMCS_GUEST_CR3;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		//TR
		gcpustate_vmrwp->encoding = VMCS_GUEST_TR_BASE ;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_TR_LIMIT;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_TR_SELECTOR;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_TR_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0x8B;
		XMHF_SLAB_CALLNEW(&spl);

		//CS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_CS_SELECTOR;
		gcpustate_vmrwp->value = 0x8;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_CS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_CS_LIMIT;
		gcpustate_vmrwp->value = 0xFFFFFFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_CS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0xc09b;
		XMHF_SLAB_CALLNEW(&spl);

		//DS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_DS_SELECTOR;
		gcpustate_vmrwp->value = 0x10;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_DS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_DS_LIMIT;
		gcpustate_vmrwp->value = 0xFFFFFFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_DS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0xc093;
		XMHF_SLAB_CALLNEW(&spl);

		//ES segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_ES_SELECTOR;
		gcpustate_vmrwp->value = 0x10 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_ES_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_ES_LIMIT;
		gcpustate_vmrwp->value = 0xFFFFFFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_ES_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0xc093;
		XMHF_SLAB_CALLNEW(&spl);

		//FS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_FS_SELECTOR;
		gcpustate_vmrwp->value = 0x10 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_FS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_FS_LIMIT;
		gcpustate_vmrwp->value = 0xFFFFFFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_FS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0xc093;
		XMHF_SLAB_CALLNEW(&spl);

		//GS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_GS_SELECTOR;
		gcpustate_vmrwp->value = 0x10 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_GS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_GS_LIMIT;
		gcpustate_vmrwp->value = 0xFFFFFFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_GS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0xc093;
		XMHF_SLAB_CALLNEW(&spl);

		//SS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_SS_SELECTOR;
		gcpustate_vmrwp->value = 0x10 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_SS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_SS_LIMIT;
		gcpustate_vmrwp->value = 0xFFFFFFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_SS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0xc093;
		XMHF_SLAB_CALLNEW(&spl);


		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
		gcpustate_vmrwp->encoding = VMCS_GUEST_CR0;
		XMHF_SLAB_CALLNEW(&spl);
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_GUEST_CR0;
		gcpustate_vmrwp->value &= ~(CR0_PG);
		XMHF_SLAB_CALLNEW(&spl);

		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
		gcpustate_vmrwp->encoding = VMCS_GUEST_CR0;
		XMHF_SLAB_CALLNEW(&spl);
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_CONTROL_CR0_SHADOW;
		XMHF_SLAB_CALLNEW(&spl);

	}

}
*/


//////
// invoke hypapp initialization callbacks
//////
static u32 xc_hcbinvoke(u32 src_slabid, u32 cpuid, u32 cbtype, u32 cbqual, u32 guest_slab_index){
    u32 status = XC_HYPAPPCB_CHAIN;
    u32 i;
    slab_params_t spl;
    xc_hypappcb_params_t *hcbp = (xc_hypappcb_params_t *)&spl.in_out_params[0];

    spl.src_slabid = src_slabid;
    spl.cpuid = cpuid;
    spl.dst_uapifn = 0;
    hcbp->cbtype=cbtype;
    hcbp->cbqual=cbqual;
    hcbp->guest_slab_index=guest_slab_index;

    for(i=0; i < HYPAPP_INFO_TABLE_NUMENTRIES; i++){
        if(_xcihub_hypapp_info_table[i].cbmask & XC_HYPAPPCB_MASK(cbtype)){
            spl.dst_slabid = _xcihub_hypapp_info_table[i].xmhfhic_slab_index;
            XMHF_SLAB_CALLNEW(&spl);
            if(hcbp->cbresult == XC_HYPAPPCB_NOCHAIN){
                status = XC_HYPAPPCB_NOCHAIN;
                break;
            }
        }
    }

    return status;
}


//////
// setup E820 hook for guest uobj
//////
static void	xcinit_e820initializehooks(void){
		u16 orig_int15h_ip, orig_int15h_cs;

		//implant VMCALL followed by IRET at 0040:04AC
		CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu8, 0x4ac, 0x0f); //VMCALL
		CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu8, 0x4ad, 0x01);
		CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu8, 0x4ae, 0xc1);
		CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu8, 0x4af, 0xcf); //IRET

		//store original INT 15h handler CS:IP following VMCALL and IRET
		orig_int15h_ip = CASM_FUNCCALL(xmhfhw_sysmemaccess_readu16, 0x54);
		orig_int15h_cs = CASM_FUNCCALL(xmhfhw_sysmemaccess_readu16, 0x56);
		CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu16, 0x4b0, orig_int15h_ip); //original INT 15h IP
		CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu16, 0x4b2, orig_int15h_cs); //original INT 15h CS

		//point IVT INT15 handler to the VMCALL instruction
		CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu16, 0x54, 0x00ac);
		CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu16, 0x56, 0x0040);
}


//////
// copy guest boot module into appropriate location
//////
static void	xcinit_copyguestbootmodule(u32 g_bm_base, u32 g_bm_size){
/*	u8 rg_bootcode[]  = {
		0x0F, 0x01, 0xC1, //VMCALL
		0xEB, 0xFE,	//JMP EIP
		0x90,		//NOP
		0x90,		//NOP
	};
	u8 rg_bootcode_verif[7];

	//write boot code to guest boot area
	_XDPRINTF_("%s: BSP: writing boot-code...\n", __func__);
	CASM_FUNCCALL(xmhfhw_sysmem_copy_obj2sys, (u8 *)0x00007C00, &rg_bootcode, sizeof(rg_bootcode));
	_XDPRINTF_("%s: BSP: boot-code written successfully\n", __func__);
	_XDPRINTF_("%s: BSP: reading boot-code...\n", __func__);
	CASM_FUNCCALL(xmhfhw_sysmem_copy_sys2obj, &rg_bootcode_verif, (u8 *)0x00007C00, sizeof(rg_bootcode_verif));
	_XDPRINTF_("%s: BSP: boot-code: %02x %02x %02x %02x...\n", __func__,
			rg_bootcode_verif[0], rg_bootcode_verif[1], rg_bootcode_verif[2], rg_bootcode_verif[3]);
*/

	_XDPRINTF_("%s: boot-module at 0x%08x, size=0x%08x (%u) bytes\n", __func__, g_bm_base, g_bm_size, g_bm_size);
	CASM_FUNCCALL(xmhfhw_sysmemaccess_copy, 0x00007C00, g_bm_base, g_bm_size);


}


void slab_main(slab_params_t *sp){
    bool isbsp = xmhfhw_lapic_isbsp();

    #if defined (__DEBUG_SERIAL__)
	static volatile u32 cpucount=0;
	#endif //__DEBUG_SERIAL__


    //grab lock
    CASM_FUNCCALL(spin_lock,&__xcinit_smplock);

    _XDPRINTF_("XC_INIT[%u]: got control: ESP=%08x\n", (u16)sp->cpuid, CASM_FUNCCALL(read_esp,CASM_NOPARAM));
    _XDPRINTF_("XC_INIT[%u]: HYPAPP_INFO_TABLE_NUMENTRIES=%u\n", (u16)sp->cpuid, HYPAPP_INFO_TABLE_NUMENTRIES);

    //test uboj invocation
    //xcinit_do_test(sp);

    //plant int 15h redirection code for E820 reporting and copy boot-module
    if(isbsp){
        _XDPRINTF_("XC_INIT[%u]: BSP: Proceeding to install E820 redirection...\n", (u16)sp->cpuid);
    	xcinit_e820initializehooks();
        _XDPRINTF_("XC_INIT[%u]: BSP: E820 redirection enabled\n", (u16)sp->cpuid);
        _XDPRINTF_("XC_INIT[%u]: BSP: Proceeding to copy guest boot-module...\n", (u16)sp->cpuid);
    	xcinit_copyguestbootmodule(sp->in_out_params[0], sp->in_out_params[1]);
        _XDPRINTF_("XC_INIT[%u]: BSP: guest boot-module copied\n", (u16)sp->cpuid);
    }

    //setup guest uobj state
    xcinit_setup_guest(sp, isbsp);

    //invoke hypapp initialization callbacks
    xc_hcbinvoke(XMHFGEEC_SLAB_XC_INIT, sp->cpuid, XC_HYPAPPCB_INITIALIZE, 0, XMHFGEEC_SLAB_XG_RICHGUEST);


    _XDPRINTF_("XC_INIT[%u]: Proceeding to call guest: ESP=%08x, eflags=%08x\n", (u16)sp->cpuid,
    		CASM_FUNCCALL(read_esp,CASM_NOPARAM), CASM_FUNCCALL(read_eflags, CASM_NOPARAM));

	#if defined (__DEBUG_SERIAL__)
	cpucount++;
	#endif //__DEBUG_SERIAL__

    //release lock
    CASM_FUNCCALL(spin_unlock,&__xcinit_smplock);


    #if defined (__DEBUG_SERIAL__)
    while(cpucount < __XMHF_CONFIG_DEBUG_SERIAL_MAXCPUS__);
    #endif //__DEBUG_SERIAL__

    //call guest
    xcinit_do_callguest(sp);


    //_XDPRINTF_("%s[%u]: Should  never get here.Halting!\n", __func__, (u16)sp->cpuid);
    HALT();

    return;
}



/*    //debug
    _XDPRINTF_("Halting!\n");
    _XDPRINTF_("XMHF Tester Finished!\n");
    HALT();
*/






#if 0


	/*_XDPRINTF_("%s: vmcs pinbased=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_PIN_BASED));
	_XDPRINTF_("%s: pinbase MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR]);
	_XDPRINTF_("%s: cpu_based vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_CPU_BASED));
	_XDPRINTF_("%s: cpu_based MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR]);
	_XDPRINTF_("%s: seccpu_based vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_SECCPU_BASED));
	_XDPRINTF_("%s: seccpu_based MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
	_XDPRINTF_("%s: entrycontrols vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_ENTRY_CONTROLS));
	_XDPRINTF_("%s: entrycontrols MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR]);
	_XDPRINTF_("%s: exitcontrols vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_EXIT_CONTROLS));
	_XDPRINTF_("%s: exitcontrols MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR]);
	_XDPRINTF_("%s: iobitmapa vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL));
	_XDPRINTF_("%s: iobitmapb vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap load vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap store vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap exit load vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL));
	_XDPRINTF_("%s: ept pointer vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_EPT_POINTER_FULL));

	_XDPRINTF_("%s: CR0 vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR0));
	_XDPRINTF_("%s: CR4 vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR4));
	_XDPRINTF_("%s: CR0 mask vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR0_MASK));
	_XDPRINTF_("%s: CR4 mask vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR4_MASK));
	_XDPRINTF_("%s: CR0 shadow vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR0_SHADOW));
	_XDPRINTF_("%s: CR4 shadow vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR4_SHADOW));
	*/


	//MSR bitmap support
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_MSR_BITMAPS_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msrbitmaps_region );
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 28)) );

	//setup NMI intercept for core-quiescing
	//XXX: needs to go in xcinit/richguest slab
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_PIN_BASED, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_PIN_BASED) | (u64)(1 << 3) ) );


        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR4, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR4) | CR4_PAE | CR4_PSE) );

        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 9)) );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 15)) );

        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE0_FULL, _guestslab1_init_pdpt[0] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE1_FULL, _guestslab1_init_pdpt[1] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE2_FULL, _guestslab1_init_pdpt[2] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE3_FULL, _guestslab1_init_pdpt[3] );


        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, &_guestslab1_init_pml4t );



    /*
    x86_64
    //64-bit host
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_CONTROLS, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_EXIT_CONTROLS) | (1 << 9)) );
    */

/*
    //64-bit specific guest slab setup
    {

        //Critical MSR load/store
        {
            u32 i;
            msr_entry_t *hmsr = (msr_entry_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region;
            msr_entry_t *gmsr = (msr_entry_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region;

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
                        //gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_LME);
                        //gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_LMA);
                        //gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_SCE);
                        //gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_NXE);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_IA32_EFER_FULL, gmsr[i].data);

                    }
                    break;

                    default:
                        break;
                }

            }

            //host MSR load on exit, we store it ourselves before entry
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL, (void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);

            //guest MSR load on entry, store on exit
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, (void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, (void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, vmx_msr_area_msrs_count);

        }


 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR4, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR4) | CR4_PAE | CR4_PSE) );

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 9)) );
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 15)) );

        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE0_FULL, _guestslab1_init_pdpt[0] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE1_FULL, _guestslab1_init_pdpt[1] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE2_FULL, _guestslab1_init_pdpt[2] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE3_FULL, _guestslab1_init_pdpt[3] );


        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, &_guestslab1_init_pml4t );


        //TR, should be usable for VMX to work, but not used by guest
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_LIMIT, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_SELECTOR, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_ACCESS_RIGHTS, 0x8B);

        //CS, DS, ES, FS, GS and SS segments
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_SELECTOR, 0x8);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_ACCESS_RIGHTS, 0xa09b);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_ACCESS_RIGHTS, 0xa093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_ACCESS_RIGHTS, 0xa093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_ACCESS_RIGHTS, 0xa093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_ACCESS_RIGHTS, 0xa093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_ACCESS_RIGHTS, 0xa093);


        //GDTR
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_BASE, &_guestslab1_init_gdt_start);
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_LIMIT, (sizeof(_guestslab1_init_gdt_start)-1) );


    }
*/



    _xcinit_dotests(cpuid);

    _XDPRINTF_("%s[%u]: Should  never get here.Halting!\n",
        __func__, (u32)cpuid);

    HALT();


#endif // 0
