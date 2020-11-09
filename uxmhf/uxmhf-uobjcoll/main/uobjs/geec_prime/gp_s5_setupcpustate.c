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
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec_prime.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_sentinel.h>
//#include <uapi_slabmempgtbl.h>
//#include <xc_init.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xc_ihub.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xc_exhub.h>

//set IOPl to CPl-3
static void __xmhfhic_x86vmx_setIOPL3(uint64_t cpuid){
	uint32_t eflags;
	eflags = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_eflags,CASM_NOPARAM);
	eflags &= ~(EFLAGS_IOPL); //clear out IOPL bits
	//eflags |= 0x00000000; //set IOPL to 0
	eflags |= EFLAGS_IOPL;

	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__write_eflags,eflags);
}


//setup VMX state for CPU
static bool __xmhfhic_x86vmx_setupvmxstate(uint64_t cpuid){
	uint32_t cpuindex = (uint32_t)cpuid;
	const uint32_t vmx_msr_area_msrs[] = {MSR_EFER, MSR_IA32_PAT}; //critical MSRs that need to be saved/restored across guest VM switches
	const unsigned int vmx_msr_area_msrs_count = (sizeof(vmx_msr_area_msrs)/sizeof(vmx_msr_area_msrs[0]));	//count of critical MSRs that need to be saved/restored across VM switches
	uint32_t lodword, hidword;
	uint64_t msr_value;
	uint64_t vmcs_phys_addr = __xmhfhic_x86vmx_archdata[cpuindex].vmx_vmcs_region;

	//save contents of VMX MSRs as well as MSR EFER and EFCR
	{
		uint32_t i;
		uint32_t eax, edx;
		uint64_t msr_value;
		for(i=0; i < IA32_VMX_MSRCOUNT; i++){
			msr_value = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__rdmsr64, (IA32_VMX_BASIC_MSR + i));
			eax = (uint32_t)msr_value;
			edx = (uint32_t)(msr_value >> 32);

			__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[i] = (uint64_t)edx << 32 | (uint64_t) eax;
		}

		msr_value = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__rdmsr64, MSR_EFER);
		eax = (uint32_t)msr_value;
		edx = (uint32_t)(msr_value >> 32);

		__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_efer = (uint64_t)edx << 32 | (uint64_t) eax;
		msr_value = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__rdmsr64, MSR_EFCR);
		eax = (uint32_t)msr_value;
		edx = (uint32_t)(msr_value >> 32);

		__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_efcr = (uint64_t)edx << 32 | (uint64_t) eax;
  	}



	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__write_cr4, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_cr4,CASM_NOPARAM) |  CR4_VMXE);


	//enter VMX root operation using VMXON
	{
		uint32_t retval=0;
		uint64_t vmxonregion_paddr = (uint64_t)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmxon_region;
		//set VMCS rev id
		*((uint32_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmxon_region) = (uint32_t)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

		if(!CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmxon,vmxonregion_paddr)){
			_XDPRINTF_("%s(%u): unable to enter VMX root operation\n", __func__, (uint32_t)cpuid);
			return false;
		}
	}

	//@assert 1;

	//clear VMCS
	if(!CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmclear, (uint64_t)vmcs_phys_addr))
		return false;

	//@assert 1;


	//set VMCS revision id
	*((uint32_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmcs_region) = (uint32_t)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

	//load VMPTR
	if(!CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmptrld,(uint64_t)vmcs_phys_addr))
		return false;

	//@assert 1;


	//setup host state
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_CR0, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_cr0,CASM_NOPARAM));
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_CR4, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_cr4,CASM_NOPARAM));
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_CR3, CASM_FUNCCALL32(uberspark_uobjrtl_hw__generic_x86_32_intel__read_cr3,CASM_NOPARAM));
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_CS_SELECTOR, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_segreg_cs,CASM_NOPARAM));
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_DS_SELECTOR, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_segreg_ds,CASM_NOPARAM));
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_ES_SELECTOR, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_segreg_es,CASM_NOPARAM));
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_FS_SELECTOR, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_segreg_fs,CASM_NOPARAM));
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_GS_SELECTOR, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_segreg_gs,CASM_NOPARAM));
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_SS_SELECTOR, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_segreg_ss,CASM_NOPARAM));
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_TR_SELECTOR, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_tr_sel,CASM_NOPARAM));
	//_XDPRINTF_("%s: uberspark_uobjrtl_hw__generic_x86_32_intel__read_tr_sel = %08x\n", __func__, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_tr_sel,CASM_NOPARAM));
	//_XDPRINTF_("%s: HOST TR SELECTOR = %08x\n", __func__, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmread,VMCS_HOST_TR_SELECTOR));
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_GDTR_BASE, CASM_FUNCCALL32(uberspark_uobjrtl_hw__generic_x86_32_intel__getgdtbase,CASM_NOPARAM));

	//setup host IDTR
	{
		slab_params_t spl;

		spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
		spl.dst_slabid = XMHFGEEC_SLAB_XC_EXHUB;
		spl.cpuid = (uint16_t)cpuid;
		spl.dst_uapifn = UAPI_XCEXHUB_LOADHOSTIDTRBASE;

		xcexhub_slab_main(&spl);
	}



	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_TR_BASE, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__gettssbase,CASM_NOPARAM));

	//setup intercept handler stub
	{
		slab_params_t spl;

		spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
		spl.dst_slabid = XMHFGEEC_SLAB_XC_IHUB;
		spl.cpuid = (uint16_t)cpuid;
		spl.dst_uapifn = UAPI_XCIHUB_INSTALLICPTHANDLER;

		xcihub_slab_main(&spl);
	}


	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_RSP, CASM_FUNCCALL32(uberspark_uobjrtl_hw__generic_x86_32_intel__read_esp,CASM_NOPARAM));


	msr_value = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__rdmsr64, IA32_SYSENTER_CS_MSR);
	lodword = (uint32_t)msr_value;
	hidword = (uint32_t)(msr_value >> 32);
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_SYSENTER_CS, lodword);

	msr_value = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__rdmsr64, IA32_SYSENTER_ESP_MSR);
	lodword = (uint32_t)msr_value;
	hidword = (uint32_t)(msr_value >> 32);
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_SYSENTER_ESP, (((uint64_t)hidword << 32) | (uint64_t)lodword));

	msr_value = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__rdmsr64, IA32_SYSENTER_EIP_MSR);
	lodword = (uint32_t)msr_value;
	hidword = (uint32_t)(msr_value >> 32);
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_SYSENTER_EIP, (((uint64_t)hidword << 32) | (uint64_t)lodword));

	msr_value = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__rdmsr64, IA32_MSR_FS_BASE);
	lodword = (uint32_t)msr_value;
	hidword = (uint32_t)(msr_value >> 32);
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_FS_BASE, (((uint64_t)hidword << 32) | (uint64_t)lodword) );

	msr_value = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__rdmsr64, IA32_MSR_GS_BASE);
	lodword = (uint32_t)msr_value;
	hidword = (uint32_t)(msr_value >> 32);
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_HOST_GS_BASE, (((uint64_t)hidword << 32) | (uint64_t)lodword) );

	//setup default VMX controls
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VMX_PIN_BASED, (uint32_t)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR]);
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (uint32_t)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR]);
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_EXIT_CONTROLS, (uint32_t)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR]);
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_CONTROLS, (uint32_t)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR]);


	//IO bitmap support
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmread,VMCS_CONTROL_VMX_CPU_BASED) | (uint64_t)(1 << 25)) );

	//activate secondary processor controls
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (uint32_t)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (uint32_t) ((uint64_t)CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmread,VMCS_CONTROL_VMX_CPU_BASED) | 0x0000000080000000ULL ) );

	//setup VMCS link pointer
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_GUEST_VMCS_LINK_POINTER_FULL, 0xFFFFFFFFUL);
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_GUEST_VMCS_LINK_POINTER_HIGH, 0xFFFFFFFFUL);

	//setup memory protection
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmread,VMCS_CONTROL_VMX_SECCPU_BASED) | (uint64_t)(1 <<1) | (uint64_t)(1 << 5)) );
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VPID, 0); //[need to populate in sentinel]
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_FULL, 0); // [need to populate in sentinel]
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_HIGH, 0); // [need to populate in sentinel]
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, ((uint64_t)CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmread,VMCS_CONTROL_VMX_CPU_BASED) & (uint64_t)~(1 << 15) & (uint64_t)~(1 << 16)) );


        //Critical MSR load/store
        {
		uint32_t i;
		msr_entry_t *hmsr = (msr_entry_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region;
		msr_entry_t *gmsr = (msr_entry_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region;

		//store host and guest initial values of the critical MSRs
		for(i=0; i < vmx_msr_area_msrs_count; i++){
			uint32_t msr, eax, edx;
			uint64_t msr_value;
			msr = vmx_msr_area_msrs[i];
			msr_value = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__rdmsr64, msr);
			eax = (uint32_t)msr_value;
			edx = (uint32_t)(msr_value >> 32);


			//host MSR values will be what we get from RDMSR
			hmsr[i].index = msr;
			hmsr[i].data = ((uint64_t)edx << 32) | (uint64_t)eax;

			//adjust and populate guest MSR values according to the MSR
			gmsr[i].index = msr;
			gmsr[i].data = ((uint64_t)edx << 32) | (uint64_t)eax;

			switch(msr){
			    case MSR_EFER:{
				gmsr[i].data = gmsr[i].data & (uint64_t)~(1ULL << EFER_LME);
				gmsr[i].data = gmsr[i].data & (uint64_t)~(1ULL << EFER_LMA);
				gmsr[i].data = gmsr[i].data & (uint64_t)~(1ULL << EFER_SCE);
				gmsr[i].data = gmsr[i].data & (uint64_t)~(1ULL << EFER_NXE);
			    }
			    break;

			    default:
				break;
			}
		}

		//host MSR load on exit, we store it ourselves before entry
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_HIGH, 0);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);

		//guest MSR load on entry, store on exit
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_HIGH, 0);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_HIGH, 0);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, vmx_msr_area_msrs_count);
        }


	//setup unrestricted guest
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (uint32_t)((uint64_t)CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmread,VMCS_CONTROL_VMX_SECCPU_BASED) | (uint64_t)(1 << 7)) );

	//enable execution of INVPCID
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (uint32_t)((uint64_t)CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmread,VMCS_CONTROL_VMX_SECCPU_BASED) | (uint64_t)(1 << 12)) );

	//setup CR0 and CR0 access
	{
		_XDPRINTF_("%s[%u]: CR0_ALWAYS1BITS_MASK=0x%08x\n", __func__, (uint32_t)cpuid, (uint32_t)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR]);
		uint32_t control_cr0_mask = ~ (CR0_TS);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_CR0_MASK,
		//		(uint32_t)(((((uint32_t)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR] & ~(CR0_PE)) & ~(CR0_PG)) | CR0_CD) | CR0_NW) );
				control_cr0_mask);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_GUEST_CR0,
				(uint32_t)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR]);
	}

	//setup CR4 and CR4 access
	{
		uint32_t control_cr4_mask = ~ (CR4_PVI | CR4_DE | CR4_PCE | CR4_OSFXSR | CR4_OSXMMEXCPT | CR4_TSD | CR4_PGE);
		_XDPRINTF_("%s[%u]: CR4_ALWAYS1BITS_MASK=0x%08x\n", __func__, (uint32_t)cpuid, (uint32_t)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
		//trap access to non-guest controlled CR4 fixed bits (this includes the VMXE bit)
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_CR4_MASK,
				control_cr4_mask);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_GUEST_CR4,
				(uint32_t)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__vmx_vmwrite,VMCS_CONTROL_CR4_SHADOW,
				(uint32_t)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
	}


	return true;
}



#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
	uint32_t check_esp, check_eip = CASM_RET_EIP;
	bool gp_s5_entry_invoked = false;

	void hwm_vdriver_writeesp(uint32_t oldval, uint32_t newval){
		//@assert (newval >= ((uint32_t)&_init_bsp_cpustack + 4)) && (newval <= ((uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
	}

	void hwm_vdriver_cpu_writecr3(uint32_t oldval, uint32_t newval){
		//@assert (newval ==(uint32_t)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);
	}


	void main(void){
		uint32_t cpuid = 0;
		bool isbsp = true;

		//populate hardware model stack and program counter
		hwm_cpu_gprs_esp = (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
		hwm_cpu_gprs_eip = check_eip;
		check_esp = hwm_cpu_gprs_esp; // pointing to top-of-stack

		//execute harness
		hwm_cpu_cr4 = 0x00000030;
		hwm_cpu_cr0 = 0x80000015;
		hwm_cpu_cr3 =(uint32_t)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t;

		gp_s5_setupcpustate(cpuid, isbsp);

		//@assert (hwm_cpu_gdtr_base == (uint32_t)&__xmhfhic_x86vmx_gdt_start);
		//@assert (hwm_cpu_cs_selector == __CS_CPL0);
		//@assert (hwm_cpu_ds_selector == __DS_CPL0);
		//@assert (hwm_cpu_es_selector == __DS_CPL0);
		//@assert (hwm_cpu_fs_selector == __DS_CPL0);
		//@assert (hwm_cpu_gs_selector == __DS_CPL0);
		//@assert (hwm_cpu_ss_selector == __DS_CPL0);
		//@assert (hwm_cpu_tr_selector ==(__TRSEL + ((uint32_t)cpuid * 8) ));
		//@assert (hwm_cpu_eflags & EFLAGS_IOPL);
		// //@assert (hwm_cpu_msr_apic_base == MMIO_APIC_BASE);
		//@assert (hwm_cpu_msr_efer & ((1 << EFER_NXE)));
		//@assert (hwm_cpu_cr4 & CR4_OSXSAVE);
		//@assert (hwm_cpu_cr0 & 0x20);
		//@assert (hwm_cpu_vmcs_host_rsp >= ((uint32_t)&_init_bsp_cpustack + 4)) && (hwm_cpu_vmcs_host_rsp <= ((uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
		//@assert (hwm_cpu_vmcs_host_cr3 == (uint32_t)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);

		//@assert hwm_cpu_gprs_esp == check_esp;
		//@assert hwm_cpu_gprs_eip == check_eip;
	}
#endif


void gp_s5_setupcpustate(uint32_t cpuid, bool isbsp){

	//replicate common MTRR state on this CPU
	uberspark_uobjrtl_hw__generic_x86_32_intel__restore_mtrrs(&_mtrrs);

	//load GDT
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__loadGDT,&__xmhfhic_x86vmx_gdt);
	_XDPRINTF_("%s[%u]: GDT loaded\n", __func__, (uint32_t)cpuid);


	//reload CS
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__reloadcs,__CS_CPL0);
	_XDPRINTF_("%s[%u]: Reloaded CS\n", __func__, (uint32_t)cpuid);


	//reload DS, FS, GS and SS
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__reloaddsregs,__DS_CPL0);
	_XDPRINTF_("%s[%u]: Reloaded segment registers\n", __func__, (uint32_t)cpuid);


	//load TR
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__loadTR, (__TRSEL + ((uint32_t)cpuid * 8) ) );
	_XDPRINTF_("%s[%u]: TR loaded\n", __func__, (uint32_t)cpuid);


	//load IDT
	{
		slab_params_t spl;

		spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
		spl.dst_slabid = XMHFGEEC_SLAB_XC_EXHUB;
		spl.cpuid = (uint16_t)cpuid;
		spl.dst_uapifn = UAPI_XCEXHUB_LOADIDT;

		xcexhub_slab_main(&spl);
	}


	////turn on CR0.WP bit for supervisor mode write protection
	//write_cr0(uberspark_uobjrtl_hw__generic_x86_32_intel__read_cr0() | CR0_WP);
	//_XDPRINTF_("%s[%u]: Enabled supervisor mode write protection\n", __func__, (uint32_t)cpuid);

	//set IOPL3
	__xmhfhic_x86vmx_setIOPL3(cpuid);
	_XDPRINTF_("%s[%u]: set IOPL to CPL-3\n", __func__, (uint32_t)cpuid);


	//set LAPIC base address to preferred address
	{
		uint64_t msrapic = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__rdmsr64,MSR_APIC_BASE);
		uint64_t msrapic_val = ((msrapic & 0x0000000000000FFFULL) | X86SMP_LAPIC_MEMORYADDRESS);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__wrmsr64,MSR_APIC_BASE, (uint32_t)msrapic_val, (uint32_t)((uint64_t)msrapic_val >> 32) );
	}
	_XDPRINTF_("%s[%u]: set LAPIC base address to %016llx\n", __func__, (uint32_t)cpuid, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__rdmsr64,MSR_APIC_BASE));


	//turn on NX protections
	{
		uint64_t msrefer_val= (CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__rdmsr64, MSR_EFER) | (1 << EFER_NXE));
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__wrmsr64,MSR_EFER, (uint32_t)msrefer_val, (uint32_t)((uint64_t)msrefer_val >> 32) );
		_XDPRINTF_("%s[%u]: NX protections enabled\n", __func__, (uint32_t)cpuid);

	}



	//set OSXSAVE bit in CR4 to enable us to pass-thru XSETBV intercepts
	//when the CPU supports XSAVE feature
	if(uberspark_uobjrtl_hw__generic_x86_32_intel__cpuhasxsavefeature()){
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__write_cr4, (CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_cr4, CASM_NOPARAM) | CR4_OSXSAVE) );
		_XDPRINTF_("%s[%u]: XSETBV passthrough enabled\n", __func__, (uint32_t)cpuid);
	}


	//set bit 5 (EM) of CR0 to be VMX compatible in case of Intel cores
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__write_cr0, (CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_cr0, CASM_NOPARAM) | 0x20));
	_XDPRINTF_("%s[%u]: Set CR0.EM to be VMX compatible\n", __func__, (uint32_t)cpuid);


	//setup sysenter syscall stub
	{
		slab_params_t spl;

		spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
		spl.dst_slabid = XMHFGEEC_SLAB_GEEC_SENTINEL;
		spl.cpuid = cpuid;
		// spl.dst_uapifn = UAPI_SENTINEL_INSTALLSYSCALLSTUB;

		XMHF_SLAB_CALLNEW(&spl);
	}

	//setup VMX state
	if(!__xmhfhic_x86vmx_setupvmxstate(cpuid)){
		_XDPRINTF_("%s[%u]: Unable to set VMX state. Halting!\n", __func__, (uint32_t)cpuid);
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
	}

	_XDPRINTF_("%s[%u]: Setup VMX state\n", __func__, (uint32_t)cpuid);

}


