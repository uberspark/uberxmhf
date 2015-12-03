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

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <geec_prime.h>
#include <geec_sentinel.h>
#include <uapi_slabmempgtbl.h>
#include <xc_init.h>



//set IOPl to CPl-3
static void __xmhfhic_x86vmx_setIOPL3(u64 cpuid){
	u32 eflags;
	eflags = CASM_FUNCCALL(read_eflags,CASM_NOPARAM);
	eflags &= ~(EFLAGS_IOPL); //clear out IOPL bits
	//eflags |= 0x00000000; //set IOPL to 0
	eflags |= EFLAGS_IOPL;

	CASM_FUNCCALL(write_eflags,eflags);
}


//setup VMX state for CPU
static bool __xmhfhic_x86vmx_setupvmxstate(u64 cpuid){
	u32 cpuindex = (u32)cpuid;
	const u32 vmx_msr_area_msrs[] = {MSR_EFER, MSR_IA32_PAT}; //critical MSRs that need to be saved/restored across guest VM switches
	const unsigned int vmx_msr_area_msrs_count = (sizeof(vmx_msr_area_msrs)/sizeof(vmx_msr_area_msrs[0]));	//count of critical MSRs that need to be saved/restored across VM switches
	u32 lodword, hidword;
	u64 msr_value;
	u64 vmcs_phys_addr = __xmhfhic_x86vmx_archdata[cpuindex].vmx_vmcs_region;


	//save contents of VMX MSRs as well as MSR EFER and EFCR
	{
		u32 i;
		u32 eax, edx;
		u64 msr_value;
		for(i=0; i < IA32_VMX_MSRCOUNT; i++){
			msr_value = CASM_FUNCCALL(rdmsr64, (IA32_VMX_BASIC_MSR + i));
			eax = (u32)msr_value;
			edx = (u32)(msr_value >> 32);

			__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[i] = (u64)edx << 32 | (u64) eax;
		}

		msr_value = CASM_FUNCCALL(rdmsr64, MSR_EFER);
		eax = (u32)msr_value;
		edx = (u32)(msr_value >> 32);

		__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_efer = (u64)edx << 32 | (u64) eax;
		msr_value = CASM_FUNCCALL(rdmsr64, MSR_EFCR);
		eax = (u32)msr_value;
		edx = (u32)(msr_value >> 32);

		__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_efcr = (u64)edx << 32 | (u64) eax;
  	}

	CASM_FUNCCALL(write_cr4, CASM_FUNCCALL(read_cr4,CASM_NOPARAM) |  CR4_VMXE);

	//enter VMX root operation using VMXON
	{
		u32 retval=0;
		u64 vmxonregion_paddr = (u64)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmxon_region;
		//set VMCS rev id
		*((u32 *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmxon_region) = (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

		if(!__vmx_vmxon(vmxonregion_paddr)){
				_XDPRINTF_("%s(%u): unable to enter VMX root operation\n", __func__, (u32)cpuid);
				return false;
		}
	}

	//clear VMCS
	if(!__vmx_vmclear((u64)vmcs_phys_addr))
		return false;

	//set VMCS revision id
	*((u32 *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmcs_region) = (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

	//load VMPTR
	if(!__vmx_vmptrld((u64)vmcs_phys_addr))
		return false;

	//setup host state
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CR0, CASM_FUNCCALL(read_cr0,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CR4, CASM_FUNCCALL(read_cr4,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CR3, CASM_FUNCCALL(read_cr3,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CS_SELECTOR, CASM_FUNCCALL(read_segreg_cs,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_DS_SELECTOR, CASM_FUNCCALL(read_segreg_ds,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_ES_SELECTOR, CASM_FUNCCALL(read_segreg_es,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_FS_SELECTOR, CASM_FUNCCALL(read_segreg_fs,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_GS_SELECTOR, CASM_FUNCCALL(read_segreg_gs,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_SS_SELECTOR, CASM_FUNCCALL(read_segreg_ss,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_TR_SELECTOR, CASM_FUNCCALL(read_tr_sel,CASM_NOPARAM));
	//_XDPRINTF_("%s: read_tr_sel = %08x\n", __func__, CASM_FUNCCALL(read_tr_sel,CASM_NOPARAM));
	//_XDPRINTF_("%s: HOST TR SELECTOR = %08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_HOST_TR_SELECTOR));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_GDTR_BASE, CASM_FUNCCALL(xmhf_baseplatform_arch_x86_getgdtbase,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_IDTR_BASE, CASM_FUNCCALL(xmhf_baseplatform_arch_x86_getidtbase,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_TR_BASE, CASM_FUNCCALL(xmhf_baseplatform_arch_x86_gettssbase,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_RIP, xmhfgeec_slab_info_table[XMHFGEEC_SLAB_GEEC_SENTINEL].slab_memoffset_entries[GEEC_SENTINEL_MEMOFFSETS_INTERCEPTHANDLER_IDX]);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_RSP, CASM_FUNCCALL(read_rsp,CASM_NOPARAM));

	msr_value = CASM_FUNCCALL(rdmsr64, IA32_SYSENTER_CS_MSR);
	lodword = (u32)msr_value;
	hidword = (u32)(msr_value >> 32);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_SYSENTER_CS, lodword);

	msr_value = CASM_FUNCCALL(rdmsr64, IA32_SYSENTER_ESP_MSR);
	lodword = (u32)msr_value;
	hidword = (u32)(msr_value >> 32);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_SYSENTER_ESP, (((u64)hidword << 32) | (u64)lodword));

	msr_value = CASM_FUNCCALL(rdmsr64, IA32_SYSENTER_EIP_MSR);
	lodword = (u32)msr_value;
	hidword = (u32)(msr_value >> 32);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_SYSENTER_EIP, (((u64)hidword << 32) | (u64)lodword));

	msr_value = CASM_FUNCCALL(rdmsr64, IA32_MSR_FS_BASE);
	lodword = (u32)msr_value;
	hidword = (u32)(msr_value >> 32);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_FS_BASE, (((u64)hidword << 32) | (u64)lodword) );

	msr_value = CASM_FUNCCALL(rdmsr64, IA32_MSR_GS_BASE);
	lodword = (u32)msr_value;
	hidword = (u32)(msr_value >> 32);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_GS_BASE, (((u64)hidword << 32) | (u64)lodword) );

	//setup default VMX controls
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_PIN_BASED, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR]);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR]);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_CONTROLS, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR]);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_CONTROLS, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR]);

	//IO bitmap support
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 25)) );

	//activate secondary processor controls
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (u32) (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 31)) );

	//setup VMCS link pointer
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_VMCS_LINK_POINTER_FULL, 0xFFFFFFFFUL);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_VMCS_LINK_POINTER_HIGH, 0xFFFFFFFFUL);

	//setup memory protection
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (u64)(1 <<1) | (u64)(1 << 5)) );
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VPID, 0); //[need to populate in sentinel]
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_FULL, 0); // [need to populate in sentinel]
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_HIGH, 0); // [need to populate in sentinel]
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) & (u64)~(1 << 15) & (u64)~(1 << 16)) );


        //Critical MSR load/store
        {
		u32 i;
		msr_entry_t *hmsr = (msr_entry_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region;
		msr_entry_t *gmsr = (msr_entry_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region;

		//store host and guest initial values of the critical MSRs
		for(i=0; i < vmx_msr_area_msrs_count; i++){
			u32 msr, eax, edx;
			u64 msr_value;
			msr = vmx_msr_area_msrs[i];
			msr_value = CASM_FUNCCALL(rdmsr64, msr);
			eax = (u32)msr_value;
			edx = (u32)(msr_value >> 32);


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
		CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region);
		CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_HIGH, 0);
		CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);

		//guest MSR load on entry, store on exit
		CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region);
		CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_HIGH, 0);
		CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);
		CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region);
		CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_HIGH, 0);
		CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, vmx_msr_area_msrs_count);
        }

	//setup unrestricted guest
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (u64)(1 << 7)) );

	//trap access to CR0 fixed 1-bits
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR0_MASK, (u32)(((((u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR] & ~(CR0_PE)) & ~(CR0_PG)) | CR0_CD) | CR0_NW) );

	//trap access to CR4 fixed bits (this includes the VMXE bit)
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR4_MASK, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);

	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR0, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR]);

	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR4, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);




 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR4_SHADOW, (u64)CR4_VMXE);


 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_PAGEFAULT_ERRORCODE_MASK, 0x00000000);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_PAGEFAULT_ERRORCODE_MATCH, 0x00000000);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EXCEPTION_BITMAP, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR3_TARGET_COUNT, 0);


 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR0_SHADOW, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR0));


 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_EXCEPTION_ERRORCODE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_INTERRUPTION_INFORMATION, 0);


 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RSP, 0); //[need to populate in sentinel]

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RIP, 0); // [need to populate in sentinel]
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ACTIVITY_STATE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RFLAGS, (1 <<1) | (EFLAGS_IOPL));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_INTERRUPTIBILITY, 0);


    //IDTR
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_IDTR_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_IDTR_LIMIT, 0);



    //LDTR, unusable
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_LDTR_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_LDTR_LIMIT, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_LDTR_SELECTOR, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_LDTR_ACCESS_RIGHTS, 0x10000);




    //32-bit specific guest slab setup
    {


	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR3, 0 );


	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR0, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0) & ~(CR0_PG) ) );
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR0_SHADOW, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR0));

	//TR, should be usable for VMX to work, but not used by guest
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_BASE, 0);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_LIMIT, 0);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_SELECTOR, 0);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_ACCESS_RIGHTS, 0x8B);

	//CS, DS, ES, FS, GS and SS segments
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_SELECTOR, 0x8);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_BASE, 0);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_LIMIT, 0xFFFFFFFFUL);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_ACCESS_RIGHTS, 0xc09b);

	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_SELECTOR, 0x10);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_BASE, 0);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_LIMIT, 0xFFFFFFFFUL);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_ACCESS_RIGHTS, 0xc093);

	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_SELECTOR, 0x10);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_BASE, 0);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_LIMIT, 0xFFFFFFFFUL);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_ACCESS_RIGHTS, 0xc093);

	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_SELECTOR, 0x10);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_BASE, 0);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_LIMIT, 0xFFFFFFFFUL);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_ACCESS_RIGHTS, 0xc093);

	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_SELECTOR, 0x10);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_BASE, 0);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_LIMIT, 0xFFFFFFFFUL);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_ACCESS_RIGHTS, 0xc093);

	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_SELECTOR, 0x10);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_BASE, 0);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_LIMIT, 0xFFFFFFFFUL);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_ACCESS_RIGHTS, 0xc093);
    }



















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
    */
	_XDPRINTF_("%s: CR0 vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR0));
	_XDPRINTF_("%s: CR4 vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR4));
	_XDPRINTF_("%s: CR0 mask vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR0_MASK));
	_XDPRINTF_("%s: CR4 mask vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR4_MASK));
	_XDPRINTF_("%s: CR0 shadow vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR0_SHADOW));
	_XDPRINTF_("%s: CR4 shadow vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR4_SHADOW));


    return true;
}



void gp_s5_setupcpustate(u32 cpuid, bool isbsp){

	//replicate common MTRR state on this CPU
	xmhfhw_cpu_x86_restore_mtrrs(&_mtrrs);

	//load GDT
	CASM_FUNCCALL(xmhfhw_cpu_loadGDT,&__xmhfhic_x86vmx_gdt);
	_XDPRINTF_("%s[%u]: GDT loaded\n", __func__, (u32)cpuid);

	//reload CS
	CASM_FUNCCALL(__xmhfhic_x86vmx_reloadCS,__CS_CPL0);
	_XDPRINTF_("%s[%u]: Reloaded CS\n", __func__, (u32)cpuid);

	//reload DS, FS, GS and SS
	CASM_FUNCCALL(__xmhfhic_x86vmx_reloadsegregs,__DS_CPL0);
	_XDPRINTF_("%s[%u]: Reloaded segment registers\n", __func__, (u32)cpuid);

	//load TR
	CASM_FUNCCALL(xmhfhw_cpu_loadTR, (__TRSEL + ((u32)cpuid * 16) ) );
	_XDPRINTF_("%s[%u]: TR loaded\n", __func__, (u32)cpuid);

	//load IDT
	CASM_FUNCCALL(xmhfhw_cpu_loadIDT,&__xmhfhic_x86vmx_idt);
	_XDPRINTF_("%s[%u]: IDT loaded\n", __func__, (u32)cpuid);

	////turn on CR0.WP bit for supervisor mode write protection
	//write_cr0(read_cr0() | CR0_WP);
	//_XDPRINTF_("%s[%u]: Enabled supervisor mode write protection\n", __func__, (u32)cpuid);

	//set IOPL3
	__xmhfhic_x86vmx_setIOPL3(cpuid);
	_XDPRINTF_("%s[%u]: set IOPL to CPL-3\n", __func__, (u32)cpuid);

	//set LAPIC base address to preferred address
	{
		u64 msrapic = CASM_FUNCCALL(rdmsr64,MSR_APIC_BASE);
		u64 msrapic_val = ((msrapic & 0x0000000000000FFFULL) | X86SMP_LAPIC_MEMORYADDRESS);
		CASM_FUNCCALL(wrmsr64,MSR_APIC_BASE, (u32)msrapic_val, (u32)((u64)msrapic_val >> 32) );
	}
	_XDPRINTF_("%s[%u]: set LAPIC base address to %016llx\n", __func__, (u32)cpuid, CASM_FUNCCALL(rdmsr64,MSR_APIC_BASE));

	//turn on NX protections
	{
		u64 msrefer_val= (CASM_FUNCCALL(rdmsr64, MSR_EFER) | (1 << EFER_NXE));
		CASM_FUNCCALL(wrmsr64,MSR_EFER, (u32)msrefer_val, (u32)((u64)msrefer_val >> 32) );
		_XDPRINTF_("%s[%u]: NX protections enabled\n", __func__, (u32)cpuid);

	}


	//set OSXSAVE bit in CR4 to enable us to pass-thru XSETBV intercepts
	//when the CPU supports XSAVE feature
	if(xmhf_baseplatform_arch_x86_cpuhasxsavefeature()){
		CASM_FUNCCALL(write_cr4,read_cr4(CASM_NOPARAM) | CR4_OSXSAVE);
		_XDPRINTF_("%s[%u]: XSETBV passthrough enabled\n", __func__, (u32)cpuid);
	}

	//set bit 5 (EM) of CR0 to be VMX compatible in case of Intel cores
	CASM_FUNCCALL(write_cr0,read_cr0(CASM_NOPARAM) | 0x20);
	_XDPRINTF_("%s[%u]: Set CR0.EM to be VMX compatible\n", __func__, (u32)cpuid);


	//setup SYSENTER/SYSEXIT mechanism
	{
	wrmsr64(IA32_SYSENTER_CS_MSR, (u32)__CS_CPL0, 0);
	wrmsr64(IA32_SYSENTER_EIP_MSR, (u32)xmhfgeec_slab_info_table[XMHFGEEC_SLAB_GEEC_SENTINEL].slab_memoffset_entries[GEEC_SENTINEL_MEMOFFSETS_SYSENTERHANDLER_IDX], 0);
	wrmsr64(IA32_SYSENTER_ESP_MSR, (u32)((u32)_geec_primesmp_sysenter_stack[(u32)cpuid] + MAX_PLATFORM_CPUSTACK_SIZE), 0);
	}
	_XDPRINTF_("%s: setup SYSENTER/SYSEXIT mechanism\n", __func__);
	_XDPRINTF_("SYSENTER CS=%016llx\n", CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_CS_MSR));
	_XDPRINTF_("SYSENTER RIP=%016llx\n", CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_EIP_MSR));
	_XDPRINTF_("SYSENTER RSP=%016llx\n", CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_ESP_MSR));


	//setup VMX state
	if(!__xmhfhic_x86vmx_setupvmxstate(cpuid)){
	_XDPRINTF_("%s[%u]: Unable to set VMX state. Halting!\n", __func__, (u32)cpuid);
	HALT();
	}
	_XDPRINTF_("%s[%u]: Setup VMX state\n", __func__, (u32)cpuid);

}


