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
//#include <uapi_slabmempgtbl.h>
//#include <xc_init.h>



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

		if(!CASM_FUNCCALL(__vmx_vmxon,vmxonregion_paddr)){
			_XDPRINTF_("%s(%u): unable to enter VMX root operation\n", __func__, (u32)cpuid);
			return false;
		}
	}

	//@assert 1;

	//clear VMCS
	if(!CASM_FUNCCALL(__vmx_vmclear, (u64)vmcs_phys_addr))
		return false;

	//@assert 1;


	//set VMCS revision id
	*((u32 *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmcs_region) = (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

	//load VMPTR
	if(!CASM_FUNCCALL(__vmx_vmptrld,(u64)vmcs_phys_addr))
		return false;

	//@assert 1;


	//setup host state
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CR0, CASM_FUNCCALL(read_cr0,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CR4, CASM_FUNCCALL(read_cr4,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CR3, CASM_FUNCCALL32(read_cr3,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CS_SELECTOR, CASM_FUNCCALL(read_segreg_cs,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_DS_SELECTOR, CASM_FUNCCALL(read_segreg_ds,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_ES_SELECTOR, CASM_FUNCCALL(read_segreg_es,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_FS_SELECTOR, CASM_FUNCCALL(read_segreg_fs,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_GS_SELECTOR, CASM_FUNCCALL(read_segreg_gs,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_SS_SELECTOR, CASM_FUNCCALL(read_segreg_ss,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_TR_SELECTOR, CASM_FUNCCALL(read_tr_sel,CASM_NOPARAM));
	//_XDPRINTF_("%s: read_tr_sel = %08x\n", __func__, CASM_FUNCCALL(read_tr_sel,CASM_NOPARAM));
	//_XDPRINTF_("%s: HOST TR SELECTOR = %08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_HOST_TR_SELECTOR));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_GDTR_BASE, CASM_FUNCCALL32(xmhf_baseplatform_arch_x86_getgdtbase,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_IDTR_BASE, CASM_FUNCCALL32(xmhf_baseplatform_arch_x86_getidtbase,CASM_NOPARAM));
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_TR_BASE, CASM_FUNCCALL(xmhf_baseplatform_arch_x86_gettssbase,CASM_NOPARAM));

	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_RIP, xmhfgeec_slab_info_table[XMHFGEEC_SLAB_GEEC_SENTINEL].slab_memoffset_entries[GEEC_SENTINEL_MEMOFFSETS_INTERCEPTHANDLER_IDX]);

	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_RSP, CASM_FUNCCALL32(read_esp,CASM_NOPARAM));


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
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 25)) );

	//activate secondary processor controls
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (u32) ((u64)CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_CPU_BASED) | 0x0000000080000000ULL ) );

	//setup VMCS link pointer
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_VMCS_LINK_POINTER_FULL, 0xFFFFFFFFUL);
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_VMCS_LINK_POINTER_HIGH, 0xFFFFFFFFUL);

	//setup memory protection
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_SECCPU_BASED) | (u64)(1 <<1) | (u64)(1 << 5)) );
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VPID, 0); //[need to populate in sentinel]
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_FULL, 0); // [need to populate in sentinel]
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_HIGH, 0); // [need to populate in sentinel]
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, ((u64)CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_CPU_BASED) & (u64)~(1 << 15) & (u64)~(1 << 16)) );


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
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (u32)((u64)CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_SECCPU_BASED) | (u64)(1 << 7)) );

	//enable execution of INVPCID
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (u32)((u64)CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_SECCPU_BASED) | (u64)(1 << 12)) );

	//setup CR0 and CR0 access
	{
		_XDPRINTF_("%s[%u]: CR0_ALWAYS1BITS_MASK=0x%08x\n", __func__, (u32)cpuid, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR]);
		u32 control_cr0_mask = ~ (CR0_TS);
		CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR0_MASK,
		//		(u32)(((((u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR] & ~(CR0_PE)) & ~(CR0_PG)) | CR0_CD) | CR0_NW) );
				control_cr0_mask);
		CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR0,
				(u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR]);
	}

	//setup CR4 and CR4 access
	{
		u32 control_cr4_mask = ~ (CR4_PVI | CR4_DE | CR4_PCE | CR4_OSFXSR | CR4_OSXMMEXCPT | CR4_TSD | CR4_PGE);
		_XDPRINTF_("%s[%u]: CR4_ALWAYS1BITS_MASK=0x%08x\n", __func__, (u32)cpuid, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
		//trap access to non-guest controlled CR4 fixed bits (this includes the VMXE bit)
		CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR4_MASK,
				control_cr4_mask);
		CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR4,
				(u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
		CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR4_SHADOW,
				(u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
	}


	return true;
}



#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
	u32 check_esp, check_eip = CASM_RET_EIP;
	bool gp_s5_entry_invoked = false;

	void xmhfhwm_vdriver_writeesp(u32 oldval, u32 newval){
		//@assert (newval >= ((u32)&_init_bsp_cpustack + 4)) && (newval <= ((u32)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
	}

	void xmhfhwm_vdriver_cpu_writecr3(u32 oldval, u32 newval){
		//@assert (newval ==(u32)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);
	}


	void main(void){
		u32 cpuid = 0;
		bool isbsp = true;

		//populate hardware model stack and program counter
		xmhfhwm_cpu_gprs_esp = (u32)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
		xmhfhwm_cpu_gprs_eip = check_eip;
		check_esp = xmhfhwm_cpu_gprs_esp; // pointing to top-of-stack

		//execute harness
		xmhfhwm_cpu_cr4 = 0x00000030;
		xmhfhwm_cpu_cr0 = 0x80000015;
		xmhfhwm_cpu_cr3 =(u32)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t;

		gp_s5_setupcpustate(cpuid, isbsp);

		//@assert (xmhfhwm_cpu_gdtr_base == (u32)&__xmhfhic_x86vmx_gdt_start);
		//@assert (xmhfhwm_cpu_cs_selector == __CS_CPL0);
		//@assert (xmhfhwm_cpu_ds_selector == __DS_CPL0);
		//@assert (xmhfhwm_cpu_es_selector == __DS_CPL0);
		//@assert (xmhfhwm_cpu_fs_selector == __DS_CPL0);
		//@assert (xmhfhwm_cpu_gs_selector == __DS_CPL0);
		//@assert (xmhfhwm_cpu_ss_selector == __DS_CPL0);
		//@assert (xmhfhwm_cpu_tr_selector ==(__TRSEL + ((u32)cpuid * 8) ));
		//@assert (xmhfhwm_cpu_idtr_base == (u32)&__xmhfhic_x86vmx_idt_start);
		//@assert (xmhfhwm_cpu_eflags & EFLAGS_IOPL);
		// //@assert (xmhfhwm_cpu_msr_apic_base == MMIO_APIC_BASE);
		//@assert (xmhfhwm_cpu_msr_efer & ((1 << EFER_NXE)));
		//@assert (xmhfhwm_cpu_cr4 & CR4_OSXSAVE);
		//@assert (xmhfhwm_cpu_cr0 & 0x20);
		//@assert (xmhfhwm_cpu_msr_sysenter_cs == __CS_CPL0);
		//@assert (xmhfhwm_cpu_msr_sysenter_eip == xmhfgeec_slab_info_table[XMHFGEEC_SLAB_GEEC_SENTINEL].slab_memoffset_entries[GEEC_SENTINEL_MEMOFFSETS_SYSENTERHANDLER_IDX]);
		//@assert (xmhfhwm_cpu_msr_sysenter_esp_lo == (u32)((u32)&_geec_primesmp_sysenter_stack[(u32)cpuid+1]));
		//@assert (xmhfhwm_cpu_msr_sysenter_esp_hi == 0);
		//@assert (xmhfhwm_cpu_vmcs_host_rip == xmhfgeec_slab_info_table[XMHFGEEC_SLAB_GEEC_SENTINEL].slab_memoffset_entries[GEEC_SENTINEL_MEMOFFSETS_INTERCEPTHANDLER_IDX]);
		//@assert (xmhfhwm_cpu_vmcs_host_rsp >= ((u32)&_init_bsp_cpustack + 4)) && (xmhfhwm_cpu_vmcs_host_rsp <= ((u32)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
		//@assert (xmhfhwm_cpu_vmcs_host_cr3 == (u32)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);

		//@assert xmhfhwm_cpu_gprs_esp == check_esp;
		//@assert xmhfhwm_cpu_gprs_eip == check_eip;
	}
#endif


void gp_s5_setupcpustate(u32 cpuid, bool isbsp){

	//replicate common MTRR state on this CPU
	xmhfhw_cpu_x86_restore_mtrrs(&_mtrrs);

	//load GDT
	CASM_FUNCCALL(xmhfhw_cpu_loadGDT,&__xmhfhic_x86vmx_gdt);
	_XDPRINTF_("%s[%u]: GDT loaded\n", __func__, (u32)cpuid);


	//reload CS
	CASM_FUNCCALL(xmhfhw_cpu_reloadcs,__CS_CPL0);
	_XDPRINTF_("%s[%u]: Reloaded CS\n", __func__, (u32)cpuid);


	//reload DS, FS, GS and SS
	CASM_FUNCCALL(xmhfhw_cpu_reloaddsregs,__DS_CPL0);
	_XDPRINTF_("%s[%u]: Reloaded segment registers\n", __func__, (u32)cpuid);


	//load TR
	CASM_FUNCCALL(xmhfhw_cpu_loadTR, (__TRSEL + ((u32)cpuid * 8) ) );
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
		CASM_FUNCCALL(write_cr4, (CASM_FUNCCALL(read_cr4, CASM_NOPARAM) | CR4_OSXSAVE) );
		_XDPRINTF_("%s[%u]: XSETBV passthrough enabled\n", __func__, (u32)cpuid);
	}


	//set bit 5 (EM) of CR0 to be VMX compatible in case of Intel cores
	CASM_FUNCCALL(write_cr0, (CASM_FUNCCALL(read_cr0, CASM_NOPARAM) | 0x20));
	_XDPRINTF_("%s[%u]: Set CR0.EM to be VMX compatible\n", __func__, (u32)cpuid);


	//setup sysenter syscall stub
	{
		slab_params_t spl;

		spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
		spl.dst_slabid = XMHFGEEC_SLAB_GEEC_SENTINEL;
		spl.cpuid = cpuid;
		spl.dst_uapifn = UAPI_SENTINEL_INSTALLSYSCALLSTUB;

		XMHF_SLAB_CALLNEW(&spl);
	}

	//setup VMX state
	if(!__xmhfhic_x86vmx_setupvmxstate(cpuid)){
		_XDPRINTF_("%s[%u]: Unable to set VMX state. Halting!\n", __func__, (u32)cpuid);
		CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
	}

	_XDPRINTF_("%s[%u]: Setup VMX state\n", __func__, (u32)cpuid);

}


