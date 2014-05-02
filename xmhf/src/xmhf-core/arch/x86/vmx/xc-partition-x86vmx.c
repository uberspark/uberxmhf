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
 * XMHF partition component (x86 VMX backend)
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf-core.h>
#include <xc-x86.h>
#include <xc-x86vmx.h>






//setup guest OS state for the partition
void xmhf_partition_arch_x86vmx_setupguestOSstate(context_desc_t context_desc){
/*void xmhf_partition_arch_x86vmx_setupguestOSstate(xc_cpu_t *xc_cpu, u32 xc_partition_index){
	u32 lodword, hidword;
	xc_partition_t *xc_partition = &g_xc_primary_partition[xc_partition_index];
	xc_cpuarchdata_x86vmx_t *xc_cpuarchdata_x86vmx = (xc_cpuarchdata_x86vmx_t *)xc_cpu->cpuarchdata;
	xc_partition_trapmaskdata_x86vmx_t *xc_partition_trapmaskdata_x86vmx = (xc_partition_trapmaskdata_x86vmx_t *)xc_partition->trapmaskdata;
	xc_partition_hptdata_x86vmx_t *eptdata = (xc_partition_hptdata_x86vmx_t *)xc_partition->hptdata;

	
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
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_RIP, (u32)xmhf_parteventhub_arch_x86vmx_entry);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_RSP, read_esp());
	rdmsr(IA32_SYSENTER_CS_MSR, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_CS, lodword);
	rdmsr(IA32_SYSENTER_ESP_MSR, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_ESP, (u32)(((u64)hidword << 32) | (u64)lodword));
	rdmsr(IA32_SYSENTER_EIP_MSR, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_EIP, (u32)(((u64)hidword << 32) | (u64)lodword));
	rdmsr(IA32_MSR_FS_BASE, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_FS_BASE, (u32) (((u64)hidword << 32) | (u64)lodword) );
	rdmsr(IA32_MSR_GS_BASE, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_GS_BASE, (u32) (((u64)hidword << 32) | (u64)lodword) );

	//setup default VMX controls
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_PIN_BASED, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_CONTROLS, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR]);

	//IO bitmap support
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL, (u32)hva2spa((void*)xc_partition_trapmaskdata_x86vmx->vmx_iobitmap_region));
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPA_ADDRESS_HIGH, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL, (u32)hva2spa( ((void*)xc_partition_trapmaskdata_x86vmx->vmx_iobitmap_region + PAGE_SIZE_4K) ));
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPB_ADDRESS_HIGH, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (1 << 25)) );

	//Critical MSR load/store
	{
		u32 i;
		msr_entry_t *hmsr = (msr_entry_t *)xc_cpuarchdata_x86vmx->vmx_msr_area_host_region;
		msr_entry_t *gmsr = (msr_entry_t *)xc_cpuarchdata_x86vmx->vmx_msr_area_guest_region;

		#ifndef __XMHF_VERIFICATION__
		//store initial values of the MSRs
		for(i=0; i < vmx_msr_area_msrs_count; i++){
			u32 msr, eax, edx;
			msr = vmx_msr_area_msrs[i];						
			rdmsr(msr, &eax, &edx);
			hmsr[i].index = gmsr[i].index = msr;
			hmsr[i].data = gmsr[i].data = ((u64)edx << 32) | (u64)eax;
		}
		#endif

		//host MSR load on exit, we store it ourselves before entry
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL, (u32)hva2spa((void*)xc_cpuarchdata_x86vmx->vmx_msr_area_host_region));
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_HIGH, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);

		//guest MSR load on entry, store on exit
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, (u32)hva2spa((void*)xc_cpuarchdata_x86vmx->vmx_msr_area_guest_region));
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_HIGH, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, (u32)hva2spa((void*)xc_cpuarchdata_x86vmx->vmx_msr_area_guest_region));
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_HIGH, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, vmx_msr_area_msrs_count);
		
	}


	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_PAGEFAULT_ERRORCODE_MASK, 0x00000000);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_PAGEFAULT_ERRORCODE_MATCH, 0x00000000);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EXCEPTION_BITMAP, 0);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR3_TARGET_COUNT, 0);  


	//activate secondary processor controls
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (1 << 31)) );

	//setup unrestricted guest
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (1 << 7)) );

	//setup VMCS link pointer
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_VMCS_LINK_POINTER_FULL, (u32)0xFFFFFFFFUL);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_VMCS_LINK_POINTER_HIGH, (u32)0xFFFFFFFFUL);
	
	//setup NMI intercept for core-quiescing
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_PIN_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_PIN_BASED) | (1 << 3) ) );
	
	//trap access to CR0 fixed 1-bits
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR0_MASK, ((((xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR] & ~(CR0_PE)) & ~(CR0_PG)) | CR0_CD) | CR0_NW) );
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR0_SHADOW, xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0));
			
	//trap access to CR4 fixed bits (this includes the VMXE bit)
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR4_MASK, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR4_SHADOW, CR4_VMXE);

	//setup memory protection
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (1 <<1) | (1 << 5)) );
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VPID, 1);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_FULL, (hva2spa((void*)eptdata->vmx_ept_pml4_table) | 0x1E) );
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_HIGH, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) & ~(1 << 15) & ~(1 << 16)) );
*/

	//--------------------------------------------------------------------------------------------------------------------------------
	//setup guest state
	//CR0, real-mode, PE and PG bits cleared
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR0, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0) & ~(CR0_PE) & ~(CR0_PG)) );
	//CR3 set to 0, does not matter
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, 0);
	//IDTR
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_IDTR_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_IDTR_LIMIT, 0x3ff);
	//GDTR
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_LIMIT, 0);
	//LDTR, unusable
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_LIMIT, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_SELECTOR, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_ACCESS_RIGHTS, 0x10000);
	//TR, should be usable for VMX to work, but not used by guest
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_LIMIT, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_SELECTOR, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_ACCESS_RIGHTS, 0x83);
	//RSP
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RSP, 0);
	
	//RIP and activity state
	if(context_desc.cpu_desc.isbsp){
		//printf("\nBSP(0x%02x): copying boot-module to boot guest", xc_cpu->cpuid);
		//#ifndef __XMHF_VERIFICATION__
		//memcpy((void *)__GUESTOSBOOTMODULE_BASE, (void *)xcbootinfo->richguest_bootmodule_base, xcbootinfo->richguest_bootmodule_size);
		//#endif
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_SELECTOR, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_BASE, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RIP, 0x7c00);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ACTIVITY_STATE, 0);	//normal activity state
	}else{
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_SELECTOR, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_BASE, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RIP, 0);
		xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ACTIVITY_STATE, 3);	//wait-for-SIPI
	}

	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_LIMIT, 0xFFFF);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_ACCESS_RIGHTS, 0x93);

	//RFLAGS
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RFLAGS, ((((0 & ~((1<<3)|(1<<5)|(1<<15)) ) | (1 <<1)) | (1<<9)) & ~(1<<14)) );
	//CS, DS, ES, FS, GS and SS segments
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_SELECTOR, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_LIMIT, 0xFFFF);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_ACCESS_RIGHTS, 0x93);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_SELECTOR, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_LIMIT, 0xFFFF);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_ACCESS_RIGHTS, 0x93);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_SELECTOR, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_LIMIT, 0xFFFF);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_ACCESS_RIGHTS, 0x93);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_SELECTOR, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_LIMIT, 0xFFFF);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_ACCESS_RIGHTS, 0x93);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_SELECTOR, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_BASE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_LIMIT, 0xFFFF);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_ACCESS_RIGHTS, 0x93);

}









//---------------------------------------------------------------------
//initialize partition monitor for a given CPU
//void xmhf_partition_arch_initializemonitor(u32 cpu_index){
//	xc_cpu_t *xc_cpu = &g_xc_cpu[cpu_index];
//	xmhf_partition_arch_x86vmx_initializemonitor(xc_cpu);
//}

//setup guest OS state for the partition
void xmhf_partition_arch_setupguestOSstate(context_desc_t context_desc){
	//xc_cpu_t *xc_cpu = &g_xc_cpu[cpu_index];
	xmhf_partition_arch_x86vmx_setupguestOSstate(context_desc);
}

//start executing the partition and guest OS
//void xmhf_partition_arch_start(u32 cpu_index){
//	xc_cpu_t *xc_cpu = &g_xc_cpu[cpu_index];
//	xmhf_partition_arch_x86vmx_start(xc_cpu);
//}








