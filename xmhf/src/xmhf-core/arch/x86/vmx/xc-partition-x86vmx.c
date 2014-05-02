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

//critical MSRs that need to be saved/restored across guest VM switches
static const u32 vmx_msr_area_msrs[] = {
	MSR_EFER, 
	MSR_IA32_PAT,
	MSR_K6_STAR,
};

//count of critical MSRs that need to be saved/restored across VM switches
static const unsigned int vmx_msr_area_msrs_count = (sizeof(vmx_msr_area_msrs)/sizeof(vmx_msr_area_msrs[0]));


//initialize partition monitor for a given CPU
static void xmhf_partition_arch_x86vmx_initializemonitor(xc_cpu_t *xc_cpu){
	xc_cpuarchdata_x86vmx_t *xc_cpuarchdata_x86vmx = (xc_cpuarchdata_x86vmx_t *)xc_cpu->cpuarchdata;
	u64 vmcs_phys_addr = hva2spa((void*)xc_cpuarchdata_x86vmx->vmx_vmcs_region);

	  
	//check VMX support
	{
	u32	cpu_features;
	#ifndef __XMHF_VERIFICATION__
	asm("mov	$1, %%eax \n"
				"cpuid \n"
				"mov	%%ecx, %0	\n"
				::"m"(cpu_features): "eax", "ebx", "ecx", "edx" );
		if ( ( cpu_features & (1<<5) ) == 0 ){
			printf("CPU(0x%02x) does not support VMX. Halting!", xc_cpu->cpuid);
	  HALT();
		}
	#endif
	}

	//save contents of VMX MSRs as well as MSR EFER and EFCR 
	{
	u32 i;
	u32 eax, edx;
	#ifndef __XMHF_VERIFICATION__
	for(i=0; i < IA32_VMX_MSRCOUNT; i++){
	#else
	for(i=0; i < 1; i++){
	#endif
		#ifndef __XMHF_VERIFICATION__
		rdmsr( (IA32_VMX_BASIC_MSR + i), &eax, &edx);
		#endif
		xc_cpuarchdata_x86vmx->vmx_msrs[i] = (u64)edx << 32 | (u64) eax;        
	}

	#ifndef __XMHF_VERIFICATION__
	rdmsr(MSR_EFER, &eax, &edx);
	#endif
	xc_cpuarchdata_x86vmx->vmx_msr_efer = (u64)edx << 32 | (u64) eax;
	#ifndef __XMHF_VERIFICATION__
	rdmsr(MSR_EFCR, &eax, &edx);
	#endif
	xc_cpuarchdata_x86vmx->vmx_msr_efcr = (u64)edx << 32 | (u64) eax;

	printf("\nCPU(0x%02x): MSR_EFER=0x%08x%08x", xc_cpu->cpuid, (u32)((u64)xc_cpuarchdata_x86vmx->vmx_msr_efer >> 32), 
          (u32)xc_cpuarchdata_x86vmx->vmx_msr_efer);
    printf("\nCPU(0x%02x): MSR_EFCR=0x%08x%08x", xc_cpu->cpuid, (u32)((u64)xc_cpuarchdata_x86vmx->vmx_msr_efcr >> 32), 
          (u32)xc_cpuarchdata_x86vmx->vmx_msr_efcr);
  
	}

	//we required unrestricted guest support, halt if we don;t have it
	if( !( (u32)((u64)xc_cpuarchdata_x86vmx->vmx_msrs[IA32_VMX_MSRCOUNT-1] >> 32) & 0x80 ) ){
		printf("\n%s: need unrestricted guest support but did not find any. Halting!", __FUNCTION__);
		HALT();
	}

	//enable VMX by setting CR4
	#ifndef __XMHF_VERIFICATION__
	asm(	" mov  %%cr4, %%eax	\n"\
		" bts  $13, %%eax	\n"\
		" mov  %%eax, %%cr4	" ::: "eax" );
	#endif
	printf("\nCPU(0x%02x): enabled VMX", xc_cpu->cpuid);

	//enter VMX root operation using VMXON
	{
	u32 retval=0;
	u64 vmxonregion_paddr = hva2spa((void*)xc_cpuarchdata_x86vmx->vmx_vmxon_region);
	//set VMCS rev id
	#ifndef __XMHF_VERIFICATION__
	*((u32 *)xc_cpuarchdata_x86vmx->vmx_vmxon_region) = (u32)xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];
	#endif

	#ifndef __XMHF_VERIFICATION__
	asm( "vmxon %1 \n"
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
	#endif

	if(!retval){
	  printf("\nCPU(0x%02x): Fatal, unable to enter VMX root operation", xc_cpu->cpuid);
	  HALT();
	}  

	printf("\nCPU(0x%02x): Entered VMX root operation", xc_cpu->cpuid);
	}


	//clear VMCS
	if(!__vmx_vmclear((u64)vmcs_phys_addr)){
	printf("\nCPU(0x%02x): VMCLEAR failed, HALT!", xc_cpu->cpuid);
	HALT();
	}
	printf("\nCPU(0x%02x): VMCLEAR success.", xc_cpu->cpuid);
  
  
	//set VMCS revision id
	*((u32 *)xc_cpuarchdata_x86vmx->vmx_vmcs_region) = (u32)xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

	//load VMPTR
	if(!__vmx_vmptrld((u64)vmcs_phys_addr)){
	printf("\nCPU(0x%02x): VMPTRLD failed, HALT!", xc_cpu->cpuid);
	HALT();
	}
	printf("\nCPU(0x%02x): VMPTRLD success.", xc_cpu->cpuid);

}



//setup guest OS state for the partition
void xmhf_partition_arch_x86vmx_setupguestOSstate(xc_cpu_t *xc_cpu, u32 xc_partition_index){
	u32 lodword, hidword;
	xc_partition_t *xc_partition = &g_xc_primary_partition[xc_partition_index];
	xc_cpuarchdata_x86vmx_t *xc_cpuarchdata_x86vmx = (xc_cpuarchdata_x86vmx_t *)xc_cpu->cpuarchdata;
	xc_partition_trapmaskdata_x86vmx_t *xc_partition_trapmaskdata_x86vmx = (xc_partition_trapmaskdata_x86vmx_t *)xc_partition->trapmaskdata;
	
	//setup host state

	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CR0, read_cr0());
	__vmx_vmwrite(VMCS_HOST_CR0, read_cr0());
	__vmx_vmread(VMCS_HOST_CR0, &lodword);
	printf("\nVMCS_HOST_CR0=%x, read_cr0=%x, lod=%x", xmhfhw_cpu_x86vmx_vmread(VMCS_HOST_CR0), read_cr0(), lodword);
	HALT_ON_ERRORCOND(xmhfhw_cpu_x86vmx_vmread(VMCS_HOST_CR0) == read_cr0());
	
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

#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
	if( vcpu->vmcs.host_RIP == (u64)(u32)xmhf_parteventhub_arch_x86vmx_entry)
		vcpu->vmcs.host_RIP = 0xDEADBEEF;
#endif //__XMHF_VERIFICATION__

			

#ifndef __XMHF_VERIFICATION__			
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
#endif

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
      
	//setup guest state
	//CR0, real-mode, PE and PG bits cleared
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR0, (xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR] & ~(CR0_PE) & ~(CR0_PG)) );
	//CR4, required bits set (usually VMX enabled bit)
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR4, xc_cpuarchdata_x86vmx->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
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
	if(xc_cpu->is_bsp){
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

	//flush guest TLB to start with
	//xmhf_memprot_arch_x86vmx_flushmappings();
}


//----------------------------------------------------------------------
// start HVM on a given physical core
// on success: this function will not return
// on failure: 1 if a valid error code is present, 0 if no error code, 
// 2 if invalid error info. (should never happen)
//----------------------------------------------------------------------
u32 __vmx_start_hvm(void) __attribute__ ((naked)) {
	//save GPRs
	asm volatile ("pushal\r\n");
   
	//real-mode setup just like the BIOS
	asm volatile ("movl $0x0, %eax\r\n");
	asm volatile ("movl $0x0, %ebx\r\n");
	asm volatile ("movl $0x0, %ecx\r\n");
	asm volatile ("movl $0x80, %edx\r\n");
	asm volatile ("movl $0x0, %ebp\r\n");
	asm volatile ("movl $0x0, %esi\r\n");
	asm volatile ("movl $0x0, %edi\r\n");

	//attempt to instantiate the HVM
	asm volatile ("vmlaunch\r\n");
	 
	//if we get here then some error happened during the launch
	
	//restore stack frame for a return from this procedure
	asm volatile ("popal\r\n");	

	//there are two possible causes of failure, VMFailInvalid or
	//VMFailValid (VM instruction error field contains the error code)
	//check which happened and return appropriate value in eax 
	asm volatile ("jc __vmx_start_hvm_failinvalid\r\n"
				  "jnz	__vmx_start_hvm_undefinedimplementation	\r\n"
				  "movl $0x1, %eax\r\n"
				  "ret\r\n"					//return 1 as we have error code
				  "__vmx_start_hvm_undefinedimplementation:\r\n"
				  "movl $0x2, %eax\r\n"		//violation of VMLAUNCH specs., handle it anyways
				  "ret\r\n"
				  "__vmx_start_hvm_failinvalid:\r\n"
				  "xorl %eax, %eax\r\n"		//return 0 as we have no error code available
				  "ret\r\n"
	);

}

//start executing the partition and guest OS
static void xmhf_partition_arch_x86vmx_start(xc_cpu_t *xc_cpu){
	u32 errorcode;
    
#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
	//ensure that whenever a partition is started on a vcpu, we have extended paging
	//enabled and that the base points to the extended page tables we have initialized
	assert( (vcpu->vmcs.control_EPT_pointer_high == 0) && (vcpu->vmcs.control_EPT_pointer_full == (hva2spa((void*)vcpu->vmx_vaddr_ept_pml4_table) | 0x1E)) );
	assert( (vcpu->vmcs.control_VMX_seccpu_based & 0x2) );
	assert( vcpu->vmcs.host_RIP == 0xDEADBEEF);
#endif

#ifndef __XMHF_VERIFICATION__
	HALT_ON_ERRORCOND( xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_VMCS_LINK_POINTER_FULL) == 0xFFFFFFFFUL );

	errorcode=__vmx_start_hvm();
	HALT_ON_ERRORCOND(errorcode != 2);	//this means the VMLAUNCH implementation violated the specs.

	switch(errorcode){
			case 0:	//no error code, VMCS pointer is invalid
				printf("\nCPU(0x%02x): VMLAUNCH error; VMCS pointer invalid?. HALT!", xc_cpu->cpuid);
				break;
			case 1:{//error code available, so dump it
				u32 code=xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMINSTR_ERROR);
				printf("\nCPU(0x%02x): VMLAUNCH error; code=0x%x. HALT!", xc_cpu->cpuid, code);
				//xmhf_baseplatform_arch_x86vmx_dumpVMCS(vcpu);
				break;
			}
	}
	HALT();
#endif	

}





//---------------------------------------------------------------------
//initialize partition monitor for a given CPU
void xmhf_partition_arch_initializemonitor(u32 cpu_index){
	xc_cpu_t *xc_cpu = &g_xc_cpu[cpu_index];
	xmhf_partition_arch_x86vmx_initializemonitor(xc_cpu);
}

//setup guest OS state for the partition
void xmhf_partition_arch_setupguestOSstate(u32 cpu_index, u32 xc_partition_index){
	xc_cpu_t *xc_cpu = &g_xc_cpu[cpu_index];
	xmhf_partition_arch_x86vmx_setupguestOSstate(xc_cpu, xc_partition_index);
}

//start executing the partition and guest OS
void xmhf_partition_arch_start(u32 cpu_index){
	xc_cpu_t *xc_cpu = &g_xc_cpu[cpu_index];
	xmhf_partition_arch_x86vmx_start(xc_cpu);
}








