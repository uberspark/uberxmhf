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

// runtime.c
// author: amit vasudevan (amitvasudevan@acm.org)

//---includes-------------------------------------------------------------------
#include <xmhf.h>

#if defined(__DRT__) && !defined(__DMAP__)

// This macro is defined in xmhf-dmaprot.h. However when !__DMAP__ this header
// is not included. So define it here.
#define ACPI_MAX_RSDT_ENTRIES (256)

static void vmx_eap_zap(void)
{
    ACPI_RSDP rsdp;
    ACPI_RSDT rsdt;
    u32 num_rsdtentries;
    uintptr_t rsdtentries[ACPI_MAX_RSDT_ENTRIES];
    uintptr_t status;
    VTD_DMAR dmar;
    u32 i, dmarfound;
    spa_t dmaraddrphys, remappingstructuresaddrphys;
    spa_t rsdt_xsdt_spaddr = INVALID_SPADDR;
    hva_t rsdt_xsdt_vaddr = INVALID_VADDR;

    // zero out rsdp and rsdt structures
    memset(&rsdp, 0, sizeof(ACPI_RSDP));
    memset(&rsdt, 0, sizeof(ACPI_RSDT));

    // get ACPI RSDP
    // [TODO] Unify the name of <xmhf_baseplatform_arch_x86_acpi_getRSDP> and <xmhf_baseplatform_arch_x86_acpi_getRSDP>, and then remove the following #ifdef
    status = xmhf_baseplatform_arch_x86_acpi_getRSDP(&rsdp);
    HALT_ON_ERRORCOND(status != 0); // we need a valid RSDP to proceed
    printf("\n%s: RSDP at %08x", __FUNCTION__, status);

    // [Superymk] Use RSDT if it is ACPI v1, or use XSDT addr if it is ACPI v2
    if (rsdp.revision == 0) // ACPI v1
    {
        printf("\n%s: ACPI v1", __FUNCTION__);
        rsdt_xsdt_spaddr = rsdp.rsdtaddress;
    }
    else if (rsdp.revision == 0x2) // ACPI v2
    {
        printf("\n%s: ACPI v2", __FUNCTION__);
        rsdt_xsdt_spaddr = (spa_t)rsdp.xsdtaddress;
    }
    else // Unrecognized ACPI version
    {
        printf("\n%s: ACPI unsupported version!", __FUNCTION__);
        return;
    }

    // grab ACPI RSDT
    // Note: in i386, <rsdt_xsdt_spaddr> should be in lower 4GB. So the conversion to vaddr is fine.
    rsdt_xsdt_vaddr = (hva_t)rsdt_xsdt_spaddr;

    xmhf_baseplatform_arch_flat_copy((u8 *)&rsdt, (u8 *)rsdt_xsdt_vaddr, sizeof(ACPI_RSDT));
    printf("\n%s: RSDT at %08x, len=%u bytes, hdrlen=%u bytes",
           __FUNCTION__, rsdt_xsdt_vaddr, rsdt.length, sizeof(ACPI_RSDT));

    // get the RSDT entry list
    num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT)) / sizeof(u32);
    HALT_ON_ERRORCOND(num_rsdtentries < ACPI_MAX_RSDT_ENTRIES);
    xmhf_baseplatform_arch_flat_copy((u8 *)&rsdtentries, (u8 *)(rsdt_xsdt_vaddr + sizeof(ACPI_RSDT)),
                                     sizeof(u32) * num_rsdtentries);
    printf("\n%s: RSDT entry list at %08x, len=%u", __FUNCTION__,
           (rsdt_xsdt_vaddr + sizeof(ACPI_RSDT)), num_rsdtentries);

    // find the VT-d DMAR table in the list (if any)
    for (i = 0; i < num_rsdtentries; i++)
    {
        xmhf_baseplatform_arch_flat_copy((u8 *)&dmar, (u8 *)rsdtentries[i], sizeof(VTD_DMAR));
        if (dmar.signature == VTD_DMAR_SIGNATURE)
        {
            dmarfound = 1;
            break;
        }
    }

    // if no DMAR table, bail out
    if (!dmarfound)
        return;

    dmaraddrphys = rsdtentries[i]; // DMAR table physical memory address;
    printf("\n%s: DMAR at %08x", __FUNCTION__, dmaraddrphys);

    i = 0;
    remappingstructuresaddrphys = dmaraddrphys + sizeof(VTD_DMAR);
    printf("\n%s: remapping structures at %08x", __FUNCTION__, remappingstructuresaddrphys);

    // zap VT-d presence in ACPI table...
    // TODO: we need to be a little elegant here. eventually need to setup
    // EPT/NPTs such that the DMAR pages are unmapped for the guest
    xmhf_baseplatform_arch_flat_writeu32(dmaraddrphys, 0UL);

    // success
    printf("\n%s: success, leaving...", __FUNCTION__);
}
#endif /* defined(__DRT__) && !defined(__DMAP__) */

//---runtime main---------------------------------------------------------------
void xmhf_runtime_entry(void){
	u32 cpu_vendor;

	//get CPU vendor
	cpu_vendor = xmhf_baseplatform_getcpuvendor();
        (void)cpu_vendor;

	//initialize Runtime Parameter Block (rpb)
	rpb = (RPB *)&arch_rpb;

	//setup debugging
	xmhf_debug_init((char *)&rpb->RtmUartConfig);
	printf("\nruntime initializing...");

  	//initialize basic platform elements
	xmhf_baseplatform_initialize();

    //[debug] dump E820 and MP table
 	#ifndef __XMHF_VERIFICATION__
 	printf("\nNumber of E820 entries = %u", rpb->XtVmmE820NumEntries);
	{
		int i;
		for(i=0; i < (int)rpb->XtVmmE820NumEntries; i++){
		printf("\n0x%08x%08x, size=0x%08x%08x (%u)",
          g_e820map[i].baseaddr_high, g_e820map[i].baseaddr_low,
          g_e820map[i].length_high, g_e820map[i].length_low,
          g_e820map[i].type);
		}
  	}
	printf("\nNumber of MP entries = %u", rpb->XtVmmMPCpuinfoNumEntries);
	{
		int i;
		for(i=0; i < (int)rpb->XtVmmMPCpuinfoNumEntries; i++)
			printf("\nCPU #%u: bsp=%u, lapic_id=0x%02x", i, g_cpumap[i].isbsp, g_cpumap[i].lapic_id);
	}
	#endif //__XMHF_VERIFICATION__


	#ifndef __XMHF_VERIFICATION__
	//setup EMHF exception handler component
	xmhf_xcphandler_initialize();
	#endif

#if defined (__DMAP__)
		// TODO: DMAP code not ported to amd64 yet
		{
			#define ADDR_512GB  (PAGE_SIZE_512G)
				u64 protectedbuffer_paddr;
				hva_t protectedbuffer_vaddr;
				u32 protectedbuffer_size;

				protectedbuffer_paddr = hva2spa(&g_rntm_dmaprot_buffer);
				protectedbuffer_vaddr = (hva_t)&g_rntm_dmaprot_buffer;
				protectedbuffer_size = xmhf_dmaprot_getbuffersize(DMAPROT_PHY_ADDR_SPACE_SIZE); // ADDR_512GB
				HALT_ON_ERRORCOND(protectedbuffer_size <= SIZE_G_RNTM_DMAPROT_BUFFER);

				printf("\nRuntime: Re-initializing DMA protection (physical address space size:0x%llX)...", DMAPROT_PHY_ADDR_SPACE_SIZE);
				if(!xmhf_dmaprot_initialize(protectedbuffer_paddr, protectedbuffer_vaddr, protectedbuffer_size)){
					printf("\nRuntime: Unable to re-initialize DMA protection. HALT!");
					HALT();
				}

				//protect SL and runtime memory regions
				xmhf_dmaprot_protect(rpb->XtVmmRuntimePhysBase - PAGE_SIZE_2M, rpb->XtVmmRuntimeSize+PAGE_SIZE_2M);
				printf("\nRuntime: Protected SL+Runtime (%08lx-%08x) from DMA.", rpb->XtVmmRuntimePhysBase - PAGE_SIZE_2M, rpb->XtVmmRuntimePhysBase+rpb->XtVmmRuntimeSize);
		}

#else //!__DMAP__

	#if defined (__DRT__)
	//if __DRT__ is enabled without DMA protections, zap DMAR device
	//from ACPI tables
	if(cpu_vendor == CPU_VENDOR_INTEL){
		vmx_eap_zap();
	}
	#endif	//__DRT__

#endif

	//initialize base platform with SMP
	xmhf_baseplatform_smpinitialize();

	printf("\nRuntime: We should NEVER get here!");
	HALT_ON_ERRORCOND(0);
}

//we get control here in the context of *each* physical CPU core
//vcpu->isbsp = 1 if the core is a BSP or 0 if its an AP
//isEarlyInit = 1 if we were boot-strapped by the BIOS and is 0
//in the event we were launched from a running OS
void xmhf_runtime_main(VCPU *vcpu, u32 isEarlyInit){

  //initialize CPU
  xmhf_baseplatform_cpuinitialize();

  //initialize partition monitor (i.e., hypervisor) for this CPU
  xmhf_partition_initializemonitor(vcpu);

  //setup guest OS state for partition
  xmhf_partition_setupguestOSstate(vcpu);

  //initialize memory protection for this core
  xmhf_memprot_initialize(vcpu);

  //initialize application parameter block and call app main
  {
    APP_PARAM_BLOCK appParamBlock;

    appParamBlock.bootsector_ptr = rpb->XtGuestOSBootModuleBase;
    appParamBlock.bootsector_size = rpb->XtGuestOSBootModuleSize;
    appParamBlock.optionalmodule_ptr = rpb->runtime_appmodule_base;
    appParamBlock.optionalmodule_size = rpb->runtime_appmodule_size;
    appParamBlock.runtimephysmembase = rpb->XtVmmRuntimePhysBase;
    appParamBlock.boot_drive = rpb->XtGuestOSBootDrive;
    COMPILE_TIME_ASSERT(sizeof(appParamBlock.cmdline) >= sizeof(rpb->cmdline));
    #ifndef __XMHF_VERIFICATION__
    strncpy(appParamBlock.cmdline, rpb->cmdline, sizeof(appParamBlock.cmdline));
    #endif

    //call app main
    if(xmhf_app_main(vcpu, &appParamBlock)){
        printf("\nCPU(0x%02x): EMHF app. failed to initialize. HALT!", vcpu->id);
        HALT();
    }
  }

#ifndef __XMHF_VERIFICATION__
  //increment app main success counter
  spin_lock(&g_lock_appmain_success_counter);
  g_appmain_success_counter++;
  spin_unlock(&g_lock_appmain_success_counter);

  //if BSP, wait for all cores to go through app main successfully
  //TODO: conceal g_midtable_numentries behind interface
  //xmhf_baseplatform_getnumberofcpus
  if(vcpu->isbsp && (g_midtable_numentries > 1)){
		printf("\nCPU(0x%02x): Waiting for all cores to cycle through appmain...", vcpu->id);
		while(g_appmain_success_counter < g_midtable_numentries);
		printf("\nCPU(0x%02x): All cores have successfully been through appmain.", vcpu->id);
  }
#endif

  //late initialization is still WiP and we can get only this far
  //currently
	if(!isEarlyInit){
		printf("\nCPU(0x%02x): Late-initialization, WiP, HALT!", vcpu->id);
		HALT();
	}

#ifndef __XMHF_VERIFICATION__
  //initialize support for SMP guests
  xmhf_smpguest_initialize(vcpu);
#endif

  //start partition (guest)
  printf("\n%s[%02x]: starting partition...", __FUNCTION__, vcpu->id);
  xmhf_partition_start(vcpu);

  printf("\nCPU(0x%02x): FATAL, should not be here. HALTING!", vcpu->id);
  HALT();
}
