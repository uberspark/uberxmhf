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

//sl.c
//secure loader implementation
//author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>

RPB * rpb;
u32 sl_baseaddr=0;

//this is the SL parameter block and is placed in a seperate UNTRUSTED
//section. It is populated by the "init" (late or early) loader, which
//uses the late-launch mechanism to load the SL
struct _sl_parameter_block slpb __attribute__(( section(".sl_untrusted_params") )) = {
	.magic = SL_PARAMETER_BLOCK_MAGIC,
};


//we get here from slheader.S
// rdtsc_* are valid only if PERF_CRIT is not defined.  slheader.S
// sets them to 0 otherwise.
void xmhf_sl_main(u32 cpu_vendor, u32 baseaddr, u32 rdtsc_eax, u32 rdtsc_edx){


	u32 runtime_physical_base;
	u32 runtime_size_2Maligned;

#ifdef __AMD64__
	xmhf_setup_sl_paging(baseaddr);
#elif !defined(__I386__)
    #error "Unsupported Arch"
#endif /* !defined(__I386__) */

	//linker relocates sl image starting from 0, so
    //parameter block must be at offset 0x10000
	HALT_ON_ERRORCOND( (sla_t)&slpb == 0x10000 );

	//do we have the required MAGIC?
	HALT_ON_ERRORCOND( slpb.magic == SL_PARAMETER_BLOCK_MAGIC);

	//we currently only support x86 (AMD and Intel)
	HALT_ON_ERRORCOND (cpu_vendor == CPU_VENDOR_AMD || cpu_vendor == CPU_VENDOR_INTEL);

	//initialize debugging early on
	xmhf_debug_init((char *)&slpb.uart_config);

	//initialze sl_baseaddr variable and print its value out
	sl_baseaddr = baseaddr;

	//is our launch before the OS has been loaded (early) is loaded or
	//is it after the OS has been loaded (late)
	if(slpb.isEarlyInit)
		printf("SL(early-init): at 0x%08x, starting...\n", sl_baseaddr);
    else
		printf("SL(late-init): at 0x%08x, starting...\n", sl_baseaddr);

	//debug: dump SL parameter block
	printf("SL: slpb at = 0x%08lx\n", (sla_t)&slpb);
	printf("	errorHandler=0x%08x\n", slpb.errorHandler);
	printf("	isEarlyInit=0x%08x\n", slpb.isEarlyInit);
	printf("	numE820Entries=%u\n", slpb.numE820Entries);
	printf("	system memory map buffer at 0x%08lx\n", (sla_t)&slpb.memmapbuffer);
	printf("	numCPUEntries=%u\n", slpb.numCPUEntries);
	printf("	cpuinfo buffer at 0x%08lx\n", (sla_t)&slpb.cpuinfobuffer);
	printf("	runtime size= %u bytes\n", slpb.runtime_size);
	printf("	OS bootmodule at 0x%08x, size=%u bytes\n",
		slpb.runtime_osbootmodule_base, slpb.runtime_osbootmodule_size);
    printf("  OS boot_drive is 0x%02x\n", (u32)slpb.runtime_osbootdrive);
    printf("\tcmdline = \"%s\"\n", slpb.cmdline);

	//debug: if we are doing some performance measurements
    slpb.rdtsc_after_drtm = (u64)rdtsc_eax | ((u64)rdtsc_edx << 32);
    printf("SL: RDTSC before_drtm 0x%llx, after_drtm 0x%llx\n",
           slpb.rdtsc_before_drtm, slpb.rdtsc_after_drtm);
    printf("SL: [PERF] RDTSC DRTM elapsed cycles: 0x%llx\n",
           slpb.rdtsc_after_drtm - slpb.rdtsc_before_drtm);

	//get runtime physical base
	runtime_physical_base = sl_baseaddr + PAGE_SIZE_2M;	//base of SL + 2M

	//compute 2M aligned runtime size
	runtime_size_2Maligned = PAGE_ALIGN_UP_2M((ulong_t)slpb.runtime_size);

	printf("SL: runtime at 0x%08x; size=0x%08x bytes adjusted to 0x%08x bytes (2M aligned)\n",
			runtime_physical_base, slpb.runtime_size, runtime_size_2Maligned);

	//setup runtime parameter block with required parameters
	{
	#ifndef __XMHF_VERIFICATION__
		//get a pointer to the runtime header and make sure its sane
		rpb=(RPB *)PAGE_SIZE_2M;	//runtime starts at offset 2M from sl base
	#else
		//setup runtime parameter block pointer
		//actual definitions
		extern RPB _xrpb;
		rpb = (RPB *)&_xrpb;
	#endif

		printf("SL: RPB, magic=0x%08x\n", rpb->magic);
		HALT_ON_ERRORCOND(rpb->magic == RUNTIME_PARAMETER_BLOCK_MAGIC);

		//populate runtime parameter block fields
		rpb->isEarlyInit = slpb.isEarlyInit; //tell runtime if we started "early" or "late"

		//store runtime physical and virtual base addresses along with size
		rpb->XtVmmRuntimePhysBase = runtime_physical_base;
		rpb->XtVmmRuntimeVirtBase = __TARGET_BASE;
		rpb->XtVmmRuntimeSize = slpb.runtime_size;

#ifdef __SKIP_RUNTIME_BSS__
#ifdef __DRT__
	#error "__SKIP_RUNTIME_BSS__ not supported when __DRT__"
#endif /* __DRT__ */

		{
			u32 rt_bss_phys_begin = rpb->XtVmmRuntimeBssBegin - __TARGET_BASE_SL;
			u32 rt_bss_size = rpb->XtVmmRuntimeBssEnd - rpb->XtVmmRuntimeBssBegin;
			memset((void *)(uintptr_t)rt_bss_phys_begin, 0, rt_bss_size);
		}
#endif /* __SKIP_RUNTIME_BSS__ */

		//store revised E820 map and number of entries
		#ifndef __XMHF_VERIFICATION__
		memcpy(hva2sla((void *)rpb->XtVmmE820Buffer), (void *)&slpb.memmapbuffer, (sizeof(slpb.memmapbuffer)) );
		#endif
		rpb->XtVmmE820NumEntries = slpb.numE820Entries;

		//store CPU table and number of CPUs
		#ifndef __XMHF_VERIFICATION__
		memcpy(hva2sla((void *)rpb->XtVmmMPCpuinfoBuffer), (void *)&slpb.cpuinfobuffer, (sizeof(PCPU) * slpb.numCPUEntries) );
		#endif
		rpb->XtVmmMPCpuinfoNumEntries = slpb.numCPUEntries;

		//setup guest OS boot module info in LPB
		rpb->XtGuestOSBootModuleBase=(hva_t)(slpb.runtime_osbootmodule_base);
		rpb->XtGuestOSBootModuleSize=(hva_t)(slpb.runtime_osbootmodule_size);

		//pass optional app module if any
		rpb->runtime_appmodule_base = (hva_t)(slpb.runtime_appmodule_base);
		rpb->runtime_appmodule_size = (hva_t)(slpb.runtime_appmodule_size);

		rpb->XtGuestOSBootDrive = slpb.runtime_osbootdrive;

	#if defined (__DEBUG_SERIAL__)
		//pass along UART config for serial debug output
		rpb->RtmUartConfig = slpb.uart_config;
	#endif

		//pass command line configuration forward
		COMPILE_TIME_ASSERT(sizeof(slpb.cmdline) == sizeof(rpb->cmdline));
	#ifndef __XMHF_VERIFICATION__
		strncpy(rpb->cmdline, slpb.cmdline, sizeof(slpb.cmdline));
	#endif

	}

	//initialize basic platform elements
	xmhf_baseplatform_initialize();

	//sanitize cache/MTRR/SMRAM (most important is to ensure that MTRRs
	//do not contain weird mappings)
#if defined (__DRT__)
    xmhf_sl_arch_sanitize_post_launch();
#endif	//__DRT__

#if defined (__DMAP__)
	//setup DMA protection on runtime (secure loader is already DMA protected)
	xmhf_sl_arch_early_dmaprot_init(slpb.runtime_size);
#endif

	//transfer control to runtime
	xmhf_sl_arch_xfer_control_to_runtime(rpb);

#ifndef __XMHF_VERIFICATION__
	//we should never get here
	printf("SL: Fatal, should never be here!\n");
	HALT();
#else
	return;
#endif
}
