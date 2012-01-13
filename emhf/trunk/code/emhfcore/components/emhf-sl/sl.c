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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

#include <emhf.h> 
#include <sha1.h>

extern u32 slpb_buffer[];
RPB * rpb;
u32 sl_baseaddr=0;	


/* SHA-1 hash of runtime should be defined during build process.
 * However, if it's not, don't fail.  Just proceed with all zeros.
 * XXX TODO Disable proceeding with insecure hash value. */
#ifndef ___RUNTIME_INTEGRITY_HASH___
#define ___RUNTIME_INTEGRITY_HASH___ BAD_INTEGRITY_HASH
#endif /*  ___RUNTIME_INTEGRITY_HASH___ */

//this is the SL parameter block and is placed in a seperate UNTRUSTED
//section
struct _sl_parameter_block slpb __attribute__(( section(".sl_untrusted_params") )) = {
	.magic = SL_PARAMETER_BLOCK_MAGIC,
};



#define SERIAL_BASE 0x3f8
void raw_serial_init(void){
    // enable DLAB and set baudrate 115200
    outb(SERIAL_BASE+0x3, 0x80);
    outb(SERIAL_BASE+0x0, 0x01);
    outb(SERIAL_BASE+0x1, 0x00);
    // disable DLAB and set 8N1
    outb(SERIAL_BASE+0x3, 0x03);
    // reset IRQ register
    outb(SERIAL_BASE+0x1, 0x00);
    // enable fifo, flush buffer, enable fifo
    outb(SERIAL_BASE+0x2, 0x01);
    outb(SERIAL_BASE+0x2, 0x07);
    outb(SERIAL_BASE+0x2, 0x01);
    // set RTS,DTR
    outb(SERIAL_BASE+0x4, 0x03);
}




//we get here from slheader.S
// rdtsc_* are valid only if PERF_CRIT is not defined.  slheader.S
// sets them to 0 otherwise.
void slmain(u32 cpu_vendor, u32 baseaddr, u32 rdtsc_eax, u32 rdtsc_edx){
	//SL_PARAMETER_BLOCK *slpb;
	u32 runtime_physical_base;
	u32 runtime_size_2Maligned;
	
	u32 runtime_gdt;
	u32 runtime_idt;
	u32 runtime_entrypoint;
	u32 runtime_topofstack;

	ASSERT( (u32)&slpb == 0x10000 ); //linker relocates sl image starting from 0, so
                                         //parameter block must be at offset 0x10000    

	//we currently only support x86 (AMD and Intel)
	ASSERT (cpu_vendor == CPU_VENDOR_AMD || cpu_vendor == CPU_VENDOR_INTEL);
	
	//initialize debugging early on
	#ifdef __DEBUG_SERIAL__
			g_uart_config = slpb.uart_config;
			init_uart();
	#endif

	#ifdef __DEBUG_VGA__
		vgamem_clrscr();
	#endif
	
	//dump SL parameter block address
	printf("\nSL: slpb at = 0x%08x", (u32)&slpb);

	//initialze sl_baseaddr variable and print its value out
	sl_baseaddr = baseaddr;
	
	if(slpb.isEarlyInit)
		printf("\nSL(early-init): at 0x%08x, starting...", sl_baseaddr);    
    else
		printf("\nSL(late-init): at 0x%08x, starting...", sl_baseaddr);
		

	ASSERT( slpb.magic == SL_PARAMETER_BLOCK_MAGIC);
	
	printf("\n	hashSL=0x%08x", slpb.hashSL);
	printf("\n	errorHandler=0x%08x", slpb.errorHandler);
	printf("\n	isEarlyInit=0x%08x", slpb.isEarlyInit);
	printf("\n	numE820Entries=%u", slpb.numE820Entries);
	printf("\n	e820map at 0x%08x", (u32)&slpb.e820map);
	printf("\n	numCPUEntries=%u", slpb.numCPUEntries);
	printf("\n	pcpus at 0x%08x", (u32)&slpb.pcpus);
	printf("\n	runtime size= %u bytes", slpb.runtime_size);
	printf("\n	OS bootmodule at 0x%08x, size=%u bytes", 
		slpb.runtime_osbootmodule_base, slpb.runtime_osbootmodule_size);

    slpb.rdtsc_after_drtm = (u64)rdtsc_eax | ((u64)rdtsc_edx << 32);
    printf("\nSL: RDTSC before_drtm 0x%llx, after_drtm 0x%llx",
           slpb.rdtsc_before_drtm, slpb.rdtsc_after_drtm);
    printf("\nSL: [PERF] RDTSC DRTM elapsed cycles: 0x%llx",
           slpb.rdtsc_after_drtm - slpb.rdtsc_before_drtm);
    
  //debug, dump E820 and MP table
 	printf("\n	e820map:\n");
  {
    u32 i;
    for(i=0; i < slpb.numE820Entries; i++){
      printf("\n		0x%08x%08x, size=0x%08x%08x (%u)", 
          slpb.e820map[i].baseaddr_high, slpb.e820map[i].baseaddr_low,
          slpb.e820map[i].length_high, slpb.e820map[i].length_low,
          slpb.e820map[i].type);
    }
  }
  printf("\n	pcpus:\n");
  {
    u32 i;
    for(i=0; i < slpb.numCPUEntries; i++)
      printf("\n		CPU #%u: bsp=%u, lapic_id=0x%02x", i, slpb.pcpus[i].isbsp, slpb.pcpus[i].lapic_id);
  }


	//get runtime physical base
	runtime_physical_base = sl_baseaddr + PAGE_SIZE_2M;	//base of SL + 2M
	
	//compute 2M aligned runtime size
	runtime_size_2Maligned = PAGE_ALIGN_UP2M(slpb.runtime_size);

	printf("\nSL: runtime at 0x%08x (2M aligned size= %u bytes)", 
			runtime_physical_base, runtime_size_2Maligned);


	//initialize basic platform elements
	emhf_baseplatform_initialize();

	//initialize CPU (sets up MTRR settings etc.)
	//emhf_baseplatform_cpuinitialize();
	
	//sanitize cache/MTRR/SMRAM (most important is to ensure that MTRRs 
	//do not contain weird mappings)
    sanitize_post_launch();
    
    /* Note: calling this *before* paging is enabled is important */
    if(sl_integrity_check((u8*)PAGE_SIZE_2M, slpb.runtime_size)) // XXX base addr
        printf("\nsl_intergrity_check SUCCESS");
    else
        printf("\nsl_intergrity_check FAILURE");

	//get a pointer to the runtime header
 	rpb=(RPB *)PAGE_SIZE_2M;	//runtime starts at offset 2M from sl base
	printf("\nSL: RPB, magic=0x%08x", rpb->magic);
	ASSERT(rpb->magic == RUNTIME_PARAMETER_BLOCK_MAGIC);

    
	//setup DMA protection on runtime (secure loader is already DMA protected)
	early_dmaprot_init(slpb.runtime_size);
		
	//tell runtime if we started "early" or "late"
	rpb->isEarlyInit = slpb.isEarlyInit;
		
    //store runtime physical and virtual base addresses along with size
  	rpb->XtVmmRuntimePhysBase = runtime_physical_base;
  	rpb->XtVmmRuntimeVirtBase = __TARGET_BASE;
  	rpb->XtVmmRuntimeSize = slpb.runtime_size;

    //store revised E820 map and number of entries
	memcpy(hva2sla(rpb->XtVmmE820Buffer), (void *)&slpb.e820map, (sizeof(GRUBE820) * slpb.numE820Entries));
  	rpb->XtVmmE820NumEntries = slpb.numE820Entries; 

	//store CPU table and number of CPUs
    memcpy(hva2sla(rpb->XtVmmMPCpuinfoBuffer), (void *)&slpb.pcpus, (sizeof(PCPU) * slpb.numCPUEntries));
  	rpb->XtVmmMPCpuinfoNumEntries = slpb.numCPUEntries; 

   	//setup guest OS boot module info in LPB	
	rpb->XtGuestOSBootModuleBase=slpb.runtime_osbootmodule_base;
	rpb->XtGuestOSBootModuleSize=slpb.runtime_osbootmodule_size;

    // pass command line configuration forward 
    rpb->uart_config = g_uart_config;

	////debug dump uart_config field
    //printf("\nrpb->uart_config.port = %x", rpb->uart_config.port);
	//printf("\nrpb->uart_config.clock_hz = %u", rpb->uart_config.clock_hz);
	//printf("\nrpb->uart_config.baud = %u", rpb->uart_config.baud);
	//printf("\nrpb->uart_config.data_bits, parity, stop_bits, fifo = %x %x %x %x", 
	//	rpb->uart_config.data_bits, rpb->uart_config.parity, rpb->uart_config.stop_bits, rpb->uart_config.fifo);*/


	//setup runtime TSS
	{
			TSSENTRY *t;
	  	u32 tss_base=(u32)rpb->XtVmmTSSBase;
	  	u32 gdt_base= *(u32 *)(hva2sla(rpb->XtVmmGdt + 2));
	
			//fix TSS descriptor, 18h
			t= (TSSENTRY *)((u32)gdt_base + __TRSEL );
		  t->attributes1= 0x89;
		  t->limit16_19attributes2= 0x10;
		  t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
		  t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
		  t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);      
		  t->limit0_15=0x67;
	}
	printf("\nSL: setup runtime TSS.");	


	//obtain runtime gdt, idt, entrypoint and stacktop values and patch
	//entry point in XtLdrTransferControltoRtm
	{
			extern u32 sl_runtime_entrypoint_patch[];
			u32 *patchloc = (u32 *)((u32)sl_runtime_entrypoint_patch + 1);
			
			runtime_gdt = rpb->XtVmmGdt;
			runtime_idt = rpb->XtVmmIdt;
			runtime_entrypoint = rpb->XtVmmEntryPoint;
			runtime_topofstack = rpb->XtVmmStackBase+rpb->XtVmmStackSize; 
			printf("\nSL: runtime entry values:");
			printf("\n	gdt=0x%08x, idt=0x%08x", runtime_gdt, runtime_idt);
			printf("\n	entrypoint=0x%08x, topofstack=0x%08x", runtime_entrypoint, runtime_topofstack);
			*patchloc = runtime_entrypoint;
	}
		
		
	//setup paging for runtime 
	runtime_setup_paging(rpb, runtime_physical_base, __TARGET_BASE, runtime_size_2Maligned);
	printf("\nSL: setup runtime paging.");        

	//transfer control to runtime
	sl_xfer_control_to_runtime(runtime_gdt, runtime_idt, 
				runtime_entrypoint, runtime_topofstack);

	//we should never get here
	printf("\nSL: Fatal, should never be here!");
	HALT();
} 

