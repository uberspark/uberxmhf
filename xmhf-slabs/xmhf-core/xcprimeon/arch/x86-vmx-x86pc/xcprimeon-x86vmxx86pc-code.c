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

/**
 * XMHF core primeon slab (xcprimeon), x86-vmx-x86pc backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcprimeon.h>

__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__(( align(4096) )) void xcprimeon_arch_entry(void) {

	asm volatile (	".global _mle_page_table_start \r\n"
					"_mle_page_table_start:\r\n"
					".fill 4096, 1, 0 \r\n"
					".fill 4096, 1, 0 \r\n"
					".fill 4096, 1, 0 \r\n"
					".global _mle_page_table_end \r\n"
					"_mle_page_table_end: \r\n"
					".global _mle_hdr \r\n"
					"_mle_hdr:\r\n"
					".fill 0x80, 1, 0x90\r\n" //TODO: should really be sizeof(mle_hdr_t)
					".global _sl_start \r\n"
					"_sl_start: \r\n"
					"movw %%ds, %%ax \r\n"
					"movw %%ax, %%fs \r\n"
					"movw %%ax, %%gs \r\n"
					"movw %%ax, %%ss \r\n"
					"movl $0x10200000, %%esp \r\n" //TODO: get rid of hard-coded stack top
					"jmp xcprimeon_entry \r\n"
			    :
			    :
	);
}


//initialize GDT
static void _xcprimeon_cpu_x86_initializeGDT(void){

	asm volatile(
		"lgdt  %0 \r\n"
		"pushl	%1 \r\n"				// far jump to runtime entry point
		"pushl	$reloadsegs \r\n"
		"lret \r\n"
		"reloadsegs: \r\n"
		"movw	%2, %%ax \r\n"
		"movw	%%ax, %%ds \r\n"
		"movw	%%ax, %%es \r\n"
		"movw	%%ax, %%fs \r\n"
		"movw	%%ax, %%gs \r\n"
		"movw  %%ax, %%ss \r\n"
		: //no outputs
		: "m" (_gdt), "i" (__CS_CPL0), "i" (__DS_CPL0)
		: //no clobber
	);


}

//initialize IO privilege level
static void _xcprimeon_cpu_x86_initializeIOPL(void){

	asm volatile(
		"pushl	$0x3000 \r\n"					// clear flags, but set IOPL=3 (CPL-3)
		"popf \r\n"
		: //no outputs
		: //no inputs
		: //no clobber
	);


}


__attribute__((section(".stack"))) __attribute__(( aligned(4096) )) static u8 _tss_stack[PAGE_SIZE_4K];

//initialize TSS
static void _xcprimeon_cpu_x86_initializeTSS(void){
		u32 i;
		u32 tss_base=(u32)&_tss;
		TSSENTRY *t;
		tss_t *tss= (tss_t *)_tss;

		tss->ss0 = __DS_CPL0;
		tss->esp0 = (u32)_tss_stack + PAGE_SIZE_4K;

		_XDPRINTF_("\nfixing TSS descriptor (TSS base=%x)...", tss_base);
		t= (TSSENTRY *)(u32)&_gdt_start[(__TRSEL/sizeof(u64))];
		t->attributes1= 0xE9;
		t->limit16_19attributes2= 0x0;
		t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
		t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
		t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);
		t->limit0_15=0x67;
		_XDPRINTF_("\nTSS descriptor fixed.");

}


//initialize basic exception handling
static void _xcprimeon_initialize_exceptionhandling(void){
	u32 *pexceptionstubs;
	u32 i;

	for(i=0; i < EMHF_XCPHANDLER_MAXEXCEPTIONS; i++){
		idtentry_t *idtentry=(idtentry_t *)((u32)&_idt_start+ (i*8));
		//idtentry->isrLow= (u16)__xcprimeon_exceptionstubs[i];
		//idtentry->isrHigh= (u16) ( (u32)__xcprimeon_exceptionstubs[i] >> 16 );
		idtentry->isrLow= (u16)_exceptionstubs[i];
		idtentry->isrHigh= (u16) ( (u32)_exceptionstubs[i] >> 16 );
		idtentry->isrSelector = __CS_CPL0;
		idtentry->count=0x0;
		idtentry->type=0xEE;	//32-bit interrupt gate
								//present=1, DPL=11b, system=0, type=1110b
	}

}

static u8 vtd_ret_table[PAGE_SIZE_4K]; //4KB Vt-d Root-Entry table

//protect a given physical range of memory (membase to membase+size)
//using VT-d PMRs
//return true if everything went fine, else false
static bool _xcprimeon_vtd_dmaprotect(u32 membase, u32 size){
	vtd_drhd_handle_t drhd_handle;
	u32 vtd_dmar_table_physical_address=0;
	vtd_drhd_handle_t vtd_drhd_maxhandle;

	_XDPRINTF_("\n%s: size=%08x", __FUNCTION__, size);

	//scan for available DRHD units in the platform
	if(!xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(&vtd_drhd_maxhandle, &vtd_dmar_table_physical_address))
		return false;

	//zero out RET; will be used to prevent DMA reads and writes
	//for the entire system
	memset((void *)&vtd_ret_table, 0, sizeof(vtd_ret_table));

	//initialize all DRHD units
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
		_XDPRINTF_("\n%s: Setting up DRHD unit %u...", __FUNCTION__, drhd_handle);

		if(!xmhfhw_platform_x86pc_vtd_drhd_initialize(drhd_handle) )
			return false;

		//setup blanket (full system) DMA protection using VT-d translation
		//we just employ the RET and ensure that every entry in the RET is 0
		//which means that the DRHD will
		//not allow any DMA requests for PCI bus 0-255
		//(Sec 3.3.2, VT-d Spec. v1.2)

		//set DRHD root entry table
		if(!xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table(drhd_handle, (u8 *)&vtd_ret_table))
			return false;

		//invalidate caches
		if(!xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(drhd_handle))
			return false;

		//enable VT-d translation
		xmhfhw_platform_x86pc_vtd_drhd_enable_translation(drhd_handle);

		//disable PMRs now (since DMA protection is active via translation)
		xmhfhw_platform_x86pc_vtd_drhd_disable_pmr(drhd_handle);

		//set PMR low base and limit to cover SL+runtime
		xmhfhw_platform_x86pc_vtd_drhd_set_plm_base_and_limit(drhd_handle, (u32)PAGE_ALIGN_2M(membase), (u32)(PAGE_ALIGN_2M(membase) + PAGE_ALIGN_UP2M(size)) );

		//set PMR high base and limit to cover SL+runtime
		xmhfhw_platform_x86pc_vtd_drhd_set_phm_base_and_limit(drhd_handle, (u64)PAGE_ALIGN_2M(membase), (u64)(PAGE_ALIGN_2M(membase) + PAGE_ALIGN_UP2M(size)) );

		//enable PMRs
		xmhfhw_platform_x86pc_vtd_drhd_enable_pmr(drhd_handle);

		//invalidate caches
		if(!xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(drhd_handle))
			return false;

		//disable translation (now that PMRs are active and protect SL+runtime)
		xmhfhw_platform_x86pc_vtd_drhd_disable_translation(drhd_handle);

	}

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	xmhfhw_sysmemaccess_writeu32(vtd_dmar_table_physical_address, 0UL);

	//success
	_XDPRINTF_("\n%s: success, leaving...", __FUNCTION__);

	return true;
}


static u64 _pdpt[PAE_MAXPTRS_PER_PDPT] __attribute__(( aligned(4096) ));
static u64 _pdt[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT] __attribute__(( aligned(4096) ));

static u64 _xcprimeon_getptflagsforspa(u32 spa){
	u64 flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_PSE);
	if(spa == 0xfee00000 || spa == 0xfec00000) {
		//map some MMIO regions with Page Cache disabled
		//0xfed00000 contains Intel TXT config regs & TPM MMIO
		//0xfee00000 contains LAPIC base
		flags |= (u64)(_PAGE_PCD);
	}
	return flags;
}

// initialize page tables and return page table base
static u32 _xcprimeon_populate_pagetables(void){
		u32 i, j;
		u64 default_flags = (u64)(_PAGE_PRESENT);

		for(i=0; i < PAE_PTRS_PER_PDPT; i++)
			_pdpt[i] = pae_make_pdpe(hva2spa(_pdt[i]), default_flags);

		//init pdts with unity mappings
		for(i=0; i < PAE_PTRS_PER_PDPT; i++){
			for(j=0; j < PAE_PTRS_PER_PDT; j++){
				u32 hva = ((i * PAE_PTRS_PER_PDT) + j) * PAGE_SIZE_2M;
				u64 spa = hva2spa((void*)hva);
				u64 flags = _xcprimeon_getptflagsforspa((u32)spa);
				_pdt[i][j] = pae_make_pde_big(spa, flags);
			}
		}

		return (u32)_pdpt;
}



//=========================================================================================

//perform basic (boot) CPU initialization
void xcprimeon_arch_cpu_basicinit(void){
	u32 cpu_vendor;

	//grab CPU vendor
	cpu_vendor = xmhf_baseplatform_arch_getcpuvendor();
	if (cpu_vendor != CPU_VENDOR_INTEL){
		_XDPRINTF_("%s: not an Intel CPU but running VMX backend. Halting!", __FUNCTION__);
		HALT();
	}

	//check VMX support
	{
		u32	cpu_features;
		asm volatile(	"mov	$1, %%eax \n"
						"cpuid \n"
						"mov	%%ecx, %0	\n"
					:
					:"m"(cpu_features)
					: "eax", "ebx", "ecx", "edx"
					);
		if ( ( cpu_features & (1<<5) ) == 0 ){
			_XDPRINTF_("No VMX support. Halting!");
			HALT();
		}
	}

	//set OSXSAVE bit in CR4 to enable us to pass-thru XSETBV intercepts
	//when the CPU supports XSAVE feature
	if(xmhf_baseplatform_arch_x86_cpuhasxsavefeature()){
		u32 t_cr4;
		t_cr4 = read_cr4();
		t_cr4 |= CR4_OSXSAVE;
		write_cr4(t_cr4);
	}

	//turn on NX protections
	{
		u32 eax, edx;
		rdmsr(MSR_EFER, &eax, &edx);
		eax |= (1 << EFER_NXE);
		wrmsr(MSR_EFER, eax, edx);
		_XDPRINTF_("\n%s: NX protections enabled: MSR_EFER=%08x%08x", __FUNCTION__, edx, eax);
	}

	//initialize TSS
	_xcprimeon_cpu_x86_initializeTSS();

	//initialize basic exception handling
	_XDPRINTF_("%s: proceeding to initialize basic exception handling\n", __FUNCTION__);
	_xcprimeon_initialize_exceptionhandling();
	_XDPRINTF_("%s: basic exception handling initialized\n", __FUNCTION__);
}

//initialize basic platform elements
void xcprimeon_arch_platform_initialize(void){
	//initialize platform bus
	xmhfhw_platform_bus_init();

	//check ACPI subsystem
	{
		ACPI_RSDP rsdp;
		if(!xmhfhw_platform_x86pc_acpi_getRSDP(&rsdp)){
			_XDPRINTF_("\n%s: ACPI RSDP not found, Halting!", __FUNCTION__);
			HALT();
		}
	}
}


void xcprimeon_arch_cpu_activate_modeandpaging(u64 pgtblbase){
	u32 coreptbase;

	//initialize paging
    write_cr4(read_cr4() | (u32)0x00000030); //CR4_PAE | CR4_PSE

    write_cr3((u32)pgtblbase);

    write_cr0(read_cr0() | (u32)0x80000015); // ET, EM, PE, PG

	_XDPRINTF_("\n%s: setup page tables\n", __FUNCTION__);

	//initialize GDT
	_xcprimeon_cpu_x86_initializeGDT();

	//load IDT
	asm volatile(
		"lidt  %0 \r\n"
		: //no outputs
		: "m" (_idt)
		: //no clobber
	);


	//initialize IO privilege level
	_xcprimeon_cpu_x86_initializeIOPL();

}


///////////////////////////////////////////////////////////////////////////////

void xcprimeon_arch_postdrt(void){
	txt_heap_t *txt_heap;
	os_mle_data_t *os_mle_data;

	txt_heap = get_txt_heap();
	_XDPRINTF_("SL: txt_heap = 0x%08x\n", (u32)txt_heap);
	os_mle_data = get_os_mle_data_start((txt_heap_t*)((u32)txt_heap));
	_XDPRINTF_("SL: os_mle_data = 0x%08x\n", (u32)os_mle_data);

	// restore pre-SENTER MTRRs that were overwritten for SINIT launch
	if(!validate_mtrrs(&(os_mle_data->saved_mtrr_state))) {
		_XDPRINTF_("SECURITY FAILURE: validate_mtrrs() failed.\n");
		HALT();
	}
	_XDPRINTF_("SL: Validated MTRRs\n");

	xmhfhw_cpu_x86_restore_mtrrs(&(os_mle_data->saved_mtrr_state));
    _XDPRINTF_("SL: Restored MTRRs\n");
}

void xcprimeon_arch_earlydmaprot(u32 membase, u32 size){
	_XDPRINTF_("SL: Initializing DMA protections...\n");

	if(!_xcprimeon_vtd_dmaprotect(membase, size)){
		_XDPRINTF_("SL: Fatal, could not initialize DMA protections. Halting!\n");
		HALT();
	}else{
		_XDPRINTF_("SL: Initialized DMA protections successfully\n");
	}
}

// initialization function for the core API interface
u64 xcprimeon_arch_initialize_page_tables(void){
	u32 pgtblbase;

	_XDPRINTF_("\n%s: starting...", __FUNCTION__);

	pgtblbase = _xcprimeon_populate_pagetables();

	_XDPRINTF_("\n%s: setup page tables\n", __FUNCTION__);

    return (u64)pgtblbase;
}
