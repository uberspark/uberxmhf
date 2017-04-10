#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <atags.h>
#include <fdt.h>
#include <debug.h>


extern void chainload_os(u32 r0, u32 id, struct atag *at);
//extern void cpumodeswitch_hyp2svc(u32 address);
extern void cpumodeswitch_hyp2svc(u32 r0, u32 id, struct atag *at, u32 address, u32 cpuid);

extern void entry_svc(void);

extern u32 g_hypvtable[];

u32 guestos_boot_r0=0;
u32 guestos_boot_r1=0;
u32 guestos_boot_r2=0;


void hyp_rsvhandler(void){
	bcm2837_miniuart_puts("uXMHF-rpi3: core: unhandled exception\n");
	bcm2837_miniuart_puts("uXMHF-rpi3: core: Halting!\n");
	HALT();
}


void hyphvc_handler(void){
	bcm2837_miniuart_puts("uXMHF-rpi3: core: hyphvc_handler [IN]\n");
	bcm2837_miniuart_puts("uXMHF-rpi3: core: Hello world from hypercall\n");
	bcm2837_miniuart_puts("uXMHF-rpi3: core: hyphvc_handler [OUT]\n");


/*	_XDPRINTFSMP_("uXMHF-rpi3: core: hyphvc_handler [IN]\n");
	_XDPRINTFSMP_("uXMHF-rpi3: core: Hello world from hypercall\n");
	_XDPRINTFSMP_("uXMHF-rpi3: core: hyphvc_handler [OUT]\n");
*/

}

void hypsvc_handler(void){
	u32 hsr;
	u32 elr_hyp;
	_XDPRINTFSMP_("%s: ENTER\n", __func__);

	//read hsr to determine the cause of the intercept
	hsr = sysreg_read_hsr();

	//bcm2837_miniuart_puts(" HSR= ");
	//debug_hexdumpu32(hsr);

	switch ( ((hsr & HSR_EC_MASK) >> HSR_EC_SHIFT) ){
		case HSR_EC_HVC:
			break;

		case HSR_EC_DATA_ABORT_ELCHANGE:
			//bcm2837_miniuart_puts("uXMHF-rpi3: core: s2pgtbl DATA access fault\n");
			//bcm2837_miniuart_puts(" HSR= ");
			//debug_hexdumpu32(hsr);

			elr_hyp = sysreg_read_elrhyp();
			//bcm2837_miniuart_puts(" ELR_hyp= ");
			//debug_hexdumpu32(elr_hyp);

			elr_hyp += sizeof(u32);
			sysreg_write_elrhyp(elr_hyp);

			//elr_hyp = sysreg_read_elrhyp();
			//bcm2837_miniuart_puts(" ELR_hyp [updated]= ");
			//debug_hexdumpu32(elr_hyp);
			break;

			//bcm2837_miniuart_puts("uXMHF-rpi3: core: Halting\n");
			//HALT();

		default:
			bcm2837_miniuart_puts("uXMHF-rpi3: core: UNHANDLED INTERCEPT!\n");
			bcm2837_miniuart_puts(" HSR= ");
			debug_hexdumpu32(hsr);
			bcm2837_miniuart_puts("uXMHF-rpi3: core: Halting\n");
			HALT();
	}

	_XDPRINTFSMP_("%s: EXIT\n", __func__);


}


void main_svc(u32 r0, u32 id, struct atag *at){
	u32 cpsr;

	_XDPRINTF_("%s: now in SVC mode\n", __func__);
	_XDPRINTF_("%s: r0=0x%08x, id=0x%08x, ATAGS=0x%08x\n", __func__, r0, id, at);

	_XDPRINTF_("%s: CPSR[mode]=0x%08x\n", __func__, (sysreg_read_cpsr() & 0xF));

	_XDPRINTF_("%s: proceeding to test hypercall (HVC) in SVC mode...\n", __func__);
	hypcall();
	_XDPRINTF_("%s: successful return after hypercall test\n", __func__);


	//_XDPRINTF_("%s: chainloading OS kernel...\n", __func__);
	//_XDPRINTF_("%s: r0=0x%08x, id=0x%08x, ATAGS=0x%08x\n", __func__, r0, id, at);
	//chainload_os(r0, id, at);

	_XDPRINTF_("%s: should not be here. Halting!\n", __func__);
	HALT();
}


void core_fixresmemmap(u32 fdt_address){
	struct fdt_header *fdth = (struct fdt_header *)fdt_address;
	struct fdt_reserve_entry *fdtrsvmmapentryp;
	u32 newtotalsize, padding;

	bcm2837_miniuart_puts("uxmhf-rpi3: core: core_fixresmemmap [IN]\n");

	bcm2837_miniuart_puts(" fdt_address=0x");
	debug_hexdumpu32(fdt_address);

	bcm2837_miniuart_puts(" totalsize=0x");
	debug_hexdumpu32(cpu_be2le_u32(fdth->totalsize));

	bcm2837_miniuart_puts(" off_dt_struct=0x");
	debug_hexdumpu32(cpu_be2le_u32(fdth->off_dt_struct));

	bcm2837_miniuart_puts(" size_dt_struct=0x");
	debug_hexdumpu32(cpu_be2le_u32(fdth->size_dt_struct));

	bcm2837_miniuart_puts(" off_dt_strings=0x");
	debug_hexdumpu32(cpu_be2le_u32(fdth->off_dt_strings));

	bcm2837_miniuart_puts(" size_dt_strings=0x");
	debug_hexdumpu32(cpu_be2le_u32(fdth->size_dt_strings));

	bcm2837_miniuart_puts(" off_mem_rsvmap=0x");
	debug_hexdumpu32(cpu_be2le_u32(fdth->off_mem_rsvmap));

	bcm2837_miniuart_puts(" version=0x");
	debug_hexdumpu32(cpu_be2le_u32(fdth->version));

	bcm2837_miniuart_puts(" last_comp_version=0x");
	debug_hexdumpu32(cpu_be2le_u32(fdth->last_comp_version));

	//pad totalsize to a page-boundary
	padding = PAGE_SIZE_4K - (cpu_be2le_u32(fdth->totalsize) % PAGE_SIZE_4K);
	bcm2837_miniuart_puts("padding=0x");
	debug_hexdumpu32(padding);

	//take totalsize and compute var = size + 8 * 2
	newtotalsize = cpu_be2le_u32(fdth->totalsize);
	newtotalsize += padding;
	newtotalsize += (2 * sizeof(struct fdt_reserve_entry));

	//put rsv_mem_off to size
	fdth->off_mem_rsvmap = cpu_le2be_u32(cpu_be2le_u32(fdth->totalsize) + padding);

	//set totalsize to var
	fdth->totalsize = cpu_le2be_u32(newtotalsize);

	//populate fdtrsvmmapentryp to rsv_mem_off
	fdtrsvmmapentryp = (struct fdt_reserve_entry *)(fdt_address + cpu_be2le_u32(fdth->off_mem_rsvmap));

	bcm2837_miniuart_puts("fdtrsvmmapentryp=0x");
	debug_hexdumpu32((u32)fdtrsvmmapentryp);
	bcm2837_miniuart_puts("sizeof(fdtrsvmmapentryp)=0x");
	debug_hexdumpu32(sizeof(struct fdt_reserve_entry));

	//write the guestos extent as first entry
	fdtrsvmmapentryp->address = cpu_le2be_u64(0x0000000030000000ULL);
	fdtrsvmmapentryp->size = cpu_le2be_u64(0x0000000000800000ULL);
	//fdtrsvmmapentryp->address = 0ULL;
	//fdtrsvmmapentryp->size = 0ULL;

	//terminate the list with 0sadd 16 bytes
	fdtrsvmmapentryp++;
	bcm2837_miniuart_puts("fdtrsvmmapentryp=0x");
	debug_hexdumpu32((u32)fdtrsvmmapentryp);

	fdtrsvmmapentryp->address = 0ULL;
	fdtrsvmmapentryp->size = 0ULL;

	//debug
	bcm2837_miniuart_puts("uxmhf-rpi3: core: dumping reserved memmap...\n");
	fdtrsvmmapentryp = (struct fdt_reserve_entry *)(fdt_address + cpu_be2le_u32(fdth->off_mem_rsvmap));
	bcm2837_miniuart_puts("fdtrsvmmapentryp=0x");
	debug_hexdumpu32((u32)fdtrsvmmapentryp);


	while(1){
		u64 addr = cpu_be2le_u64(fdtrsvmmapentryp->address);
		u64 size = cpu_be2le_u64(fdtrsvmmapentryp->size);
		if( addr == 0ULL &&  size == 0ULL){
			break;
		}
		bcm2837_miniuart_puts(" address:0x");
		debug_hexdumpu32(addr >> 32);
		debug_hexdumpu32((u32)addr);
		bcm2837_miniuart_puts(" size:0x");
		debug_hexdumpu32(size >> 32);
		debug_hexdumpu32((u32)size);
		fdtrsvmmapentryp++;
		bcm2837_miniuart_puts("fdtrsvmmapentryp=0x");
		debug_hexdumpu32((u32)fdtrsvmmapentryp);
	}

	bcm2837_miniuart_puts("uxmhf-rpi3: core: dumped reserved memmap...\n");

	bcm2837_miniuart_puts("uxmhf-rpi3: core: core_fixresmemmap [OUT]\n");
}


volatile __attribute__((aligned(32))) u32 my_lock=1;
extern u32 cpu_smpready[];
extern u8 cpu_stacks[];


void main(u32 r0, u32 id, struct atag *at){
	u32 hvbar, hcr, spsr_hyp;

	_XDPRINTF_("%s: ENTER: sp=0x%08x (cpu_stacks=0x%08x)\n", __func__,
			cpu_read_sp(), &cpu_stacks);

	_XDPRINTF_("uXMHF-rpi3: core: Hello World!\n");
	_XDPRINTF_(" r0=0x%08x, id=0x%08x, ATAGS=0x%08x\n", r0, id, at);

	if(!(at->size == FDT_MAGIC)){
		//bcm2837_miniuart_puts("uXMHF-rpi3: core: Error: require ATAGS to be FDT blob. Halting!\n");
		_XDPRINTF_("uXMHF-rpi3: core: Error: require ATAGS to be FDT blob. Halting!\n");
		HALT();
	}

	//bcm2837_miniuart_puts("uXMHF-rpi3: core: ATAGS pointer is a FDT blob so no worries\n");
	_XDPRINTF_("uXMHF-rpi3: core: ATAGS pointer is a FDT blob so no worries\n");

	//fix reserved memory map
	core_fixresmemmap((u32)at);


	bcm2837_platform_initialize();
	_XDPRINTF_("%s: initialized base hardware platform\n", __func__);

	hyppgtbl_populate_tables();
	_XDPRINTF_("%s: page-tables populated\n", __func__);

	hyppgtbl_activate();
	_XDPRINTF_("%s: hyp page-tables activated\n", __func__);

	// populate stage-2 page tables
	s2pgtbl_populate_tables();
	_XDPRINTF_("%s: stage-2 pts populated.\n", __func__);



/*
	_XDPRINTFSMP_("%s: lock variable at address=0x%08x\n", __func__, &my_lock);
	_XDPRINTFSMP_("%s: acquiring lock [current value=0x%08x]...\n", __func__, (u32)my_lock);
	spin_lock(&my_lock);
	_XDPRINTFSMP_("%s: lock acquired\n", __func__);
	_XDPRINTFSMP_("%s: lock current value=0x%08x\n", __func__, my_lock);


	_XDPRINTFSMP_("%s: going to release lock...\n", __func__);
	spin_unlock(&my_lock);
	_XDPRINTFSMP_("%s: lock released [cirrent value=0x%08x]\n", __func__, my_lock);
*/

	_XDPRINTFSMP_("%s: proceeding to initialize SMP...\n", __func__);
	bcm2837_platform_smpinitialize();
	_XDPRINTFSMP_("%s: secondary cores should have started. moving on with boot processor...\n", __func__);


	//_XDPRINTFSMP_("%s: core: WiP. Halting\n", __func__);
	//HALT();

	//store guest OS boot register values
	guestos_boot_r0=r0;
	guestos_boot_r1=id;
	guestos_boot_r2=at;

	hvbar = sysreg_read_hvbar();
	_XDPRINTFSMP_(" HVBAR before=0x%08x\n", hvbar);
	_XDPRINTFSMP_(" g_hypvtable at=0x%08x\n", (u32)&g_hypvtable);

	sysreg_write_hvbar((u32)&g_hypvtable);

	hvbar = sysreg_read_hvbar();
	_XDPRINTFSMP_(" loaded HVBAR with g_hypvtable; HVBAR after=0x%08x\n", hvbar);

	_XDPRINTFSMP_("uxmhf-rpi3: core: proceeding to test hypercall (HVC) in HYP mode...\n");
	hypcall();
	_XDPRINTFSMP_("uxmhf-rpi3: core: successful return after hypercall test.\n");


	_XDPRINTFSMP_("%s: HCR=0x%08x\n", __func__, sysreg_read_hcr());
	_XDPRINTFSMP_("%s: HSTR=0x%08x\n", __func__, sysreg_read_hstr());
	_XDPRINTFSMP_("%s: HCPTR=0x%08x\n", __func__, sysreg_read_hcptr());
	_XDPRINTFSMP_("%s: HDCR=0x%08x\n", __func__, sysreg_read_hdcr());


	/*

	hcr = sysreg_read_hcr();
	bcm2837_miniuart_puts(" HCR before= ");
	debug_hexdumpu32(hcr);

	spsr_hyp = sysreg_read_spsr_hyp();
	bcm2837_miniuart_puts(" SPSR_hyp= ");
	debug_hexdumpu32(spsr_hyp);

	// initialize cpu support for second stage page table translations
	bcm2837_miniuart_puts("uxmhf-rpi3: core: initializing cpu support for stage-2 pts...\n");
	s2pgtbl_initialize();
	bcm2837_miniuart_puts("uxmhf-rpi3: core: cpu ready for stage-2 pts...\n");

	// populate stage-2 page tables
	bcm2837_miniuart_puts("uxmhf-rpi3: core: populating stage-2 pts...\n");
	s2pgtbl_populate_tables();
	bcm2837_miniuart_puts("uxmhf-rpi3: core: stage-2 pts populated.\n");

	// load page table base
	s2pgtbl_loadpgtblbase();

	// activate translation
	s2pgtbl_activatetranslation();
*/

	// initialize cpu support for second stage page table translations
	s2pgtbl_initialize();
	_XDPRINTFSMP_("%s: cpu ready for stage-2 pts...\n", __func__);

	// load page table base
	s2pgtbl_loadpgtblbase();
	_XDPRINTFSMP_("%s: loaded stage-2 page-table base register\n", __func__);

	// activate translation
	//s2pgtbl_activatetranslation();
	//_XDPRINTFSMP_("%s: activated stage-2 translation\n", __func__);


	_XDPRINTFSMP_("uxmhf-rpi3: core: proceeding to switch to SVC mode...\n");
	_XDPRINTF_("%s: r0=0x%08x, id=0x%08x, ATAGS=0x%08x\n", __func__, guestos_boot_r0, guestos_boot_r1, guestos_boot_r2);

	//cpumodeswitch_hyp2svc(r0, id, at, &entry_svc);
	cpumodeswitch_hyp2svc(r0, id, at, 0x8000, 0);



/*
	_XDPRINTFSMP_("uXMHF-rpi3: core: Chainloading OS kernel...\n");
	chainload_os(guestos_boot_r0, guestos_boot_r1, guestos_boot_r2);
*/

	_XDPRINTFSMP_("uxmhf-rpi3: core: We were not supposed to be here.Halting!\n");
	HALT();

}



void secondary_main(u32 cpuid){
	u32 start_address;
	u32 hvbar;

	_XDPRINTF_("%s[%u]: ENTER: sp=0x%08x (cpu_stacks=0x%08x)\n", __func__, cpuid,
			cpu_read_sp(), &cpu_stacks);

	hyppgtbl_activate();
	_XDPRINTF_("%s[%u]: hyp page-tables activated\n", __func__, cpuid);

	hvbar = sysreg_read_hvbar();
	_XDPRINTF_(" HVBAR before=0x%08x\n", hvbar);
	_XDPRINTF_(" g_hypvtable at=0x%08x\n", (u32)&g_hypvtable);

	sysreg_write_hvbar((u32)&g_hypvtable);

	hvbar = sysreg_read_hvbar();
	_XDPRINTF_(" loaded HVBAR with g_hypvtable; HVBAR after=0x%08x\n", hvbar);

	_XDPRINTF_("%s[%u]: HCR=0x%08x\n", __func__, cpuid, sysreg_read_hcr());
	_XDPRINTF_("%s[%u]: HSTR=0x%08x\n", __func__, cpuid, sysreg_read_hstr());
	_XDPRINTF_("%s[%u]: HCPTR=0x%08x\n", __func__, cpuid, sysreg_read_hcptr());
	_XDPRINTF_("%s[%u]: HDCR=0x%08x\n", __func__, cpuid, sysreg_read_hdcr());


	//_XDPRINTF_("%s[%u]: Signalling SMP readiness...\n", __func__, cpuid);
	//cpu_smpready[cpuid]=1;

	//use XDPRINTFSMP from hereon
	//start_address=bcm2837_platform_waitforstartup(cpuid);

	//if(cpuid == 1){
	//	_XDPRINTFSMP_("%s[%u]: Boooting CPU within guest at 0x%08x...\n", __func__, cpuid, start_address);
	//	cpumodeswitch_hyp2svc(0, 0, 0, start_address);
	//}



	_XDPRINTF_("%s[%u]: We should never be here. Halting!\n", __func__, cpuid);
	HALT();
}


//all secondary CPUs get here in SVC mode and enter the wait-for-startup loop
void secondary_main_svc(u32 cpuid){
	_XDPRINTF_("%s[%u]: ENTER...\n", __func__, cpuid);

	_XDPRINTF_("%s[%u]: Signalling SMP readiness...\n", __func__, cpuid);
	cpu_smpready[cpuid]=1;

	//use XDPRINTFSMP from hereon
	//start_address=bcm2837_platform_waitforstartup(cpuid);

	//if(cpuid == 1){
	//	_XDPRINTFSMP_("%s[%u]: Boooting CPU within guest at 0x%08x...\n", __func__, cpuid, start_address);
	//	cpumodeswitch_hyp2svc(0, 0, 0, start_address);
	//}

	_XDPRINTFSMP_("%s[%u]: We should never be here. Halting!\n", __func__, cpuid);
	HALT();
}
