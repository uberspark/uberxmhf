#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <atags.h>
#include <fdt.h>
#include <debug.h>


extern void chainload_os(u32 r0, u32 id, struct atag *at);
extern void cpumodeswitch_hyp2svc(u32 address);
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
}

void hypsvc_handler(void){
	u32 hsr;
	u32 elr_hyp;
	//bcm2837_miniuart_puts("uXMHF-rpi3: core: hypSVC_handler [IN]\n");
	//bcm2837_miniuart_puts("uXMHF-rpi3: core: hypSVC_handler [OUT]\n");

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

}


void main_svc(void){
	u32 cpsr;

	bcm2837_miniuart_puts("uXMHF-rpi3: core: now in SVC mode\n");

	cpsr = sysreg_read_cpsr();
	bcm2837_miniuart_puts(" CPSR[mode]= ");
	debug_hexdumpu32((cpsr & 0xF));

	bcm2837_miniuart_puts("uxmhf-rpi3: core: proceeding to test hypercall (HVC) in SVC mode...\n");
	hypcall();
	bcm2837_miniuart_puts("uxmhf-rpi3: core: successful return after hypercall test.\n");

	bcm2837_miniuart_puts("uXMHF-rpi3: core: Chainloading OS kernel...\n");

	bcm2837_miniuart_flush();
	chainload_os(guestos_boot_r0, guestos_boot_r1, guestos_boot_r2);

	bcm2837_miniuart_puts("uxmhf-rpi3: core: Halting!\n");
	HALT();

}


void core_fixresmemmap(u32 fdt_address){
	struct fdt_header *fdth = (struct fdt_header *)fdt_address;
	struct fdt_reserve_entry *fdtrsvmmapentryp;
	u32 newtotalsize, padding;
	u64 addr_be;

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




void main(u32 r0, u32 id, struct atag *at){
	//struct atag *pat;
	//bcm2837_miniuart_init();
	//u32 cpsr;
	u32 hvbar, hcr, spsr_hyp;
	//u32 hsctlr;

	bcm2837_miniuart_puts("uXMHF-rpi3: core: Hello World!\n");
	bcm2837_miniuart_puts(" r0= ");
	debug_hexdumpu32(r0);
	bcm2837_miniuart_puts(" id= ");
	debug_hexdumpu32(id);
	bcm2837_miniuart_puts(" ATAGS= ");
	debug_hexdumpu32(at);

	if(!(at->size == FDT_MAGIC)){
		bcm2837_miniuart_puts("uXMHF-rpi3: core: Error: require ATAGS to be FDT blob. Halting!\n");
		HALT();
	}

	bcm2837_miniuart_puts("uXMHF-rpi3: core: ATAGS pointer is a FDT blob so no worries\n");

	//fix reserved memory map
	core_fixresmemmap((u32)at);

	bcm2837_miniuart_puts("uXMHF-rpi3: core: WiP. Halting\n");
	HALT();


	//store guest OS boot register values
	guestos_boot_r0=r0;
	guestos_boot_r1=id;
	guestos_boot_r2=at;

	hvbar = sysreg_read_hvbar();
	bcm2837_miniuart_puts(" HVBAR before= ");
	debug_hexdumpu32(hvbar);

	bcm2837_miniuart_puts(" g_hypvtable at= ");
	debug_hexdumpu32((u32)&g_hypvtable);
	sysreg_write_hvbar((u32)&g_hypvtable);

	hvbar = sysreg_read_hvbar();
	bcm2837_miniuart_puts(" loaded HVBAR with g_hypvtable; HVBAR after= ");
	debug_hexdumpu32(hvbar);

	bcm2837_miniuart_puts("uxmhf-rpi3: core: proceeding to test hypercall (HVC) in HYP mode...\n");
	hypcall();
	bcm2837_miniuart_puts("uxmhf-rpi3: core: successful return after hypercall test.\n");

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

	bcm2837_miniuart_puts("uxmhf-rpi3: core: proceeding to switch to SVC mode...\n");
	cpumodeswitch_hyp2svc(&entry_svc);
*/




	bcm2837_miniuart_puts("uXMHF-rpi3: core: Chainloading OS kernel...\n");

	bcm2837_miniuart_flush();
	chainload_os(guestos_boot_r0, guestos_boot_r1, guestos_boot_r2);


	bcm2837_miniuart_puts("uxmhf-rpi3: core: We were not supposed to be here.Halting!\n");
	HALT();

}


