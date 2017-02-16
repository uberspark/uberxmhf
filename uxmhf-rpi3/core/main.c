#include <bcm2837.h>
#include <miniuart.h>
#include <atags.h>
#include <debug.h>

#define HALT() while(1);

extern u32 mmio_read32 (u32 address);
extern void mmio_write32 (u32 address, u32 value);
extern void chainload_os(u32 r0, u32 id, struct atag *at);

extern u32 sysreg_read_scr(void);
extern u32 sysreg_read_cpsr(void);
extern u32 sysreg_read_hvbar(void);
extern void sysreg_write_hvbar(u32 value);

extern u32 g_hypvtable[];

void main(u32 r0, u32 id, struct atag *at){
	//struct atag *pat;
	//bcm2837_miniuart_init();
	u32 cpsr;
	u32 hvbar;

	bcm2837_miniuart_puts("uXMHF-rpi3: core: Hello World!\n");
	bcm2837_miniuart_puts(" r0= ");
	debug_hexdumpu32(r0);
	bcm2837_miniuart_puts(" id= ");
	debug_hexdumpu32(id);
	bcm2837_miniuart_puts(" ATAGS= ");
	debug_hexdumpu32(at);

	if(at->size == 0xedfe0dd0)
		bcm2837_miniuart_puts("uXMHF-rpi3: core: ATAGS pointer is a FDT blob so no worries\n");
	else{
		bcm2837_miniuart_puts("uXMHF-rpi3: core: Error: require ATAGS to be FDT blob. Halting!\n");
	}


	cpsr = sysreg_read_cpsr();
	bcm2837_miniuart_puts(" CPSR[mode]= ");
	debug_hexdumpu32((cpsr & 0xF));

	if(! ((cpsr & 0xF) == 0xA) ){
		bcm2837_miniuart_puts("uXMHF-rpi3: core: not in HYP mode. Halting!\n");
		HALT();
	}

	bcm2837_miniuart_puts(" g_hypvtable at= ");
	debug_hexdumpu32((u32)&g_hypvtable);

	hvbar = sysreg_read_hvbar();
	bcm2837_miniuart_puts(" HVBAR= ");
	debug_hexdumpu32(hvbar);


	/*
	while(at->tag){
		switch(at->tag){
			case ATAG_CORE:
				bcm2837_miniuart_puts("  Found ATAG_CORE\n");
				break;

			case ATAG_MEM:
				bcm2837_miniuart_puts("  Found ATAG_MEM\n");
				break;

			case ATAG_INITRD2:
				bcm2837_miniuart_puts("  Found ATAG_INITRD2\n");
				break;

			case ATAG_CMDLINE:
				bcm2837_miniuart_puts("  Found ATAG_CMDLINE\n");
				break;

			default:
				bcm2837_miniuart_puts("  Unknown ATAG: ");
				debug_hexdumpu32(at->tag);
				break;
		}

		at=atag_next(at);
	}*/


	bcm2837_miniuart_puts("uXMHF-rpi3: core: Chainloading OS kernel...\n");

	bcm2837_miniuart_flush();
	chainload_os(r0, id, at);
}
