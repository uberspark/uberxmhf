#include <bcm2837.h>
#include <miniuart.h>
#include <atags.h>
#include <debug.h>

extern u32 mmio_read32 (u32 address);
extern void mmio_write32 (u32 address, u32 value);
extern void chainload_os(u32 r0, u32 id, struct atag *at);

extern u32 sysreg_read_scr(void);

void main(u32 r0, u32 id, struct atag *at){
	//struct atag *pat;
	//bcm2837_miniuart_init();
	u32 scr;

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


	scr = sysreg_read_scr();
	if(scr & 0x1)
		bcm2837_miniuart_puts("uXMHF-rpi3: core: SCR.NS=1; we are in NON-SECURE state\n");
	else
		bcm2837_miniuart_puts("uXMHF-rpi3: core: SCR.NS=0; we are in SECURE state\n");

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
