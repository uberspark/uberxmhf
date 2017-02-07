#include <bcm2837.h>
#include <miniuart.h>
#include <atags.h>
#include <debug.h>

extern u32 mmio_read32 (u32 address);
extern void mmio_write32 (u32 address, u32 value);
extern void chainload_os(u32 r0, u32 id, struct atag *at);


void main(u32 r0, u32 id, struct atag *at){
	struct atag *pat;
	bcm2837_miniuart_init();

	bcm2837_miniuart_puts("uXMHF-rpi3: Hello World!\n");

	//atag_dumptags(at);
	if((u32)at == 0x100)
		bcm2837_miniuart_puts("uXMHF-rpi3: ATAGS at preferred location (0x100)\n");
	else{
		bcm2837_miniuart_puts("uXMHF-rpi3: ATAGS at non-standard location: ");
		debug_hexdumpu32((u32)at);
	}

	pat = (struct atag *)0x100;
	while(pat->tag){
		switch(pat->tag){
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
				bcm2837_miniuart_puts("  Unknown ATAG\n");
				break;
		}

		pat=atag_next(pat);
	}


	bcm2837_miniuart_puts("uXMHF-rpi3: Chainloading OS kernel...\n");

	bcm2837_miniuart_flush();
	chainload_os(r0, id, at);
}
