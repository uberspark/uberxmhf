/*
	ATAGS (ARM bootloader tags) implementation

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <bcm2837.h>
#include <atags.h>

void atag_dumptags(struct atag *at){
	bcm2837_miniuart_puts("uXMHF-rpi3: Dumping ATAG list...\n");

	while(at->hdr.tag != ATAG_NONE){
		switch(at->hdr.tag){
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

		at=atag_next(at);
	}

	bcm2837_miniuart_puts("uXMHF-rpi3: Dumped ATAG list.\n");

}
