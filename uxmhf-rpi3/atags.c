/*
	ATAGS (ARM bootloader tags) implementation

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <bcm2837.h>
#include <atags.h>

void atag_dumptags(struct atag *at){
	bcm2837_miniuart_puts("uXMHF-rpi3: Dumping ATAG list...\n");
	bcm2837_miniuart_flush();

}
