#include <bcm2837.h>
#include <miniuart.h>


extern u32 mmio_read32 (u32 address);
extern void mmio_write32 (u32 address, u32 value);
extern void chainload_os(u32 r0, u32 id, const u8 *atag);


void main(u32 r0, u32 id, struct atag *at){
	bcm2837_miniuart_init();

	bcm2837_miniuart_puts("uXMHF-rpi3: Hello World!\n");
	bcm2837_miniuart_flush();

	atag_dumptags(at);

	bcm2837_miniuart_puts("uXMHF-rpi3: Chainloading OS kernel...\n");
	bcm2837_miniuart_flush();
	chainload_os(r0, id, at);
}
