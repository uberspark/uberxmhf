#include <bcm2837.h>
#include <miniuart.h>
#include <atags.h>
#include <debug.h>

extern u32 mmio_read32 (u32 address);
extern void mmio_write32 (u32 address, u32 value);
extern void call_core(u32 r0, u32 id, struct atag *at);
extern u32 g_oskrnl_startaddr;
extern u32 g_oskrnl_size;
extern u32 g_core_startaddr;
extern u32 g_core_size;

void bsmain(u32 r0, u32 id, struct atag *at){
	bcm2837_miniuart_init();

	bcm2837_miniuart_puts("uXMHF-rpi3: bootstrap: Hello World!\n");

	bcm2837_miniuart_puts(" g_oskrnl_startaddr= ");
	debug_hexdumpu32(g_oskrnl_startaddr);
	bcm2837_miniuart_puts(" g_oskrnl_size= ");
	debug_hexdumpu32(g_oskrnl_size);
	bcm2837_miniuart_puts(" g_core_startaddr= ");
	debug_hexdumpu32(g_core_startaddr);
	bcm2837_miniuart_puts(" g_core_size= ");
	debug_hexdumpu32(g_core_size);

	bcm2837_miniuart_puts(" r0= ");
	debug_hexdumpu32(r0);
	bcm2837_miniuart_puts(" id= ");
	debug_hexdumpu32(id);
	bcm2837_miniuart_puts(" ATAGS= ");
	debug_hexdumpu32(at);

	/*if(at->size == 0xedfe0dd0)
		bcm2837_miniuart_puts("uXMHF-rpi3: ATAGS pointer is a FDT blob so no worries\n");
	else{
		bcm2837_miniuart_puts("uXMHF-rpi3: Error: require ATAGS to be FDT blob. Halting!\n");
	}*/

	bcm2837_miniuart_puts("uXMHF-rpi3: bootstrap: passing control to core...\n");

	bcm2837_miniuart_flush();
	call_core(r0, id, at);
}
