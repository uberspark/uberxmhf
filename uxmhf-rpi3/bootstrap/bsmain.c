#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <atags.h>
#include <debug.h>

extern void call_core(u32 r0, u32 id, struct atag *at);
extern u32 g_oskrnl_startaddr;
extern u32 g_oskrnl_size;
extern u32 g_core_startaddr;
extern u32 g_core_size;

extern u32 g_guestos_startaddr;
extern u32 g_guestos_size;

void memcpy(void *dest, void *src, unsigned int n){
	u32 i;
	u8 *bsrc = (u8 *)src;
	u8 *bdest = (u8 *)dest;

   for (i=0; i<n; i++)
       bdest[i] = bsrc[i];
}

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
	bcm2837_miniuart_puts(" g_guestos_startaddr= ");
	debug_hexdumpu32(g_guestos_startaddr);
	bcm2837_miniuart_puts(" g_guestos_size= ");
	debug_hexdumpu32(g_guestos_size);

	bcm2837_miniuart_puts(" r0= ");
	debug_hexdumpu32(r0);
	bcm2837_miniuart_puts(" id= ");
	debug_hexdumpu32(id);
	bcm2837_miniuart_puts(" ATAGS= ");
	debug_hexdumpu32(at);


	bcm2837_miniuart_puts("uXMHF-rpi3: bootstrap: relocating core...\n");
	memcpy(0x30000000, g_core_startaddr, g_core_size);
	bcm2837_miniuart_puts("uXMHF-rpi3: bootstrap: core relocated\n");


	bcm2837_miniuart_puts("uXMHF-rpi3: bootstrap: relocating guestos...\n");
	memcpy(0x30002000, g_guestos_startaddr, g_guestos_size);
	bcm2837_miniuart_puts("uXMHF-rpi3: bootstrap: guestos relocated\n");

	/*if(at->size == 0xedfe0dd0)
		bcm2837_miniuart_puts("uXMHF-rpi3: ATAGS pointer is a FDT blob so no worries\n");
	else{
		bcm2837_miniuart_puts("uXMHF-rpi3: Error: require ATAGS to be FDT blob. Halting!\n");
	}*/

	bcm2837_miniuart_puts("uXMHF-rpi3: bootstrap: passing control to core...\n");

	bcm2837_miniuart_flush();
	call_core(r0, id, at);
}
