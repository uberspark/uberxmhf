#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

#define HALT() while(1);

extern u32 mmio_read32 (u32 address);
extern void mmio_write32 (u32 address, u32 value);

extern void hypcall(void);


void main(u32 r0, u32 id, struct atag *at){
	//struct atag *pat;
	//bcm2837_miniuart_init();
	u32 cpsr;
	u32 hvbar, hcr, spsr_hyp;

	bcm2837_miniuart_puts("uXMHF-rpi3: guestos: Hello World!\n");
	bcm2837_miniuart_puts(" r0= ");
	debug_hexdumpu32(r0);
	bcm2837_miniuart_puts(" id= ");
	debug_hexdumpu32(id);
	bcm2837_miniuart_puts(" ATAGS= ");
	debug_hexdumpu32(at);

	bcm2837_miniuart_puts("uXMHF-rpi3: guestos: All done. Halting!\n");
	HALT();

}


