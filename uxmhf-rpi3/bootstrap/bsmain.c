#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <atags.h>
#include <debug.h>

extern void call_core(u32 r0, u32 id, struct atag *at);

void bsmain(u32 r0, u32 id, struct atag *at){
	u32 hsctlr, cpsr;

	bcm2837_miniuart_init();

	bcm2837_miniuart_puts("uXMHF-rpi3: bootstrap: Hello World!\n");

	cpsr = sysreg_read_cpsr();
	bcm2837_miniuart_puts(" CPSR[mode]= ");
	debug_hexdumpu32((cpsr & 0xF));

	if(! ((cpsr & 0xF) == 0xA) ){
		bcm2837_miniuart_puts("uXMHF-rpi3: core: not in HYP mode. Halting!\n");
		HALT();
	}


	hsctlr = sysreg_read_hsctlr();
	bcm2837_miniuart_puts(" HSCTLR before= ");
	debug_hexdumpu32(hsctlr);

	hsctlr |= (1 << 12);	//enable instruction caching
	hsctlr |= (1 << 2);		//enable data caching

	sysreg_write_hsctlr(hsctlr);

	hsctlr = sysreg_read_hsctlr();
	bcm2837_miniuart_puts(" HSCTLR after= ");
	debug_hexdumpu32(hsctlr);

	bcm2837_miniuart_puts(" r0= ");
	debug_hexdumpu32(r0);
	bcm2837_miniuart_puts(" id= ");
	debug_hexdumpu32(id);
	bcm2837_miniuart_puts(" ATAGS= ");
	debug_hexdumpu32(at);
	bcm2837_miniuart_puts("uXMHF-rpi3: bootstrap: passing control to core...\n");

	bcm2837_miniuart_flush();
	call_core(r0, id, at);
}
