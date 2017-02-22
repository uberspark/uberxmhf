#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

#define HALT() while(1);

extern u32 mmio_read32 (u32 address);
extern void mmio_write32 (u32 address, u32 value);
extern u32 sysreg_read_cpsr(void);

extern u32 sysreg_read_vbar(void);
extern void sysreg_write_vbar(u32 value);

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

	cpsr = sysreg_read_cpsr();
	bcm2837_miniuart_puts(" CPSR[mode]= ");
	debug_hexdumpu32((cpsr & 0xF));

	bcm2837_miniuart_puts("uxmhf-rpi3: guestos: proceeding to test hypercall (HVC) in SVC mode...\n");
	hypcall();
	bcm2837_miniuart_puts("uxmhf-rpi3: guestos: successful return after hypercall test.\n");


	bcm2837_miniuart_puts("uXMHF-rpi3: guestos: All done. Halting!\n");
	HALT();

}


