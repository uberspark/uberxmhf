/*
	ARM 8 stage-2 page table translation functions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

/* setup CPU to support stage-2 table translation */
void s2pgtbl_initialize(void){
	u32 vtcr;

	vtcr = sysreg_read_vtcr();
	bcm2837_miniuart_puts("VTCR= ");
	debug_hexdumpu32(vtcr);

}
