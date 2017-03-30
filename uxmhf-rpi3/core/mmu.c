/*
	ARM 8 MMU functions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

void mmu_disableallcaches(void){
	u32 hsctlr;

	//invalidate all TLB
	sysreg_tlbiallh();

	//invalidate instruction caches
	sysreg_iciallu();

	//disable instruction and data caching
	hsctlr = sysreg_read_hsctlr();
	hsctlr &= ~(1 << 12);	//disable instruction caching
	hsctlr &= ~(1 << 2);	//disable data caching
	sysreg_write_hsctlr(hsctlr);

}
