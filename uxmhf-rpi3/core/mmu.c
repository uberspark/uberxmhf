/*
	ARM 8 MMU functions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

void mmu_invalidatetlbs(void){
	//invalidate all TLB
	sysreg_tlbiallh();
}

void mmu_invalidateicache(void){
	//invalidate instruction caches
	sysreg_iciallu();
}

//enable instruction caching
void mmu_enableicache(void){
	u32 hsctlr;

	hsctlr = sysreg_read_hsctlr();
	hsctlr |= (1 << 12);	//enable instruction caching
	sysreg_write_hsctlr(hsctlr);
}

//enable data caching
void mmu_enabledcache(void){
	u32 hsctlr;

	hsctlr = sysreg_read_hsctlr();
	hsctlr |= (1 << 2);		//enable data caching
	sysreg_write_hsctlr(hsctlr);
}

//disable instruction caching
void mmu_disableicache(void){
	u32 hsctlr;

	hsctlr = sysreg_read_hsctlr();
	hsctlr &= ~(1 << 12);	//disable instruction caching
	sysreg_write_hsctlr(hsctlr);
}

//disable data caching
void mmu_disabledcache(void){
	u32 hsctlr;

	hsctlr = sysreg_read_hsctlr();
	hsctlr &= ~(1 << 2);		//disable data caching
	sysreg_write_hsctlr(hsctlr);
}


//activate MMU translation
void mmu_activatetranslation(void){
	u32 hsctlr;

	hsctlr = sysreg_read_hsctlr();
	_XDPRINTF_("%s: HSCTLR before=0x%08x\n", __func__, hsctlr);

	hsctlr |= HSCTLR_M_MASK;
	hsctlr |= (1 << 2);		//enable data caching
	hsctlr |= (1 << 12);	//enable instruction caching

	sysreg_write_hsctlr(hsctlr);

	hsctlr = sysreg_read_hsctlr();
	_XDPRINTF_("%s: HSCTLR after=0x%08x\n", __func__, hsctlr);
}

