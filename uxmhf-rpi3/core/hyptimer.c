/*
	ARM 8 hypervisor timer module

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>



//////
// hyptimer_test
// test function for hypervisor timers
//////
void hyptimer_test(u32 cpuid){
	u32 cpsr;

	_XDPRINTFSMP_("%s[%u]: ENTER\n", __func__, cpuid);

	cpsr = sysreg_read_cpsr();
	_XDPRINTFSMP_("%s[%u]: CPSR=0x%08x; CPSR.A=%u, CPSR.I=%u, CPSR.F=%u\n",
			__func__, cpuid, cpsr, ((cpsr & (1UL << 8)) >> 8),
			((cpsr & (1UL << 7)) >> 7),
			((cpsr & (1UL << 6)) >> 6) );

	cpsr &= ~(1UL << 7);	//clear CPSR.I to allow IRQss
	sysreg_write_cpsr(cpsr);

	_XDPRINTFSMP_("%s[%u]: now moving into endless loop...\n", __func__, cpuid);
	HALT();

	_XDPRINTFSMP_("%s[%u]: EXIT\n", __func__, cpuid);
}
