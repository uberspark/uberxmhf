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
// hyptimer_emptyloop
// empty loop for delay
//////
u32 hyptimer_emptyloop(void){
	u32 i;
	u32 dummy=0;
	for(i=0; i < 1024; i++)
		dummy+=i;
	return dummy;
}

//////
// hyptimer_test
// test function for hypervisor timers
//////
void hyptimer_test(u32 cpuid){
	u32 cpsr;
	u64 cntpct_val;

	_XDPRINTFSMP_("%s[%u]: ENTER\n", __func__, cpuid);

	cpsr = sysreg_read_cpsr();
	_XDPRINTFSMP_("%s[%u]: CPSR[before]=0x%08x; CPSR.A=%u, CPSR.I=%u, CPSR.F=%u\n",
			__func__, cpuid, cpsr, ((cpsr & (1UL << 8)) >> 8),
			((cpsr & (1UL << 7)) >> 7),
			((cpsr & (1UL << 6)) >> 6) );

	cpsr &= ~(1UL << 7);	//clear CPSR.I to allow IRQss
	sysreg_write_cpsr(cpsr);


	cpsr = sysreg_read_cpsr();
	_XDPRINTFSMP_("%s[%u]: CPSR[after]=0x%08x; CPSR.A=%u, CPSR.I=%u, CPSR.F=%u\n",
			__func__, cpuid, cpsr, ((cpsr & (1UL << 8)) >> 8),
			((cpsr & (1UL << 7)) >> 7),
			((cpsr & (1UL << 6)) >> 6) );


	cntpct_val = sysreg_read_cntpct();
	_XDPRINTFSMP_("%s[%u]: CNTPCT[before]=0x%016llx\n", __func__, cpuid, cntpct_val);
	hyptimer_emptyloop();
	cntpct_val = sysreg_read_cntpct();
	_XDPRINTFSMP_("%s[%u]: CNTPCT[after]=0x%016llx\n", __func__, cpuid, cntpct_val);


	_XDPRINTFSMP_("%s[%u]: CNTHP_TVAL[initial]=%d\n", __func__, cpuid, sysreg_read_cnthp_tval());
	sysreg_write_cnthp_tval(2048);
	_XDPRINTFSMP_("%s[%u]: CNTHP_TVAL[reset]=%d\n", __func__, cpuid, sysreg_read_cnthp_tval());
	//hyptimer_emptyloop();

	sysreg_write_cnthp_ctl(0x1);
	hyptimer_emptyloop();
	hyptimer_emptyloop();
	hyptimer_emptyloop();
	hyptimer_emptyloop();
	_XDPRINTFSMP_("%s[%u]: CNTHP_TVAL[current]=%d\n", __func__, cpuid, sysreg_read_cnthp_tval());
	_XDPRINTFSMP_("%s[%u]: CNTHP_CTL[current]=%d\n", __func__, cpuid, sysreg_read_cnthp_ctl());


	_XDPRINTFSMP_("%s[%u]: now moving into endless loop...\n", __func__, cpuid);
	HALT();

	_XDPRINTFSMP_("%s[%u]: EXIT\n", __func__, cpuid);
}
