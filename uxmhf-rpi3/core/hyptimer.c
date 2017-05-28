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
	_XDPRINTFSMP_("%s[%u]: ENTER\n", __func__, cpuid);

	_XDPRINTFSMP_("%s[%u]: EXIT\n", __func__, cpuid);
}
