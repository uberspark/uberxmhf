/*
	guest context switch tracer

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>
#include <ctxtrace.h>

//initialize guest context tracing
void ctxtrace_init(u32 cpuid){
	u32 hstr;

	hstr = sysreg_read_hstr();
	_XDPRINTFSMP_("%s[%u]: HSTR before=0x%08x\n", __func__, cpuid, hstr);

	hstr = hstr | (1UL << 2);	//activate trap on CP15, c2

	_XDPRINTFSMP_("%s[%u]: HSTR after=0x%08x\n", __func__, cpuid, hstr);
	sysreg_write_hstr(hstr);

	_XDPRINTFSMP_("%s[%u]: initialized guest context tracing\n", __func__, cpuid);
}
