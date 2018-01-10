/*
	ARM 8 hypervisor vector table interface

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>


//////
// externs
//////
extern u32 g_hypvtable[BCM2837_MAXCPUS][8];


//////
// hypvtable_initialize
// initialize vector table for given CPU
//////
void hypvtable_initialize(u32 cpuid){

	//setup HVBAR for vectors
	_XDPRINTFSMP_("%s[%u]: HVBAR[before]=0x%08x\n", __func__, cpuid, sysreg_read_hvbar());

	_XDPRINTFSMP_("%s[%u]: ghypvtable at 0x%08x\n", __func__, cpuid, (u32)&g_hypvtable[cpuid]);
	sysreg_write_hvbar((u32)&g_hypvtable[cpuid]);

	_XDPRINTFSMP_("%s[%u]: HVBAR[after]=0x%08x\n", __func__, cpuid, sysreg_read_hvbar());
}
