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
extern void hypvtable_fiq_handler0(void);
extern void hypvtable_reserved_handler0(void);


//////
// hypvtable_setentry
// initialize an entry in the vector table for given CPU
// return 0 on success; non-zero on fail
//////
u32 hypvtable_setentry(u32 cpuid, u32 entry_idx, u32 entry_addr){
	u32 vector_table_entry_base;
	u32 entry_value;

	if(entry_idx > 7)
		return 1;

	vector_table_entry_base =(u32)&g_hypvtable[cpuid];
	vector_table_entry_base += sizeof(u32) * entry_idx;

	if(entry_addr < vector_table_entry_base)
		return 2;

	//formula to setup vector table value based on given 32-bit address
	//1. addr - vtable_base + 0x4
	//2. divide 1 by 4
	//3. subtract 1
	//4. add to unsigned 0xEA000000
	entry_value = 0xEA000000 + (u32)(((entry_addr - vector_table_entry_base + 0x4) / 4) - 1);

	g_hypvtable[cpuid][entry_idx]=entry_value;
}


//////
// hypvtable_initialize
// initialize vector table for given CPU
//////
void hypvtable_initialize(u32 cpuid){
	u32 i;

	//debug
	_XDPRINTFSMP_("%s[%u]: hypvtable_fiq_handler0 at 0x%08x\n", __func__, cpuid, (u32)&hypvtable_fiq_handler0);
	_XDPRINTFSMP_("%s[%u]: hypvtable_reserved_handler0 at 0x%08x\n", __func__, cpuid, (u32)&hypvtable_reserved_handler0);
	_XDPRINTFSMP_("%s[%u]: dumping (ghypvtable at 0x%08x) contents...\n", __func__, cpuid, (u32)&g_hypvtable[cpuid]);
	for(i=0; i < 8; i++){
		_XDPRINTFSMP_("%s[%u]:   0x%08x\n", __func__, cpuid, g_hypvtable[cpuid][i]);
	}
	_XDPRINTFSMP_("%s[%u]: dumped ghypvtable\n", __func__, cpuid);

#if 0
	//test
	hypvtable_setentry(cpuid, 7, (u32)&hypvtable_fiq_handler0);
	_XDPRINTFSMP_("%s[%u]: dumping (ghypvtable at 0x%08x) contents...\n", __func__, cpuid, (u32)&g_hypvtable[cpuid]);
	for(i=0; i < 8; i++){
		_XDPRINTFSMP_("%s[%u]:   0x%08x\n", __func__, cpuid, g_hypvtable[cpuid][i]);
	}
	_XDPRINTFSMP_("%s[%u]: dumped ghypvtable\n", __func__, cpuid);
#endif


	//setup HVBAR for vectors
	_XDPRINTFSMP_("%s[%u]: HVBAR[before]=0x%08x\n", __func__, cpuid, sysreg_read_hvbar());
	sysreg_write_hvbar((u32)&g_hypvtable[cpuid]);
	_XDPRINTFSMP_("%s[%u]: HVBAR[after]=0x%08x\n", __func__, cpuid, sysreg_read_hvbar());
}
