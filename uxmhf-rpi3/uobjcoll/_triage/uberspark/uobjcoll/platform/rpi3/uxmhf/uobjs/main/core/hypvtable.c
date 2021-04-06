/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

/*
	ARM 8 hypervisor vector table interface
	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/debug.h>
//#include <uberspark/include/uberspark.h>


//////
// externs
//////
extern u32 g_hypvtable[BCM2837_MAXCPUS][8];


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
	_XDPRINTFSMP_("%s[%u]: dumping (ghypvtable at 0x%08x) contents...\n", __func__, cpuid, (u32)&g_hypvtable[cpuid]);
	for(i=0; i < 8; i++){
		_XDPRINTFSMP_("%s[%u]:   0x%08x\n", __func__, cpuid, g_hypvtable[cpuid][i]);
	}
	_XDPRINTFSMP_("%s[%u]: dumped ghypvtable\n", __func__, cpuid);

	//setup HVBAR for vectors
	_XDPRINTFSMP_("%s[%u]: HVBAR[before]=0x%08x\n", __func__, cpuid, CASM_FUNCCALL(sysreg_read_hvbar, CASM_NOPARAM));
	sysreg_write_hvbar((u32)&g_hypvtable[cpuid]);
	_XDPRINTFSMP_("%s[%u]: HVBAR[after]=0x%08x\n", __func__, cpuid, CASM_FUNCCALL(sysreg_read_hvbar, CASM_NOPARAM));
}
