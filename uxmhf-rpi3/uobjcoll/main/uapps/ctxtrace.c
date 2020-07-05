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
	guest context switch tracer
	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/debug.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/ctxtrace.h>
//#include <uberspark/include/uberspark.h>

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



void ctxtrace_ttbr0_access_handler(arm8_32_regs_t *r, u32 rw, u32 rt){
	//_XDPRINTFSMP_("%s: rw=%u, rt=%u\n", __func__, rw, rt);
	if(rw == 1){
		//read from system register and write to guest general purpose register
		guest_regwrite(r, rt, sysreg_read_ttbr0());
	}else{
		//write to system register by reading from guest general purpose register
		sysreg_write_ttbr0(guest_regread(r, rt));
	}
}

void ctxtrace_ttbr1_access_handler(arm8_32_regs_t *r, u32 rw, u32 rt){
	//_XDPRINTFSMP_("%s: rw=%u, rt=%u\n", __func__, rw, rt);
	if(rw == 1){
		//read from system register and write to guest general purpose register
		guest_regwrite(r, rt, sysreg_read_ttbr1());
	}else{
		//write to system register by reading from guest general purpose register
		sysreg_write_ttbr1(guest_regread(r, rt));
	}
}

void ctxtrace_ttbcr_access_handler(arm8_32_regs_t *r, u32 rw, u32 rt){
	//_XDPRINTFSMP_("%s: rw=%u, rt=%u\n", __func__, rw, rt);
	if(rw == 1){
		//read from system register and write to guest general purpose register
		guest_regwrite(r, rt, sysreg_read_ttbcr());
	}else{
		//write to system register by reading from guest general purpose register
		sysreg_write_ttbcr(guest_regread(r, rt));
	}
}



//cp15 trap handler
void ctxtrace_cp15_trap_handler(arm8_32_regs_t *r, u32 hsr){
	u32 trap_iss;
	u32 rw;
	u32 crm;
	u32 rt;
	u32 crn;
	u32 opc1;
	u32 opc2;
	u32 cond;
	u32 cv;

	//get trap iss
	trap_iss = (hsr & HSR_ISS_MASK) >> HSR_ISS_SHIFT;

	//populate trap variables for easy trace/emulation
	rw 		= (	trap_iss & 0x00000001UL );
	crm 	= (	trap_iss & 0x0000001eUL	) >> 1;
	rt 		= (	trap_iss & 0x000001e0UL	) >> 5;
	crn 	= (	trap_iss & 0x00003c00UL	) >> 10;
	opc1 	= (	trap_iss & 0x0001c000UL	) >> 14;
	opc2 	= (	trap_iss & 0x000e0000UL	) >> 17;
	cond 	= (	trap_iss & 0x00f00000UL	) >> 20;
	cv 		= (	trap_iss & 0x01000000UL	) >> 24;


	//if cv is zero bail-out
	if(cv == 0){
		_XDPRINTFSMP_("%s: cv=%u, cond=%x, opc2=%u, opc1=%u, crn=%u, rt=%u, crm=%u, rw=%u\n",
				__func__, cv, cond, opc2, opc1, crn, rt, crm, rw);
		_XDPRINTFSMP_("%s: unhandled case with cv=0. Halting!\n", __func__);
		HALT();
	}

	//we currently ignore cond

	//cases we support
	if( crn == 0x2 && opc1 == 0 && crm == 0 && opc2 == 0){
		//ttbr0 access
		ctxtrace_ttbr0_access_handler(r, rw, rt);

	}else if (crn == 0x2 && opc1 == 0 && crm == 0 && opc2 == 1){
		//ttbr1 access
		ctxtrace_ttbr1_access_handler(r, rw, rt);

	}else if (crn == 0x2 && opc1 == 0 && crm == 0 && opc2 == 2){
		//ttbcr access
		ctxtrace_ttbcr_access_handler(r, rw, rt);

	}else{
		_XDPRINTFSMP_("%s: cv=%u, cond=%x, opc2=%u, opc1=%u, crn=%u, rt=%u, crm=%u, rw=%u\n",
				__func__, cv, cond, opc2, opc1, crn, rt, crm, rw);
		_XDPRINTFSMP_("%s: invalid case; unsupported. Halting!\n", __func__);
		HALT();
	}

}
