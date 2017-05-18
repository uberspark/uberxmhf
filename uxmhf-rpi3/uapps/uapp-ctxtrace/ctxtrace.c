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



void ctxtrace_ttbr0_access_handler(arm8_32_regs_t *r, u32 rw, u32 rt){
	_XDPRINTFSMP_("%s: rw=%u, rt=%u\n", __func__, rw, rt);
	HALT();
}

void ctxtrace_ttbr1_access_handler(arm8_32_regs_t *r, u32 rw, u32 rt){
	_XDPRINTFSMP_("%s: rw=%u, rt=%u\n", __func__, rw, rt);
	HALT();
}

void ctxtrace_ttbcr_access_handler(arm8_32_regs_t *r, u32 rw, u32 rt){
	_XDPRINTFSMP_("%s: rw=%u, rt=%u\n", __func__, rw, rt);
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
	rt 		= (	trap_iss & 0x000001c0UL	) >> 5;
	crn 	= (	trap_iss & 0x00003c00UL	) >> 10;
	opc1 	= (	trap_iss & 0x0001c000UL	) >> 14;
	opc2 	= (	trap_iss & 0x000e0000UL	) >> 17;
	cond 	= (	trap_iss & 0x00f00000UL	) >> 20;
	cv 		= (	trap_iss & 0x01000000UL	) >> 24;

	_XDPRINTFSMP_("%s: cv=%u, cond=%x, opc2=%u, opc1=%u, crn=%u, rt=%u, crm=%u, rw=%u\n",
			__func__, cv, cond, opc2, opc1, crn, rt, crm, rw);

	//if cv is zero bail-out
	if(cv == 0){
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
		_XDPRINTFSMP_("%s: invalid case; unsupported. Halting!\n", __func__);
		HALT();
	}

}
