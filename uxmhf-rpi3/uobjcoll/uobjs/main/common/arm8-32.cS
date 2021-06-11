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
	ARM 8 32-bit low-level cpu state access functions

	author: amit vasudevan (amitvasudevan@acm.org), ethan joseph (ethanj217@gmail.com)
*/

#include <uberspark/include/uberspark.h>
#include <uberspark/hwm/cpu/armv8/32-bit/cortex-a53/include/hwm.h>

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>

CASM_FUNCDEF(void, mmio_write32,
			 {
				 __casm__dsb_st();
				 __casm__str_r1_r0(0);
				 __casm__bx_lr();
			 },
			 u32 address, u32 value)

CASM_FUNCDEF(u32, mmio_read32,
			 {
				 __casm__ldr_imm_r0_r0(0);
				 __casm__dsb();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 u32 address)

CASM_FUNCDEF(u32, sysreg_read_spsr_hyp,
			 {
				 __casm__mrs_r0_spsrhyp();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(u32, sysreg_read_scr,
			 {
				 __casm__mrc_p15_0_r0_c1_c1_0();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(u32, sysreg_read_cpsr,
			 {
				 __casm__mrs_r0_cpsr();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_cpsr,
			 {
				 __casm__msr_cpsr_r0();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_hvbar,
			 {
				 __casm__mrc_p15_4_r0_c12_c0_0();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_hvbar,
			 {
				 __casm__mcr_p15_4_r0_c12_c0_0();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_hcr,
			 {
				 __casm__mrc_p15_4_r0_c1_c1_0();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_hcr,
			 {
				 __casm__mcr_p15_4_r0_c1_c1_0();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_hsctlr,
			 {
				 __casm__mrc_p15_4_r0_c1_c0_0();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_hsctlr,
			 {
				 __casm__isb();
				 __casm__mcr_p15_4_r0_c1_c0_0();
				 __casm__isb();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_actlr,
			 {
				 __casm__mrc_p15_0_r0_c1_c0_1();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_actlr,
			 {
				 __casm__mcr_p15_0_r0_c1_c0_1();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_idisar4,
			 {
				 __casm__mrc_p15_0_r0_c0_c2_4();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, cpu_isb,
			 {
				 __casm__isb();
				 __casm__bx_lr();
			 },
			 void *noparam)

CASM_FUNCDEF(void, cpu_dsb,
			 {
				 __casm__dsb();
				 __casm__bx_lr();
			 },
			 void *noparam)

CASM_FUNCDEF(void, cpu_dmbish,
			 {
				 __casm__dmb_ish();
				 __casm__bx_lr();
			 },
			 void *noparam)

CASM_FUNCDEF(u32, cpu_read_sp,
			 {
				 __casm__mov_r0_sp();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, hypcall,
			 {
				 __casm__hvc();
				 __casm__bx_lr();
			 },
			 void *noparam)

CASM_FUNCDEF(void, svccall,
			 {
				 __casm__svc();
				 __casm__bx_lr();
			 },
			 void *noparam)

CASM_FUNCDEF(u32, sysreg_read_sctlr,
			 {
				 __casm__mrc_p15_0_r0_c1_c0_0();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_sctlr,
			 {
				 __casm__mcr_p15_0_r0_c1_c0_0();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_vbar,
			 {
				 __casm__mrc_p15_0_r0_c12_c0_0();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_vbar,
			 {
				 __casm__mcr_p15_0_r0_c12_c0_0();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_vtcr,
			 {
				 __casm__mrc_p15_4_r0_c2_c1_2();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_vtcr,
			 {
				 __casm__mcr_p15_4_r0_c2_c1_2();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_hdcr,
			 {
				 __casm__mrc_p15_4_r0_c1_c1_1();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_hdcr,
			 {
				 __casm__mcr_p15_4_r0_c1_c1_1();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_hcptr,
			 {
				 __casm__mrc_p15_4_r0_c1_c1_2();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_hcptr,
			 {
				 __casm__mcr_p15_4_r0_c1_c1_2();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_hstr,
			 {
				 __casm__mrc_p15_4_r0_c1_c1_3();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_hstr,
			 {
				 __casm__mcr_p15_4_r0_c1_c1_3();
				 __casm__bx_lr();
			 },
			 u32 value)
//returns a 64-bit value:
//r0=lower 32-bits; r1=upper 32-bits (c.f. AAPCS)
CASM_FUNCDEF(u64, sysreg_read_vttbr,
			 {
				 __casm__mrrc_p15_6_r0_r1_c2();
				 __casm__bx_lr();
				 __casm__retu64();
			 },
			 void *noparam)
//inputs: 64-bit value
//r0=lower 32-bits; r1=upper 32-bits (c.f. AAPCS)
CASM_FUNCDEF(void, sysreg_write_vttbr,
			 {
				 __casm__mcrr_p15_6_r0_r1_c2();
				 __casm__bx_lr();
			 },
			 u64 value)

CASM_FUNCDEF(u32, sysreg_read_hsr,
			 {
				 __casm__mrc_p15_4_r0_c5_c2_0();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(u32, sysreg_read_elrhyp,
			 {
				 __casm__mrs_r0_elrhyp();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_elrhyp,
			 {
				 __casm__msr_elrhyp_r0();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(void, sysreg_tlbiallh,
			 {
				 __casm__mcr_p15_4_r0_c8_c7_0();
				 __casm__dsb_ish();
				 __casm__bx_lr();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_iciallu,
			 {
				 __casm__mcr_p15_0_r0_c7_c5_0();
				 __casm__bx_lr();
			 },
			 void *noparam)

//r0=ipa to flush s2pgtbl tlb entries for
//vmid is obtained from current vttbr
CASM_FUNCDEF(void, sysreg_tlbiipas2is,
			 {
				 __casm__mcr_p15_4_r0_c8_c0_1();
				 __casm__isb();
				 __casm__dsb_ish();
				 __casm__bx_lr();
			 },
			 u32 ipa)

CASM_FUNCDEF(void, sysreg_tlbiallis,
			 {
				 __casm__mcr_p15_0_r0_c8_c3_0();
				 __casm__isb();
				 __casm__dsb_ish();
				 __casm__bx_lr();
			 },
			 void *noparam)

CASM_FUNCDEF(u32, sysreg_read_mair0,
			 {
				 __casm__mrc_p15_0_r0_c10_c2_0();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_mair0,
			 {
				 __casm__mcr_p15_0_r0_c10_c2_0();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_mair1,
			 {
				 __casm__mrc_p15_0_r0_c10_c2_1();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_mair1,
			 {
				 __casm__mcr_p15_0_r0_c10_c2_1();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_hmair0,
			 {
				 __casm__mrc_p15_4_r0_c10_c2_0();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_hmair0,
			 {
				 __casm__mcr_p15_4_r0_c10_c2_0();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_hmair1,
			 {
				 __casm__mrc_p15_4_r0_c10_c2_1();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_hmair1,
			 {
				 __casm__mcr_p15_4_r0_c10_c2_1();
				 __casm__bx_lr();
			 },
			 u32 value)

//returns a 64-bit value:
//r0=lower 32-bits; r1=upper 32-bits (c.f. AAPCS)
CASM_FUNCDEF(u64, sysreg_read_httbr,
			 {
				 __casm__mrrc_p15_4_r0_r1_c2();
				 __casm__bx_lr();
				 __casm__retu64();
			 },
			 void *noparam)

//inputs: 64-bit value
//r0=lower 32-bits; r1=upper 32-bits (c.f. AAPCS)
CASM_FUNCDEF(void, sysreg_write_httbr,
			 {
				 __casm__mcrr_p15_4_r0_r1_c2();
				 __casm__bx_lr();
			 },
			 u64 value)

CASM_FUNCDEF(u32, sysreg_read_htcr,
			 {
				 __casm__mrc_p15_4_r0_c2_c0_2();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_htcr,
			 {
				 __casm__mcr_p15_4_r0_c2_c0_2();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_dacr,
			 {
				 __casm__mrc_p15_0_r0_c3_c0_0();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_dacr,
			 {
				 __casm__mcr_p15_0_r0_c3_c0_0();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_hdfar,
			 {
				 __casm__mrc_p15_4_r0_c6_c0_0();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(u32, sysreg_read_hpfar,
			 {
				 __casm__mrc_p15_4_r0_c6_c0_4();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

//r0 specifies the 32-bit lock variable address
CASM_FUNCDEF(void, spin_lock,
			 {
				 __casm__mov_imm_r1(0);			 //load r1 with 32-bit constant 0, signifies lock is occupied
CASM_LABEL(one);
				 __casm__ldrex_imm_r2_r0(0); //load current 32-bit value of lock and mark its memory region exclusive
				 __casm__teq_imm_r2(1);			 //check if it is 1 i.e, free
				 __casm__wfe_ne();				 //if not free, then put this core in the wait-for-event state
				 __casm__strex_eq_r3_r1_r0(0);	 //if free, try occupying the lock (storing 0); status is in r3
				 __casm__teq_eq_imm_r3(0);		 //if free, test the status of the store, 0=success, 1=fail
				 __casm__b_ne(one);				 //start all over again if failure to store

				 __casm__dmb_ish(); //data memory barrier inner shareability; make memory updates visible to all cores
				 __casm__bx_lr();
			 },
			 u32 *lock)

//r0 specifies the 32-bit lock variable address
CASM_FUNCDEF(void, spin_unlock,
			 {
				 __casm__dmb_ish();		//data memory barrier
				 __casm__mov_imm_r1(1); //load r1 with 32-bit constant 1, signifies lock is free
				 __casm__str_r1_r0(0);	//store 1 into lock indicating it is now free
				 __casm__dsb_ishst();	//allow other cores to see the value
				 __casm__sev();			//signal other cores to wake up (if they are in the spinloop)
				 __casm__bx_lr();
			 },
			 u32 *lock)
//////
// pl0,1 system register access functions
// chiefly used for emulation/pass-thru
//////
CASM_FUNCDEF(u32, sysreg_read_ttbcr,
			 {
				 __casm__mrc_p15_0_r0_c2_c0_2();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_ttbcr,
			 {
				 __casm__mcr_p15_0_r0_c2_c0_2();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_ttbr0,
			 {
				 __casm__mrc_p15_0_r0_c2_c0_0();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_ttbr0,
			 {
				 __casm__mcr_p15_0_r0_c2_c0_0();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_ttbr1,
			 {
				 __casm__mrc_p15_0_r0_c2_c0_1();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_ttbr1,
			 {
				 __casm__mcr_p15_0_r0_c2_c0_1();
				 __casm__bx_lr();
			 },
			 u32 value)
//r0 is the input virtual address
CASM_FUNCDEF(void, sysreg_ats12nsour,
			 {
				 __casm__mcr_p15_0_r0_c7_c8_6();
				 __casm__bx_lr();
			 },
			 u32 value)
//r0 is the input virtual address
CASM_FUNCDEF(void, sysreg_ats1cpr,
			 {
				 __casm__mcr_p15_0_r0_c7_c8_0();
				 __casm__bx_lr();
			 },
			 u32 value)

CASM_FUNCDEF(u32, sysreg_read_par,
			 {
				 __casm__mrc_p15_0_r0_c7_c4_0();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)
//////
// generic timer system registers
//////
CASM_FUNCDEF(u64, sysreg_read_cntpct,
			 {
				 __casm__mrrc_p15_0_r0_r1_c14();
				 __casm__bx_lr();
				 __casm__retu64();
			 },
			 void *noparam)

CASM_FUNCDEF(int, sysreg_read_cnthp_tval,
			 {
				 __casm__mrc_p15_4_r0_c14_c2_0();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_cnthp_tval,
			 {
				 __casm__mcr_p15_4_r0_c14_c2_0();
				 __casm__bx_lr();
			 },
			 int value)

CASM_FUNCDEF(u32, sysreg_read_cnthp_ctl,
			 {
				 __casm__mrc_p15_4_r0_c14_c2_1();
				 __casm__bx_lr();
				 __casm__retu32();
			 },
			 void *noparam)

CASM_FUNCDEF(void, sysreg_write_cnthp_ctl,
			 {
				 __casm__mcr_p15_4_r0_c14_c2_1();
				 __casm__bx_lr();
			 },
			 u32 value)
